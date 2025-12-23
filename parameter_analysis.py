import sys
import itertools
import contextlib
import io
from dataclasses import dataclass
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path
from datetime import datetime, timezone
from typing import Dict, List, Tuple, Any, Iterable, Optional
import heapq
import cProfile
import pstats


# ============================================================
# KONFIG (im Code, keine CLI)
# ============================================================

# Laufzeit Tracking an-/ausschalten
ENABLE_PROFILING = False   # für Laufzeit Tracking, bei Bedarf False
PROFILE_OUT_FILE = Path(__file__).resolve().parent / "profile.txt"

INSTRUMENTS = ["ETHUSD"]  # später z.B. ["ETHUSD", "BTCUSD"]

# Tick-Dateien liegen hier:
# ParameterAnalysis\ticks\ticks_ETHUSD.csv
TICKS_DIR = Path(__file__).resolve().parent / "ticks"

# Ergebnis-Datei
RESULTS_CSV_FILE = Path(__file__).resolve().parent / "results.csv"

FORCE_CLOSE_OPEN_POSITIONS_AT_END = True

# Parameter-Spezifikation:
# band=0 oder step=0 => keine Variation
PARAM_SPECS = {
    "EMA_FAST":                             (10, 0, 0),     # int (!) (start, band, step)  int
    "EMA_SLOW":                             (30, 0, 0),    # int (!)
    "SIGNAL_MAX_PRICE_DISTANCE_SPREADS":    (4.0000, 0.0000, 0.0000),  # float
    "SIGNAL_MOMENTUM_TOLERANCE":            (2.0000, 0.0000, 0.0000),          # float
    "STOP_LOSS_PCT":                        (0.0070, 0.0000, 0.0000),                   # fester Stop-Loss
    "TRAILING_STOP_PCT":                    (0.0075, 0.0000, 0.0000),        # Trailing Stop
    "TRAILING_SET_CALM_DOWN":               (0.5000, 0.0000, 0.0000),            # Filter für Trailing-Nachzie-Schwelle (spread*TRAILING_SET_CALM_DOWN)
    "TAKE_PROFIT_PCT":                      (0.0060, 0.0000, 0.0000),                 # z. B. 0,2% Gewinnziel
    "BREAK_EVEN_STOP_PCT":                  (0.0020, 0.0020, 0.0005),            # sicherung der Null-Schwelle / kein Verlust mehr möglich
    "BREAK_EVEN_BUFFER_PCT":                (0.0004, 0.0004, 0.0001),          # Puffer über BREAK_EVEN_STOP, ab dem der BE auf BREAK_EVEN_STOP gesetzt wird
}

PARAM_ABBR = {
    "EMA_FAST": "E_FAST",
    "EMA_SLOW": "E_SLOW",
    "SIGNAL_MAX_PRICE_DISTANCE_SPREADS": "SIG_MPDS",
    "SIGNAL_MOMENTUM_TOLERANCE": "SIG_MT",
    "STOP_LOSS_PCT": "SL_PCT",
    "TRAILING_STOP_PCT": "TS_PCT",
    "TRAILING_SET_CALM_DOWN": "TS_CD",
    "TAKE_PROFIT_PCT": "TP_PCT",
    "BREAK_EVEN_STOP_PCT": "BE_PCT",
    "BREAK_EVEN_BUFFER_PCT": "BE_BUF_PCT",
}

# Print-Flut: True => Bot-Prints werden unterdrückt (empfohlen)
SUPPRESS_BOT_OUTPUT = True

# Backtest-Speed: on_candle_forming ist sehr teuer (HMA/WMA) und für Entries i.d.R. nicht nötig
BACKTEST_CALL_ON_CANDLE_FORMING = False   # True = 1:1 Live-Verhalten, False = schnell

# ============================================================
# Import TradingBot aus Nachbarordner (ohne Kopie)
# ============================================================

THIS_DIR = Path(__file__).resolve().parent
TRADINGBOT_DIR = THIS_DIR.parent / "TradingBot"  # passt bei deiner Struktur

if not TRADINGBOT_DIR.exists():
    raise FileNotFoundError(f"TradingBot-Verzeichnis nicht gefunden: {TRADINGBOT_DIR}")

# Wichtig: Script-Dir soll zuerst kommen, damit unser Stub chart_gui.py greift.
if str(THIS_DIR) not in sys.path:
    sys.path.insert(0, str(THIS_DIR))
if str(TRADINGBOT_DIR) not in sys.path:
    sys.path.insert(1, str(TRADINGBOT_DIR))

import tradeingbot as bot  # nutzt die Bot-Logik 1:1


# ============================================================
# Helpers: Param-Grid
# ============================================================

def _decimals_from_step(step: float) -> int:
    s = f"{step:.20f}".rstrip("0")
    if "." in s:
        return len(s.split(".")[1])
    return 0
def fmt_de(x) -> str:
    # float -> deutsches Dezimal-Komma; int bleibt int
    if isinstance(x, float):
        return f"{x:.6f}".replace(".", ",")
    return str(x)

def float_range_centered(start: float, band: float, step: float) -> List[float]:
    # band=0 oder step=0 => nur start
    if band == 0 or step == 0:
        return [float(start)]

    d_start = Decimal(str(start))
    d_band  = Decimal(str(band))
    d_step  = Decimal(str(step))

    lo = d_start - d_band
    hi = d_start + d_band

    n = int(((hi - lo) / d_step).to_integral_value(rounding=ROUND_HALF_UP))
    vals = []
    for i in range(n + 1):
        v = lo + d_step * Decimal(i)
        if v < lo or v > hi:
            continue
        vals.append(v)

    # Rundung stabilisieren
    decs = _decimals_from_step(step)
    q = Decimal("1." + ("0" * decs)) if decs > 0 else Decimal("1")
    out = []
    for v in vals:
        out.append(float(v.quantize(q, rounding=ROUND_HALF_UP)))
    # Duplikate entfernen (Rundungsartefakte)
    out = sorted(set(out))
    return out

def int_range_centered(start: int, band: int, step: int) -> List[int]:
    if band == 0 or step == 0:
        return [int(start)]
    lo = start - band
    hi = start + band
    vals = list(range(lo, hi + 1, step))
    return vals


def build_param_grid(param_specs: Dict[str, Tuple[Any, Any, Any]]) -> Tuple[List[str], List[Tuple[Any, ...]]]:
    keys = list(param_specs.keys())
    value_lists = []
    for k in keys:
        start, band, step = param_specs[k]
        if isinstance(start, int) and isinstance(band, int) and isinstance(step, int):
            value_lists.append(int_range_centered(start, band, step))
        else:
            value_lists.append(float_range_centered(float(start), float(band), float(step)))
    combos = list(itertools.product(*value_lists))
    return keys, combos


# ============================================================
# Tick Loader (pro Instrument: ticks_<EPIC>.csv)
# Format: ts_ms;bid;ask
# ============================================================

def load_ticks_for_instrument(epic: str, ticks_dir: Path) -> List[Tuple[int, float, float, int]]:
    fn = ticks_dir / f"ticks_{epic}.csv"
    if not fn.exists():
        raise FileNotFoundError(f"Tick-Datei fehlt: {fn}")

    out = []
    with open(fn, "r", encoding="utf-8") as f:
        for line_no, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            parts = line.split(";")
            if len(parts) < 3:
                continue
            ts_ms = int(parts[0])
            dt_floor = bot.local_minute_floor(ts_ms)          # 1x teuer, aber nur beim Laden
            minute_key = int(dt_floor.timestamp() // 60)      # Integer-Minute
            bid = float(parts[1])
            ask = float(parts[2])
            out.append((ts_ms, bid, ask, minute_key))
    out.sort(key=lambda x: x[0])
    return out

def merge_tick_streams_cached(
    instruments: List[str],
    ticks_cache: Dict[str, List[Tuple[int, float, float, int]]]
) -> Iterable[Tuple[int, str, float, float, int]]:

    # Multi-Instrument: Listen per Timestamp mergen, ohne Datei-I/O
    heap = []
    idx = {epic: 0 for epic in instruments}

    for epic in instruments:
        ticks = ticks_cache.get(epic, [])
        if ticks:
            ts, bid, ask, mkey = ticks[0]
            heapq.heappush(heap, (ts, epic, bid, ask, mkey))

    while heap:
        ts, epic, bid, ask, mkey = heapq.heappop(heap)
        yield ts, epic, bid, ask, mkey

        idx[epic] += 1
        i = idx[epic]
        ticks = ticks_cache.get(epic, [])
        if i < len(ticks):
            ts2, bid2, ask2, mkey2 = ticks[i]
            heapq.heappush(heap, (ts2, epic, bid2, ask2, mkey2))


# ============================================================
# Broker-Stubs (keine API)
# ============================================================

@dataclass
class DummyResponse:
    status_code: int = 200
    text: str = "OK"


class BacktestBroker:
    def __init__(self):
        self.realized_pnl = 0.0
        self.opens = 0
        self.closes = 0
        self.last_price: Dict[str, Tuple[float, float, int]] = {}  # epic -> (bid, ask, ts)

    def set_last_price(self, epic: str, bid: float, ask: float, ts_ms: int):
        self.last_price[epic] = (bid, ask, ts_ms)

    def open_position(self, CST, XSEC, epic, direction, size, entry_price, retry=True):
        # 1:1-Struktur wie Bot erwartet (open_positions[epic] Dict)
        self.opens += 1
        deal_id = f"BT_{self.opens}"
        # entry_price wird vom Bot marktseitig korrekt übergeben
        bot.open_positions[epic] = {
            "direction": direction,
            "dealId": deal_id,
            "entry_price": float(entry_price),
            "size": float(size),
            "trailing_stop": None,
            "break_even_active": False,
        }
        return DummyResponse()

    def close_position(self, CST, XSEC, epic, deal_id=None, retry=True):
        pos = bot.open_positions.get(epic)
        if not isinstance(pos, dict):
            return DummyResponse()

        direction = pos.get("direction")
        entry = float(pos.get("entry_price") or 0.0)
        size = float(pos.get("size") or 0.0)

        bid, ask, _ = self.last_price.get(epic, (None, None, None))
        if bid is None or ask is None:
            # ohne Preis keine sinnvolle Realisierung
            bot.open_positions[epic] = None
            self.closes += 1
            return DummyResponse()

        # Marktseitig korrektes Schließen:
        # BUY  -> Exit auf Bid
        # SELL -> Exit auf Ask
        if direction == "BUY":
            exit_price = bid
            pnl = (exit_price - entry) * size
        else:
            exit_price = ask
            pnl = (entry - exit_price) * size

        self.realized_pnl += pnl
        self.closes += 1
        bot.open_positions[epic] = None
        return DummyResponse()

    def get_positions(self, CST, XSEC):
        return []


# ============================================================
# Backtest-Replay: Bot-Loop nachbauen (ohne WebSocket)
# ============================================================

def set_bot_params(params: Dict[str, Any]):
    # setzt Bot-Globals (keine neue Strategie-Logik)
    for k, v in params.items():
        setattr(bot, k, v)

def reset_bot_state(instruments: List[str], broker: BacktestBroker):
    bot.INSTRUMENTS = list(instruments)
    bot.open_positions = {epic: None for epic in instruments}
    bot.candle_history = {epic: bot.deque(maxlen=5000) for epic in instruments}
    bot.TICK_RING = {}
    bot._last_dirlog_sec = {}
    bot._last_close_ts = {}
    bot._last_ticklog_sec = {}

    broker.realized_pnl = 0.0
    broker.opens = 0
    broker.closes = 0
    broker.last_price = {}

def patch_bot_for_backtest(broker: BacktestBroker):
    # API-Funktionen auf Stub umbiegen
    bot.open_position = broker.open_position
    bot.close_position = broker.close_position
    bot.get_positions = broker.get_positions

    # Zeitfunktionen innerhalb des Bot-Moduls werden im Replay gesetzt (tick-basiert).
    # Hier nur Platzhalter; im Replay pro Tick aktualisieren wir "bot.time.time" / "bot.time.monotonic".
    pass

def ts_ms_to_local_str(ts_ms: int) -> str:
    dt = datetime.fromtimestamp(ts_ms / 1000.0, tz=timezone.utc).astimezone(bot.LOCAL_TZ)
    return dt.strftime("%d.%m.%Y %H:%M:%S")

def run_single_backtest(
    instruments: List[str],
    params: Dict[str, Any],
    ticks_cache: Dict[str, List[Tuple[int, float, float, int]]]
) -> Dict[str, Any]:

    broker = BacktestBroker()
    reset_bot_state(instruments, broker)
    patch_bot_for_backtest(broker)
    set_bot_params(params)

    # Candle-States wie im Bot-Loop
    states = {epic: {"minute": None, "bar": None} for epic in instruments}

    # deterministische „Zeit“ im Bot:
    # - time.time()   -> ts in Sekunden (UTC ist egal, es geht nur um Throttle)
    # - time.monotonic() -> wir verwenden ebenfalls ts in Sekunden, reicht für Cooldown/Delta
    def set_bot_time(ts_ms: int):
        t_sec = ts_ms / 1000.0
        bot.time.time = lambda: t_sec
        bot.time.monotonic = lambda: t_sec

    last_ts = None

    out_buf = io.StringIO()
    cm = contextlib.redirect_stdout(out_buf) if SUPPRESS_BOT_OUTPUT else contextlib.nullcontext()

    with cm:
        for ts_ms, epic, bid, ask, minute_key in merge_tick_streams_cached(instruments, ticks_cache):
            last_ts = ts_ms
            set_bot_time(ts_ms)
            broker.set_last_price(epic, bid, ask, ts_ms)

            # Update last_tick_ms wie im Live-Loop (für Logik/Throttle)
            pos = bot.open_positions.get(epic)
            if isinstance(pos, dict):
                pos["last_tick_ms"] = ts_ms

            st = states[epic]
            # minute_key = bot.local_minute_floor(ts_ms)

            if st["minute"] != minute_key and st["bar"] is not None:
                # Minute abgeschlossen
                bar_to_close = st["bar"]
                bot.on_candle_close(epic, bar_to_close)

                # neue Minute starten
                st["minute"] = minute_key
                st["bar"] = {
                    "open_bid": bid, "open_ask": ask,
                    "high_bid": bid, "low_bid": bid,
                    "high_ask": ask, "low_ask": ask,
                    "close_bid": bid, "close_ask": ask,
                    "ticks": 1,
                    "timestamp": ts_ms
                }
            else:
                # Neue Candle starten, falls noch keine existiert
                if st["minute"] is None:
                    st["minute"] = minute_key
                    st["bar"] = {
                        "open_bid": bid, "open_ask": ask,
                        "high_bid": bid, "low_bid": bid,
                        "high_ask": ask, "low_ask": ask,
                        "close_bid": bid, "close_ask": ask,
                        "ticks": 1,
                        "timestamp": ts_ms
                    }
                else:
                    # Laufende Candle aktualisieren
                    b = st["bar"]
                    b["high_bid"] = max(b["high_bid"], bid)
                    b["low_bid"] = min(b["low_bid"], bid)
                    b["close_bid"] = bid
                    b["high_ask"] = max(b["high_ask"], ask)
                    b["low_ask"] = min(b["low_ask"], ask)
                    b["close_ask"] = ask
                    b["ticks"] += 1
                    b["timestamp"] = ts_ms

                # während der Minute: forming ist optional (sehr teuer wegen HMA/WMA)
                if BACKTEST_CALL_ON_CANDLE_FORMING:
                    bot.on_candle_forming(epic, st["bar"], ts_ms)

                spread = ask - bid
                bot.check_protection_rules(epic, bid, ask, spread, CST=None, XSEC=None)


        # --- NEU: am Ende Positionen zwangs-schließen (fairer Vergleich) ---
        if FORCE_CLOSE_OPEN_POSITIONS_AT_END:
            for epic in instruments:
                if isinstance(bot.open_positions.get(epic), dict):
                    broker.close_position(CST=None, XSEC=None, epic=epic)

        # am Ende: Equity = realized + unrealized (falls Position offen)
        unrealized = 0.0
        open_count = 0
        for epic in instruments:
            pos = bot.open_positions.get(epic)
            if isinstance(pos, dict):
                open_count += 1
                direction = pos.get("direction")
                entry = float(pos.get("entry_price") or 0.0)
                size = float(pos.get("size") or 0.0)
                bid, ask, _ = broker.last_price.get(epic, (None, None, None))
                if bid is not None and ask is not None:
                    if direction == "BUY":
                        unrealized += (bid - entry) * size
                    else:
                        unrealized += (entry - ask) * size

    equity = broker.realized_pnl + unrealized

    return {
        "last_ts_ms": last_ts,
        "equity": equity,
        "realized": broker.realized_pnl,
        "unrealized": unrealized,
        "opens": broker.opens,
        "closes": broker.closes,
        "open_positions_end": open_count,
    }


def main():
    keys, combos = build_param_grid(PARAM_SPECS)
    max_runs = len(combos)

    # Tickdaten einmalig laden (Cache)
    ticks_cache = {epic: load_ticks_for_instrument(epic, TICKS_DIR) for epic in INSTRUMENTS}

    # CSV Header
    header_cols = [
        "run_time", "run", "total",
        "equity", "realized", "unrealized",
        "opens", "closes", "open_end"
    ] + list(PARAM_SPECS.keys())

    with open(RESULTS_CSV_FILE, "w", encoding="utf-8", newline="") as f:
        f.write(";".join(header_cols) + "\n")

    for i, combo in enumerate(combos, 1):
        params = {k: v for k, v in zip(keys, combo)}
        metrics = run_single_backtest(INSTRUMENTS, params, ticks_cache)
        
        # Parameter-String für Konsole (nur die Keys aus PARAM_SPECS, in fester Reihenfolge)
        parts = []
        for k in PARAM_SPECS.keys():
            abbr = PARAM_ABBR.get(k, k)
            parts.append(f"{abbr}={fmt_de(params[k])}")
        param_str = " ".join(parts)


        # Konsolen-Output (Ende Durchlauf)
        run_time_str = datetime.now(bot.LOCAL_TZ).strftime("%d.%m.%Y %H:%M:%S %Z")
        saldo_str = f"{metrics['equity']:.2f}".replace(".", ",")
        print(f"{run_time_str} | Durchlauf {i}/{max_runs} | Saldo={saldo_str} | Trades={metrics['closes']} | {param_str}")

        # CSV Zeile (deutsch formatiert)
        csv_vals = [
            run_time_str,
            str(i),
            str(max_runs),
            fmt_de(metrics["equity"]),
            fmt_de(metrics["realized"]),
            fmt_de(metrics["unrealized"]),
            str(metrics["opens"]),
            str(metrics["closes"]),
            str(metrics["open_positions_end"]),
        ] + [fmt_de(params[k]) for k in PARAM_SPECS.keys()]

        with open(RESULTS_CSV_FILE, "a", encoding="utf-8", newline="") as f:
            f.write(";".join(csv_vals) + "\n")

        
if __name__ == "__main__":
    if ENABLE_PROFILING:
        pr = cProfile.Profile()
        pr.enable()
        main()
        pr.disable()

        with open(PROFILE_OUT_FILE, "w", encoding="utf-8") as f:
            stats = pstats.Stats(pr, stream=f).sort_stats("cumtime")
            stats.print_stats(40)  # Top 40 nach kumulativer Zeit
        print(f"cProfile geschrieben: {PROFILE_OUT_FILE}")
    else:
        main()
