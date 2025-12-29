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
import os
import multiprocessing as mp
from concurrent.futures import ProcessPoolExecutor, as_completed
import time
import multiprocessing as mp

# ============================================================
# KONFIG (im Code, keine CLI)
# ============================================================

# --- Grundpfade ---
THIS_DIR = Path(__file__).resolve().parent
TICKS_DIR = THIS_DIR / "ticks"                 # ParameterAnalysis\ticks\ticks_<EPIC>.csv
TRADINGBOT_DIR = THIS_DIR.parent / "TradingBot" # passt bei deiner Struktur

RESULTS_DIR = THIS_DIR / "results"
RESULTS_CSV_FILE = RESULTS_DIR / "results.csv"

PROFILE_OUT_FILE = THIS_DIR / "profile.txt"

# --- Run/Instrumente ---
INSTRUMENTS = ["ETHUSD"]  # später z.B. ["ETHUSD", "BTCUSD"]
FORCE_CLOSE_OPEN_POSITIONS_AT_END = True

# --- Laufzeit / Profiling ---
ENABLE_PROFILING = False   # für Laufzeit Tracking, bei Bedarf True

# --- Parallelisierung ---
ENABLE_PARALLEL = True
MAX_WORKERS = min(12, (os.cpu_count() or 2) - 2)  # z.B. 12 auf deinem System
MAX_INFLIGHT = 0   # 0 = automatisch (workers * 2)

# --- Output/Speed ---
SUPPRESS_BOT_OUTPUT = True
BACKTEST_CALL_ON_CANDLE_FORMING = False   # True = 1:1 Live-Verhalten, False = schnell

# --- Parameter-Spezifikation ---
# band=0 oder step=0 => keine Variation
PARAM_SPECS = {
    "EMA_FAST":                             (10, 1, 1),
    "EMA_SLOW":                             (18, 1, 1),
    "SIGNAL_MAX_PRICE_DISTANCE_SPREADS":    (4.0000, 1.0000, 1.0000),
    "SIGNAL_MOMENTUM_TOLERANCE":            (2.0000, 1.0000, 1.0000),
    "STOP_LOSS_PCT":                        (0.0030, 0.0010, 0.0010),
    "TRAILING_STOP_PCT":                    (0.0050, 0.0010, 0.0010),
    "TRAILING_SET_CALM_DOWN":               (0.5000, 0.0000, 0.0000),
    "TAKE_PROFIT_PCT":                      (0.0060, 0.0010, 0.0010),
    "BREAK_EVEN_STOP_PCT":                  (0.0045, 0.0010, 0.0010),
    "BREAK_EVEN_BUFFER_PCT":                (0.0002, 0.0000, 0.0000),
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

# ============================================================
# SNAPSHOT: letzte N Tick-Zeilen aus dem laufenden Bot übernehmen
# ============================================================
SNAPSHOT_ENABLED = True
SNAPSHOT_LAST_LINES = 10000  # << anpassen: wie viele letzte Zeilen übernehmen?

# ============================================================
# LOOP-BETRIEB (kontinuierlicher Batch)
# ============================================================
LOOP_ENABLED = True          # True = Dauerbetrieb, False = nur ein Durchlauf
LOOP_SLEEP_SECONDS = 10      # Wartezeit zwischen Läufen (Sekunden)

# ============================================================
# Import TradingBot aus Nachbarordner (ohne Kopie)
# ============================================================
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
# Worker-Cache + Worker-Funktionen
# ============================================================

_WORKER_TICKS_CACHE = None
_WORKER_INSTRUMENTS = None

def _worker_init(instruments, ticks_dir):
    global _WORKER_TICKS_CACHE, _WORKER_INSTRUMENTS
    _WORKER_INSTRUMENTS = list(instruments)
    # Jeder Worker lädt Tickdaten 1x und behält sie für alle Runs
    _WORKER_TICKS_CACHE = {epic: load_ticks_for_instrument(epic, ticks_dir) for epic in _WORKER_INSTRUMENTS}

def _worker_run(run_id, params):
    metrics = run_single_backtest(_WORKER_INSTRUMENTS, params, _WORKER_TICKS_CACHE)
    return run_id, metrics, params


def _tail_lines_bytes(path: Path, n_lines: int, chunk_size: int = 1024 * 1024) -> bytes:
    """
    Liest die letzten n_lines Zeilen (LF-getrennt) einer Datei effizient von hinten.
    Gibt Roh-Bytes zurück (UTF-8 kompatibel). Entfernt eine evtl. unvollständige letzte Zeile.
    """
    if n_lines <= 0:
        return b""

    with open(path, "rb") as f:
        f.seek(0, os.SEEK_END)
        file_size = f.tell()
        if file_size == 0:
            return b""

        data = b""
        pos = file_size

        # Von hinten chunkweise lesen, bis genug Zeilen vorhanden sind
        while pos > 0 and data.count(b"\n") <= n_lines:
            read_size = min(chunk_size, pos)
            pos -= read_size
            f.seek(pos)
            data = f.read(read_size) + data

        # Falls die Datei währenddessen geschrieben wurde: evtl. letzte Zeile unvollständig -> weg
        if data and not data.endswith(b"\n"):
            last_nl = data.rfind(b"\n")
            if last_nl != -1:
                data = data[: last_nl + 1]
            else:
                data = b""

        # Auf die letzten n_lines Zeilen schneiden
        lines = data.splitlines(keepends=True)
        if len(lines) <= n_lines:
            return b"".join(lines)
        return b"".join(lines[-n_lines:])


def _resolve_bot_tick_file(tradingbot_dir: Path, epic: str) -> Path:
    """
    Bot schreibt aktuell typischerweise in den Arbeitsordner: ticks_<EPIC>.csv
    Optional akzeptieren wir auch TradingBot/ticks/ticks_<EPIC>.csv, falls du das später so änderst.
    """
    candidates = [
        tradingbot_dir / f"ticks_{epic}.csv",
        tradingbot_dir / "ticks" / f"ticks_{epic}.csv",
    ]
    for c in candidates:
        if c.exists():
            return c
    raise FileNotFoundError(f"Keine Tickdatei für {epic} gefunden. Geprüft: {candidates}")


def snapshot_ticks_from_bot(instruments: List[str], tradingbot_dir: Path, dest_ticks_dir: Path, last_lines: int) -> None:
    dest_ticks_dir.mkdir(parents=True, exist_ok=True)

    for epic in instruments:
        src = _resolve_bot_tick_file(tradingbot_dir, epic)
        dst = dest_ticks_dir / f"ticks_{epic}.csv"

        payload = _tail_lines_bytes(src, last_lines)

        # Atomic-ish overwrite: erst temp, dann replace
        tmp = dst.with_suffix(".csv.tmp")
        with open(tmp, "wb") as f:
            f.write(payload)
        os.replace(tmp, dst)

        print(f"🧩 SNAPSHOT: {epic} ← {src.name} | letzte {last_lines} Zeilen → {dst}")



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


# ============================================================
# Liest results.csv (Semikolon-getrennt), ermittelt die Zeile mit maximaler 'equity'
# (bei mehreren Maxima: die erste/oberste) und schreibt daraus parameter.csv
# im Format KEY;VALUE (wie dein Anhang).

# Regeln:
# - Maßgeblich: Spalte 'equity' (max. Wert gewinnt; bei allen negativ = kleinster Verlust).
# - Wenn equity in allen Zeilen == 0 -> nichts ausgeben / nichts schreiben.
# - Wenn keine gültigen Datenzeilen -> nichts ausgeben / nichts schreiben.
# ============================================================

def export_best_params_from_results(results_csv: Path, out_parameter_csv: Path) -> None:

    if not results_csv.exists():
        print(f"⚠️ Keine Results-Datei gefunden: {results_csv}")
        return

    # Datei einlesen
    lines = results_csv.read_text(encoding="utf-8").splitlines()
    if len(lines) < 2:
        print(f"⚠️ Results-Datei enthält keine Datenzeilen: {results_csv}")
        return

    header = lines[0].split(";")
    if "equity" not in header:
        print(f"⚠️ Spalte 'equity' nicht gefunden in: {results_csv}")
        return

    equity_idx = header.index("equity")

    best_equity = None
    best_row = None

    any_nonzero_equity = False

    for line in lines[1:]:
        if not line.strip():
            continue

        cols = line.split(";")
        if len(cols) <= equity_idx:
            continue

        equity_str = cols[equity_idx].strip()
        if equity_str == "":
            continue

        # fmt_de schreibt Komma als Dezimaltrenner -> für Vergleich in float wandeln
        equity_val = float(equity_str.replace(",", "."))
        if equity_val != 0.0:
            any_nonzero_equity = True

        # Max suchen; bei Gleichstand gewinnt die erste Zeile => nur ">" verwenden
        if best_equity is None or equity_val > best_equity:
            best_equity = equity_val
            best_row = cols

    # Wenn keine gültige Zeile gefunden wurde
    if best_row is None or best_equity is None:
        print("⚠️ Kein gültiger Ergebnis-Datensatz gefunden (results.csv leer/invalid).")
        return

    # Wenn equity durchgängig 0 => nichts ausgeben/schreiben
    if not any_nonzero_equity:
        print("ℹ️ Keine Trades/kein Effekt: equity ist durchgängig 0 -> kein Export.")
        return

    # Parameter aus best_row ziehen: Spalten entsprechen PARAM_SPECS.keys()
    # (genau so wird results.csv bei dir geschrieben)
    params_out = []
    for k in PARAM_SPECS.keys():
        if k not in header:
            continue
        idx = header.index(k)
        if idx < len(best_row):
            params_out.append((k, best_row[idx].strip()))

    if not params_out:
        print("⚠️ Keine Parameter-Spalten gefunden -> kein Export.")
        return

    # parameter.csv schreiben (überschreiben)
    with open(out_parameter_csv, "w", encoding="utf-8", newline="") as f:
        for k, v in params_out:
            f.write(f"{k};{v}\n")

        # --- fest ergänzte Parameter (für Bot erforderlich) ---
        f.write("USE_HMA;True\n")
        f.write("TRADE_RISK_PCT;0.0025\n")
        f.write("MANUAL_TRADE_SIZE;0.3\n")

    # Log-Ausgabe
    equity_de = f"{best_equity:.2f}".replace(".", ",")
    print("\n===== BESTER PARAMETER-SATZ (aus results.csv) =====")
    print(f"Equity: {equity_de}")
    for k, v in params_out:
        print(f"{k} = {v}")
    print(f"✅ geschrieben: {out_parameter_csv}\n")


def main():    
    # --- Schritt 1: Tick-Snapshot aus laufendem Bot ziehen ---
    if SNAPSHOT_ENABLED:
        snapshot_ticks_from_bot(
            instruments=INSTRUMENTS,
            tradingbot_dir=TRADINGBOT_DIR,
            dest_ticks_dir=TICKS_DIR,
            last_lines=SNAPSHOT_LAST_LINES
        )

    keys, combos = build_param_grid(PARAM_SPECS)
    max_runs = len(combos)

    # CSV Header
    header_cols = [
        "run_time", "run", "total",
        "equity", "realized", "unrealized",
        "opens", "closes", "open_end"
    ] + list(PARAM_SPECS.keys())

    with open(RESULTS_CSV_FILE, "w", encoding="utf-8", newline="") as f_csv:
        f_csv.write(";".join(header_cols) + "\n")

        # -----------------------------
        # PARALLEL
        # -----------------------------
        if ENABLE_PARALLEL:
            import os
            import multiprocessing as mp
            from concurrent.futures import ProcessPoolExecutor, as_completed

            # Worker-Anzahl
            cpu = os.cpu_count() or 1
            workers = MAX_WORKERS if (MAX_WORKERS and MAX_WORKERS > 0) else max(1, cpu - 1)
            inflight_target = MAX_INFLIGHT if (MAX_INFLIGHT and MAX_INFLIGHT > 0) else workers * 2

            # Helper: formatiert Parameter kurz für Konsole
            def _param_str(params: Dict[str, Any]) -> str:
                parts = []
                for k in PARAM_SPECS.keys():
                    abbr = PARAM_ABBR.get(k, k)
                    parts.append(f"{abbr}={fmt_de(params[k])}")
                return " ".join(parts)

            # Wir halten Ergebnisse kurz zurück, um in Run-Reihenfolge zu schreiben
            pending: Dict[int, Tuple[int, Dict[str, Any], Dict[str, Any]]] = {}
            next_to_write = 1

            combo_iter = iter(enumerate(combos, 1))

            with ProcessPoolExecutor(
                max_workers=workers,
                initializer=_worker_init,
                initargs=(INSTRUMENTS, TICKS_DIR),
            ) as ex:
                futures = {}

                # Initial befüllen
                for _ in range(inflight_target):
                    try:
                        run_id, combo = next(combo_iter)
                    except StopIteration:
                        break
                    params = {k: v for k, v in zip(keys, combo)}
                    fut = ex.submit(_worker_run, run_id, params)
                    futures[fut] = run_id

                # Laufende Abarbeitung
                while futures:
                    # immer genau ein fertiges Future ziehen (und danach nachschieben)
                    for fut in as_completed(list(futures.keys())):
                        run_id = futures.pop(fut)
                        try:
                            rid, metrics, params = fut.result()
                        except Exception as e:
                            # Harte Fehler lieber sichtbar machen
                            raise RuntimeError(f"Worker-Fehler in Run {run_id}: {e}") from e

                        pending[rid] = (rid, metrics, params)

                        # Nächstes nachschieben
                        try:
                            next_run_id, next_combo = next(combo_iter)
                            next_params = {k: v for k, v in zip(keys, next_combo)}
                            nfut = ex.submit(_worker_run, next_run_id, next_params)
                            futures[nfut] = next_run_id
                        except StopIteration:
                            pass

                        # In Ordnung (1..N) wegschreiben/ausgeben, sobald verfügbar
                        while next_to_write in pending:
                            _, m, p = pending.pop(next_to_write)

                            run_time_str = datetime.now(bot.LOCAL_TZ).strftime("%d.%m.%Y %H:%M:%S %Z")
                            saldo_str = f"{m['equity']:.2f}".replace(".", ",")
                            print(f"{run_time_str} | Durchlauf {next_to_write}/{max_runs} | "
                                  f"Saldo={saldo_str} | Trades={m['closes']} | {_param_str(p)}")

                            csv_vals = [
                                run_time_str,
                                str(next_to_write),
                                str(max_runs),
                                fmt_de(m["equity"]),
                                fmt_de(m["realized"]),
                                fmt_de(m["unrealized"]),
                                str(m["opens"]),
                                str(m["closes"]),
                                str(m["open_positions_end"]),
                            ] + [fmt_de(p[k]) for k in PARAM_SPECS.keys()]
                            f_csv.write(";".join(csv_vals) + "\n")

                            next_to_write += 1

                        break  # wichtig: nur 1 completion pro while-Iteration

            # --- Nach dem vollständigen Durchlauf: besten Parametersatz exportieren ---
            f_csv.flush()
            try:
                os.fsync(f_csv.fileno())
            except Exception:
                pass

            export_best_params_from_results(
                results_csv=RESULTS_CSV_FILE,
                out_parameter_csv=THIS_DIR / "parameter.csv"
            )

            return  # parallel fertig

        # -----------------------------
        # SEQUENTIELL (dein bisheriger Loop)
        # -----------------------------
        ticks_cache = {epic: load_ticks_for_instrument(epic, TICKS_DIR) for epic in INSTRUMENTS}

        for i, combo in enumerate(combos, 1):
            params = {k: v for k, v in zip(keys, combo)}
            metrics = run_single_backtest(INSTRUMENTS, params, ticks_cache)

            parts = []
            for k in PARAM_SPECS.keys():
                abbr = PARAM_ABBR.get(k, k)
                parts.append(f"{abbr}={fmt_de(params[k])}")
            param_str = " ".join(parts)

            run_time_str = datetime.now(bot.LOCAL_TZ).strftime("%d.%m.%Y %H:%M:%S %Z")
            saldo_str = f"{metrics['equity']:.2f}".replace(".", ",")
            print(f"{run_time_str} | Durchlauf {i}/{max_runs} | Saldo={saldo_str} | Trades={metrics['closes']} | {param_str}")

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
            f_csv.write(";".join(csv_vals) + "\n")

    # --- Nach dem vollständigen Durchlauf: besten Parametersatz exportieren ---
    export_best_params_from_results(
        results_csv=RESULTS_CSV_FILE,
        out_parameter_csv=THIS_DIR / "parameter.csv"
    )

        
if __name__ == "__main__":
    
    mp.freeze_support()

    run_idx = 0

    try:
        while True:
            run_idx += 1
            print(f"\n===== PARAMETER_ANALYSIS RUN #{run_idx} | {datetime.now().strftime('%d.%m.%Y %H:%M:%S')} CET =====")

            if ENABLE_PROFILING:
                pr = cProfile.Profile()
                pr.enable()
                main()
                pr.disable()

                with open(PROFILE_OUT_FILE, "w", encoding="utf-8") as f:
                    stats = pstats.Stats(pr, stream=f).sort_stats("cumtime")
                    stats.print_stats(40)
                print(f"cProfile geschrieben: {PROFILE_OUT_FILE}")
            else:
                main()

            if not LOOP_ENABLED:
                break

            if LOOP_SLEEP_SECONDS > 0:
                print(f"--- Warte {LOOP_SLEEP_SECONDS} Sekunden bis zum nächsten Lauf ---")
                time.sleep(LOOP_SLEEP_SECONDS)

    except KeyboardInterrupt:
        print("\n[STOP] KeyboardInterrupt - Loop beendet.")

