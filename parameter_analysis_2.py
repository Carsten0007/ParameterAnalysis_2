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
from concurrent.futures import ProcessPoolExecutor, wait, FIRST_COMPLETED
import time

# ============================================================
# KONFIG (im Code, keine CLI)
# ============================================================

# --- Grundpfade ---
THIS_DIR = Path(__file__).resolve().parent
TICKS_DIR = THIS_DIR / "ticks"                 # ParameterAnalysis\ticks\ticks_<EPIC>.csv
TRADINGBOT_DIR = THIS_DIR.parent / "TradingBot_2" # passt bei deiner Struktur
PARAMETER_CSV_PATH = TRADINGBOT_DIR / "parameter.csv" # temporär "_2"
RESULTS_DIR = THIS_DIR / "results"
RESULTS_CSV_FILE = RESULTS_DIR / "results.csv"
PROFILE_OUT_FILE = THIS_DIR / "profile_bot_2.txt"

# --- Run/Instrumente ---
INSTRUMENTS = ["ETHUSD"]  # später z.B. ["ETHUSD", "BTCUSD"]
FORCE_CLOSE_OPEN_POSITIONS_AT_END = True

# --- Laufzeit / Profiling ---
ENABLE_PROFILING = False   # für Laufzeit Tracking, bei Bedarf True

# --- Parallelisierung ---
ENABLE_PARALLEL = True
MAX_WORKERS = max(2, min(20, (os.cpu_count() or 2) - 2)) # MAX_WORKERS = min(12, (os.cpu_count() or 2) - 2)  # z.B. 12 auf deinem System
MAX_INFLIGHT = 0   # 0 = automatisch (workers * 2)

# --- Output/Speed ---
SUPPRESS_BOT_OUTPUT = True
BACKTEST_CALL_ON_CANDLE_FORMING = False   # True = 1:1 Live-Verhalten, False = schnell

# ============================================================
# SNAPSHOT: letzte N Tick-Zeilen aus dem laufenden Bot übernehmen
# ============================================================
SNAPSHOT_ENABLED = True # True = nimmt N Zeilen aus Bot Tick Datei, False = nimmt komplette Datei aus lokalem Verzeichnis
DEFAULT_SNAPSHOT_LAST_LINES = 200000 # << anpassen: wie viele letzte Zeilen übernehmen? | Default bei neustart
SNAPSHOT_LAST_LINES = 150000 # DEFAULT_SNAPSHOT_LAST_LINES # Arbeitsparameter, wird variabel auf Periode angepasst, niedriger Startwert = schneller Start
ESTIMATED_PERIOD_MINUTES = 600  # gewünschte Dauer des analysierten Zeitraums je Lauf, z.B. 150 Minuten (= 2.5h)

# ============================================================
# LOOP-BETRIEB (kontinuierlicher Batch)
# ============================================================
LOOP_ENABLED = True          # True = Dauerbetrieb, False = nur ein Durchlauf
LOOP_SLEEP_SECONDS = 1800      # Wartezeit zwischen Läufen (Sekunden)
MIN_CLOSED_TRADES_FOR_EXPORT = 3   # z.B. 10/20/30 – Start: 20
START_PARAMS_STR = {} # Initial Parametersatz des aktuellen laufs für Vergleich equity_neu besser equity_aktuell
USE_START_VALUES_FROM_PARAMETER_CSV = True   # True = Startwerte aus parameter.csv, False = Standardwerte aus PARAM_SPECS
# --- Quality Gate ---
PF_MIN = 1.10  # Profit Factor Mindestwert für Export (1.00=Break-even, 1.10=10% Puffer)


# ============================================================
# --- Parameter-Spezifikation ---
# band=0 oder step=0 => keine Variation
# initial, band, step, min, max
# ============================================================

# #   name,                                   initial , band, step, min, max              # ~ bewährt
# PARAM_SPECS = {
#     "EMA_FAST":                             (3, 0, 0, 3, 20),                          # (10, 1, 1, 2, 20),
#     "EMA_SLOW":                             (7, 0, 0, 5, 50),                          # (18, 1, 1, 4, 50),
#     "PULLBACK_NEAR_MA_MAX_DISTANCE_SPREADS":(1.5000, 0.0000, 0.0000, 0.0000, 50.00),       # umbenannt (4.0000, 1.0000, 1.0000, 0.0000, 50),
#     "PULLBACK_FAR_MA_MIN_DISTANCE_SPREADS": (1.7000, 0.0000, 0.0000, 0.0000, 50.00),        # umbenannt (2.0000, 1.0000, 1.0000, 0.0000, 5),
#     "CONFIRM_MIN_CLOSE_DELTA_SPREADS":      (0.2000, 0.2000, 0.1000, 0.0000, 10.00),     # umbenannt (2.0000, 0.5000, 0.5000, 0.0000, 10.0),
#     "REGIME_MIN_DIRECTIONALITY":            (0.0500, 0.2000, 0.1000, 0.0000, 1.000),     # neu
#     "STOP_LOSS_PCT":                        (0.0030, 0.0020, 0.0010, 0.0000, 0.010),     # (0.0030, 0.0010, 0.0010, 0.0000, 0.01),
#     "TRAILING_STOP_PCT":                    (0.0050, 0.0020, 0.0010, 0.0000, 0.010),     # (0.0050, 0.0010, 0.0010, 0.0000, 0.01),
#     "TRAILING_SET_CALM_DOWN":               (0.1000, 0.0000, 0.0000, 0.1000, 1.000),        # (0.5000, 0.2500, 0.2500, 0.0000, 1),
#     "TAKE_PROFIT_PCT":                      (0.0100, 0.0200, 0.0100, 0.0010, 0.100),      # (0.0060, 0.0010, 0.0010, 0.0010, 0.1),
#     "BREAK_EVEN_STOP_PCT":                  (0.0005, 0.0020, 0.0010, 0.0000, 0.100),     # (0.0045, 0.0010, 0.0010, 0.0010, 0.01),
#     "BREAK_EVEN_BUFFER_PCT":                (0.0005, 0.0000, 0.0000, 0.0005, 0.001),    # (0.0002, 0.0000, 0.0000, 0.0000, 0.001),
#     }
# comment 16.01.2026 00:11


# Autopilot: Entry-Parameter variieren, Exit-Parameter fix lassen
PARAM_SPECS = {
    # --- Indikator (fix lassen, solange Entry stabilisiert wird)
    "EMA_FAST":                              (3, 0, 0, 3, 20),
    "EMA_SLOW":                              (7, 0, 0, 5, 50),

    # --- Entry / Struktur (variieren)
    # ETHUSD-freundliche, sinnvolle Bereiche (Spread-skalierte Distanzen!)
    "PULLBACK_NEAR_MA_MAX_DISTANCE_SPREADS": (1.5000, 0.5000, 0.2500, 0.2000, 3.0000),
    "PULLBACK_FAR_MA_MIN_DISTANCE_SPREADS":  (1.6000, 0.3000, 0.2000, 0.3000, 2.0000),
    "CONFIRM_MIN_CLOSE_DELTA_SPREADS":       (0.2000, 0.2000, 0.1000, 0.0000, 2.0000),
    "REGIME_MIN_DIRECTIONALITY":             (0.0500, 0.1000, 0.0500, 0.0000, 0.6000),

    # --- Exit / Money-Management (fix lassen)
    "STOP_LOSS_PCT":                         (0.0020, 0.0000, 0.0000, 0.0000, 0.010),
    "TRAILING_STOP_PCT":                     (0.0050, 0.0005, 0.0005, 0.0000, 0.010),
    "TRAILING_SET_CALM_DOWN":                (0.1000, 0.0000, 0.0000, 0.1000, 1.000),
    "TAKE_PROFIT_PCT":                       (0.0100, 0.0005, 0.0005, 0.0010, 0.100),
    "BREAK_EVEN_STOP_PCT":                   (0.0005, 0.0002, 0.0002, 0.0000, 0.100),
    "BREAK_EVEN_BUFFER_PCT":                 (0.0005, 0.0000, 0.0000, 0.0005, 0.001),
}




PARAM_ABBR = {
    "EMA_FAST": "E_FAST",
    "EMA_SLOW": "E_SLOW",
    "PULLBACK_NEAR_MA_MAX_DISTANCE_SPREADS": "PB_NMD",
    "PULLBACK_FAR_MA_MIN_DISTANCE_SPREADS": "PB_FDS",
    "CONFIRM_MIN_CLOSE_DELTA_SPREADS": "CDS",
    "REGIME_MIN_DIRECTIONALITY": "RMD",
    "STOP_LOSS_PCT": "SL",
    "TRAILING_STOP_PCT": "TS",
    "TRAILING_SET_CALM_DOWN": "TS_CD",
    "TAKE_PROFIT_PCT": "TP",
    "BREAK_EVEN_STOP_PCT": "BE",
    "BREAK_EVEN_BUFFER_PCT": "BE_BUF",
}

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

import tradingbot_2 as bot  # nutzt die Bot-Logik 1:1


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


def build_param_grid(param_specs: Dict[str, Tuple[Any, ...]]) -> Tuple[List[str], List[Tuple[Any, ...]]]:
    # Unterstützt:
    #   - 3-Tupel: (start, band, step)
    #   - 5-Tupel: (start, band, step, min, max)

    # Strategie 1 (Filter-only):
    #   Werte werden erzeugt wie bisher um start±band und dann
    #   außerhalb [min,max] verworfen (kein Clamping, keine Fenster-Verschiebung).

    keys = list(param_specs.keys())
    value_lists: List[List[Any]] = []

    for k in keys:
        spec = param_specs[k]

        if len(spec) == 3:
            start, band, step = spec
            vmin, vmax = None, None
        elif len(spec) == 5:
            start, band, step, vmin, vmax = spec
        else:
            raise ValueError(f"PARAM_SPECS[{k}] muss 3- oder 5-Tupel sein, ist aber: {spec}")

        # Bereich erzeugen (wie bisher)
        if isinstance(start, int) and isinstance(band, int) and isinstance(step, int):
            vals = int_range_centered(int(start), int(band), int(step))
        else:
            vals = float_range_centered(float(start), float(band), float(step))

        # Filter-only: min/max anwenden, falls vorhanden
        if vmin is not None and vmax is not None:
            # für ints/floats gleicher Vergleich (Python kann int/float vergleichen)
            vals = [v for v in vals if vmin <= v <= vmax]

        if not vals:
            raise ValueError(f"PARAM_SPECS[{k}] erzeugt 0 Werte nach Filter (spec={spec}).")

        value_lists.append(vals)

    combos = list(itertools.product(*value_lists))

    # --- Kombinationssperre (EMA/Pullback) ---
    def _combo_ok(keys, combo):
        d = dict(zip(keys, combo))

        # 1) EMA: Fast muss wirklich schneller sein als Slow
        if "EMA_FAST" in d and "EMA_SLOW" in d:
            ef = int(d["EMA_FAST"])
            es = int(d["EMA_SLOW"])
            if ef >= es:
                return False
            # Mindestabstand entfernt (nur fast < slow)

        # haut in ruhigen phasen nicht hin 13.01.2026
        # # 3) Pullback: FAR muss strikt größer als NEAR sein (sonst ist das Armed→Return-Gate unlogisch)
        # if ("PULLBACK_NEAR_MA_MAX_DISTANCE_SPREADS" in d and
        #     "PULLBACK_FAR_MA_MIN_DISTANCE_SPREADS" in d):
        #     near_max = float(d["PULLBACK_NEAR_MA_MAX_DISTANCE_SPREADS"])
        #     far_min  = float(d["PULLBACK_FAR_MA_MIN_DISTANCE_SPREADS"])
        #     if far_min <= near_max:
        #         return False

        return True

    before = len(combos)
    combos = [c for c in combos if _combo_ok(keys, c)]
    removed = before - len(combos)
    if removed > 0:
        print(f"🧠 Kombinationssperre aktiv: {removed} Kombinationen verworfen (von {before} → {len(combos)})")

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


def snapshot_ticks_from_bot(instruments: List[str], tradingbot_dir: Path, dest_ticks_dir: Path, last_lines: int) -> Tuple[Optional[int], Optional[int], str]:
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

        # --- nice-to-have: Gesamtzeitraum des Snapshots loggen (aus den geschriebenen Dateien) ---
        print(f"🧩 SNAPSHOT: {epic} ← {src.name} | letzte {last_lines} Zeilen → {dst}")

    # --- Gesamtzeitraum des Snapshots loggen (einmal nach vollständigem Schreiben) ---
    t0_ms, t1_ms, dur_hms = get_snapshot_time_range(instruments, dest_ticks_dir)
    print(f"🧩 SNAPSHOT: Zeitraum gesamt ({dur_hms})")

    return t0_ms, t1_ms, dur_hms


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
        # ------------------------------------------------------------
        # Quality-Metriken (Trade-basiert) für Profit Factor / AvgWin/AvgLoss
        # Diese Werte werden NUR im Backtest genutzt (bot_2), nicht im Live-Bot.
        # ------------------------------------------------------------
        self.sum_wins = 0.0          # Summe aller realisierten Gewinn-Trades (>= 0)
        self.sum_losses_abs = 0.0    # Betrag der Summe aller realisierten Verlust-Trades (>= 0)
        self.win_trades = 0          # Anzahl Gewinn-Trades
        self.loss_trades = 0         # Anzahl Verlust-Trades


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
        
                # ------------------------------------------------------------
        # Quality-Metriken: Gewinn-/Verlust-Summen für Profit Factor
        # ------------------------------------------------------------
        if pnl > 0:
            self.sum_wins += pnl
            self.win_trades += 1
        elif pnl < 0:
            self.sum_losses_abs += abs(pnl)
            self.loss_trades += 1
        # pnl == 0 -> neutral, ignorieren wir für PF

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

    # Backtest: Parameter-Reload aus parameter.csv deaktivieren,
    # sonst überschreibt der Bot pro Candle-Close die Grid-Parameter.
    if hasattr(bot, "load_parameters"):
        bot.load_parameters = lambda *args, **kwargs: None

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

    # ✅ Quick Win C: deterministische „Zeit“ im Bot ohne per-Tick Lambda-Erzeugung
    # Wir hooken time.time/monotonic einmalig und setzen pro Tick nur noch bot._BT_NOW_SEC.
    if not hasattr(bot, "_BT_NOW_SEC"):
        bot._BT_NOW_SEC = 0.0

        def _bt_time():
            return bot._BT_NOW_SEC

        bot.time.time = _bt_time
        bot.time.monotonic = _bt_time

    def set_bot_time(ts_ms: int):
        bot._BT_NOW_SEC = ts_ms / 1000.0


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

    # ------------------------------------------------------------
    # Profit Factor (PF) = SumWins / SumLossAbs
    # - Wenn es keine Verlust-Trades gab (SumLossAbs == 0), setzen wir PF auf eine große Zahl.
    # - Damit "perfekte" Sets nicht crashen (Division by Zero), aber später sauber gegated werden können.
    # ------------------------------------------------------------
    if broker.sum_losses_abs > 0:
        profit_factor = broker.sum_wins / broker.sum_losses_abs
    else:
        profit_factor = 999999.0 if broker.sum_wins > 0 else 0.0

    return {
        "last_ts_ms": last_ts,
        "equity": equity,
        "realized": broker.realized_pnl,
        "unrealized": unrealized,
        "opens": broker.opens,
        "closes": broker.closes,
        "open_positions_end": open_count,
        # Quality-Metriken (Trade-basiert)
        "sum_wins": broker.sum_wins,
        "sum_losses_abs": broker.sum_losses_abs,
        "win_trades": broker.win_trades,
        "loss_trades": broker.loss_trades,
        "profit_factor": profit_factor,
    }

# ============================================================
# Liest pro Instrument aus der Snapshot-Tickdatei (ticks_<EPIC>.csv) die erste und letzte Zeile,
# extrahiert ts_ms und gibt (min_ts_ms, max_ts_ms, duration_hhmmss) zurück.
# Format Tickzeile: ts_ms;bid;ask
# ============================================================
def get_snapshot_time_range(instruments: List[str], ticks_dir: Path) -> Tuple[Optional[int], Optional[int], str]:
    
    min_ts = None
    max_ts = None

    for epic in instruments:
        p = ticks_dir / f"ticks_{epic}.csv"
        if not p.exists():
            continue

        try:
            with open(p, "r", encoding="utf-8", errors="ignore") as f:
                first_line = f.readline().strip()

                # letzte nicht-leere Zeile holen (ohne die ganze Datei zu laden)
                f.seek(0, os.SEEK_END)
                pos = f.tell()
                last_line = ""
                chunk = 4096
                while pos > 0 and not last_line:
                    read_size = min(chunk, pos)
                    pos -= read_size
                    f.seek(pos)
                    data = f.read(read_size)
                    lines = data.splitlines()
                    # letzte nicht-leere Zeile
                    for ln in reversed(lines):
                        if ln.strip():
                            last_line = ln.strip()
                            break

            if ";" not in first_line or ";" not in last_line:
                continue

            ts0 = int(first_line.split(";", 1)[0].strip())
            ts1 = int(last_line.split(";", 1)[0].strip())

            lo, hi = (ts0, ts1) if ts0 <= ts1 else (ts1, ts0)

            min_ts = lo if (min_ts is None or lo < min_ts) else min_ts
            max_ts = hi if (max_ts is None or hi > max_ts) else max_ts

        except Exception:
            continue

    if min_ts is None or max_ts is None:
        return None, None, "00:00:00"

    dur_s = max(0, (max_ts - min_ts) // 1000)
    hh = dur_s // 3600
    mm = (dur_s % 3600) // 60
    ss = dur_s % 60
    return min_ts, max_ts, f"{hh:02d}:{mm:02d}:{ss:02d}"



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

    # --- analysierter Zeitraum (aus Snapshot-Ticks) ---
    t0_ms, t1_ms, dur_hms = get_snapshot_time_range(INSTRUMENTS, TICKS_DIR)

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

    # --- Profit Factor Gate (wenn Spalte vorhanden) ---
    pf_idx = header.index("profit_factor") if "profit_factor" in header else None


    closes_idx = header.index("closes") if "closes" in header else None
    best_closes = -1

    best_equity = None
    best_row = None

    any_nonzero_equity = False

    # Start-Equity aus results.csv bestimmen (Zeile finden, deren Parameter dem Startsatz entsprechen)
    start_equity = None
    if START_PARAMS_STR:

        printed_start_mismatch = False
        
        for line in lines[1:]:
            if not line.strip():
                continue
            cols = line.split(";")
            ok = True
            for k, s_val in START_PARAMS_STR.items():
                if k not in header:
                    ok = False
                    break
                idx = header.index(k)
                if idx >= len(cols) or cols[idx].strip() != s_val:
                    ok = False  # wichtig: bevor der Param-Loop verlassen wird

                    # DEBUG: nur 1x ausgeben, sonst Spam
                    if not printed_start_mismatch:
                        printed_start_mismatch = True

                        csv_val = cols[idx].strip() if idx < len(cols) else "<IDX_OOB>"
                        try:
                            f_csv = float(csv_val.replace(",", "."))
                        except Exception:
                            f_csv = None
                        try:
                            f_start = float(s_val.replace(",", "."))
                        except Exception:
                            f_start = None

                        print("⚠️ STARTSATZ-MISMATCH (erste Abweichung)")
                        print(f"  Param: {k}")
                        print(f"  START (s_val): '{s_val}'")
                        print(f"  CSV   (val)  : '{csv_val}'")
                        print(f"  START float  : {f_start}")
                        print(f"  CSV   float  : {f_csv}")
                        if f_start is not None and f_csv is not None:
                            print(f"  diff         : {f_csv - f_start}")

                    break  # Param-Loop verlassen -> nächste results.csv-Zeile wird geprüft

            if ok:
                eq_str = cols[equity_idx].strip()
                if eq_str != "":
                    start_equity = float(eq_str.replace(",", "."))
                break
    
    if START_PARAMS_STR and start_equity is None:
        print("⚠️ Startsatz in results.csv nicht gefunden -> Improvement-Gate deaktiviert (nur für diesen Lauf).")

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

        # B) Mindestanzahl closes vorab filtern (damit gleiche equities nicht am Ende scheitern)
        closes_i = 0
        if closes_idx is not None and closes_idx < len(cols):
            v = cols[closes_idx].strip()
            closes_i = int(v) if v.isdigit() else 0

        if closes_i < MIN_CLOSED_TRADES_FOR_EXPORT:
            continue

        # --- PF_MIN Gate: nur Kandidaten mit ausreichender Trade-Qualität zulassen ---
        if pf_idx is not None and pf_idx < len(cols):
            pf_str = cols[pf_idx].strip()
            if pf_str != "":
                pf_val = float(pf_str.replace(",", "."))
                if pf_val < PF_MIN:
                    continue
            else:
                # leere PF-Spalte -> Kandidat verwerfen (stabiler als "durchwinken")
                continue
        else:
            # profit_factor Spalte fehlt -> Gate kann nicht angewendet werden
            # (hier bewusst NICHT continue, damit Abwärtskompatibilität erhalten bleibt)
            pass

        # B) Improvement-Gate: nur Kandidaten besser als Startsatz zulassen
        if start_equity is not None and equity_val <= start_equity:
            continue
        
        # Max suchen; bei Gleichstand gewinnt die Zeile mit mehr closes
        if (best_equity is None
            or equity_val > best_equity
            or (equity_val == best_equity and closes_i > best_closes)):
            best_equity = equity_val
            best_row = cols
            best_closes = closes_i

    # Wenn PF-Gate aktiv ist und nichts übrig blieb: sauber abbrechen
    if best_row is None and pf_idx is not None:
        pf_min_str = f"{PF_MIN:.3f}".replace(".", ",")
        print(f"ℹ️ Kein Parameter-Export: kein Kandidat erfüllt PF_MIN={pf_min_str} bei gleichzeitig MIN_CLOSED_TRADES_FOR_EXPORT={MIN_CLOSED_TRADES_FOR_EXPORT}.")
        return

    # B) Wenn Improvement-Gate aktiv war, aber keine Verbesserung gefunden wurde: kein Export
    if start_equity is not None and (best_row is None or best_equity is None):
        start_de = f"{start_equity:.6f}".replace(".", ",")

        # Startsatz kompakt ausgeben (weiterverwenden)
        # Startsatz zeilenweise ausgeben (weiterverwenden)
        def _param_lines(d: dict) -> str:
            # Reihenfolge wie PARAM_SPECS (damit es lesbar/konstant bleibt)
            lines = []
            for k in PARAM_SPECS.keys():
                if k in d:
                    v = d[k]
                    # Formatierung: ints ohne Nachkommastellen, floats mit 6 und DE-Komma
                    if isinstance(v, bool):
                        s = "True" if v else "False"
                    elif isinstance(v, int):
                        s = str(v)
                    else:
                        # alles andere als float behandeln (z.B. str) -> str()
                        try:
                            s = f"{float(v):.6f}".replace(".", ",")
                        except Exception:
                            s = str(v)

                    lines.append(f"{k} = {s}")
            return "\n".join(lines)

        print(f"ℹ️ Kein Parameter-Export: keine Verbesserung gegenüber Startsatz (start_equity={start_de}).")
        if START_PARAMS_STR:
            print("ℹ️ Verwende weiter Parameter:")
            print(_param_lines(START_PARAMS_STR))
        return

    # Wenn keine gültige Zeile gefunden wurde
    if best_row is None or best_equity is None:
        print("⚠️ Kein gültiger Ergebnis-Datensatz gefunden (results.csv leer/invalid).")
        return

    # Wenn equity durchgängig 0 => nichts ausgeben/schreiben
    if not any_nonzero_equity:
        print("ℹ️ Keine Trades/kein Effekt: equity ist durchgängig 0 -> kein Export.")
        return

    # Trades/Closes aus der best_row lesen (falls vorhanden)
    closes_val = ""
    if "closes" in header:
        ci = header.index("closes")
        if ci < len(best_row):
            closes_val = best_row[ci].strip()
    
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
            # Bot erwartet Dezimalpunkt
            v_bot = v.replace(",", ".")
            f.write(f"{k};{v_bot}\n")

        # --- fest ergänzte Parameter (für Bot erforderlich) ---
        f.write("USE_HMA;True\n")
        f.write("TRADE_RISK_PCT;0.0025\n")
        f.write("MANUAL_TRADE_SIZE;0.3\n")

    # --- Verlauf protokollieren (bestes Ergebnis je Lauf) ---
    history_file = RESULTS_DIR / "result_history.csv"
    ts_local = datetime.now(bot.LOCAL_TZ).strftime("%d.%m.%Y %H:%M:%S %Z")

    # History-Header bei Bedarf schreiben
    if not history_file.exists():
        hist_header = [
            "timestamp", "range_start", "range_end", "range_duration",
            "equity", "closes",
            "sum_wins", "sum_losses_abs", "profit_factor", "win_trades", "loss_trades"
        ] + list(PARAM_SPECS.keys())

        with open(history_file, "w", encoding="utf-8", newline="") as hf:
            hf.write(";".join(hist_header) + "\n")

    # Eine Zeile anhängen
    range_start = ""
    range_end = ""
    if t0_ms is not None and t1_ms is not None:
        range_start = datetime.fromtimestamp(t0_ms / 1000, tz=bot.LOCAL_TZ).strftime("%d.%m.%Y %H:%M:%S %Z")
        range_end   = datetime.fromtimestamp(t1_ms / 1000, tz=bot.LOCAL_TZ).strftime("%d.%m.%Y %H:%M:%S %Z")

    def _best_row_val(col_name: str) -> str:
        if col_name in header:
            j = header.index(col_name)
            if j < len(best_row):
                return best_row[j].strip()
        return ""

    hist_vals = [
        ts_local,
        range_start,
        range_end,
        dur_hms,
        f"{best_equity:.6f}".replace(".", ","),
        closes_val,
        _best_row_val("sum_wins"),
        _best_row_val("sum_losses_abs"),
        _best_row_val("profit_factor"),
        _best_row_val("win_trades"),
        _best_row_val("loss_trades"),
    ] + [dict(params_out).get(k, "") for k in PARAM_SPECS.keys()]

    with open(history_file, "a", encoding="utf-8", newline="") as hf:
        hf.write(";".join(hist_vals) + "\n")


    # Log-Ausgabe
    equity_de = f"{best_equity:.2f}".replace(".", ",")
    print("\n===== BESTER PARAMETER-SATZ (aus results.csv) =====")
    print(f"Equity: {equity_de}")

    if t0_ms is not None and t1_ms is not None:
        t0_str = datetime.fromtimestamp(t0_ms / 1000, tz=bot.LOCAL_TZ).strftime("%d.%m.%Y %H:%M:%S %Z")
        t1_str = datetime.fromtimestamp(t1_ms / 1000, tz=bot.LOCAL_TZ).strftime("%d.%m.%Y %H:%M:%S %Z")
        print(f"Zeitraum: {t0_str} → {t1_str} (Dauer {dur_hms})")

    for k, v in params_out:
        print(f"{k} = {v}")
    print(f"✅ geschrieben: {out_parameter_csv}\n")


# ============================================================
# Liest KEY;VALUE aus parameter.csv.
# Gibt Strings zurück; Casting passiert beim Anwenden pro Parametertyp.
# ============================================================

def read_parameter_csv(path: Path) -> Dict[str, str]:
    
    out: Dict[str, str] = {}
    if not path.exists():
        return out

    try:
        with open(path, "r", encoding="utf-8-sig") as f:
            for raw in f:
                line = raw.strip()
                if not line or line.startswith("#"):
                    continue
                if ";" not in line:
                    continue
                k, v = [p.strip() for p in line.split(";", 1)]
                if k:
                    out[k] = v
    except Exception:
        return {}

    return out

# ============================================================
# Ersetzt in PARAM_SPECS nur den Startwert (1. Element) durch den Wert aus parameter.csv,
# falls vorhanden und parsebar. Band/Step/Min/Max bleiben unverändert.
# ============================================================

def apply_start_values_from_file(param_specs: Dict[str, Tuple[Any, ...]], param_file: Path) -> Dict[str, Tuple[Any, ...]]:
    
    start_map = read_parameter_csv(param_file)
    if not start_map:
        return param_specs

    new_specs: Dict[str, Tuple[Any, ...]] = {}

    for k, spec in param_specs.items():
        if k not in start_map:
            new_specs[k] = spec
            continue

        raw = start_map[k]

        # Typ am vorhandenen Spec-Startwert erkennen (EMA_* int, Rest float)
        try:
            if isinstance(spec[0], int):
                start_val = int(float(raw))   # toleriert "10" und "10.0"
            else:
                start_val = float(raw)        # Bot-Datei nutzt Dezimalpunkt
        except Exception:
            # wenn kaputt/nicht parsebar -> alten Startwert behalten
            new_specs[k] = spec
            continue

        if len(spec) == 5:
            _, band, step, vmin, vmax = spec
            new_specs[k] = (start_val, band, step, vmin, vmax)
        elif len(spec) == 3:
            _, band, step = spec
            new_specs[k] = (start_val, band, step)
        else:
            raise ValueError(f"PARAM_SPECS[{k}] muss 3- oder 5-Tupel sein, ist aber: {spec}")

    return new_specs



def main():
    global SNAPSHOT_LAST_LINES
    
    # --- Schritt 1: Tick-Snapshot aus laufendem Bot ziehen ---
    if SNAPSHOT_ENABLED:
        t0_ms, t1_ms, dur_hms = snapshot_ticks_from_bot(
            instruments=INSTRUMENTS,
            tradingbot_dir=TRADINGBOT_DIR,
            dest_ticks_dir=TICKS_DIR,
            last_lines=SNAPSHOT_LAST_LINES
        )

        # --- AUTO: SNAPSHOT_LAST_LINES an Zielzeitraum anpassen (max = DEFAULT/aktueller Startwert) ---
        if t0_ms is not None and t1_ms is not None and t1_ms > t0_ms:
            actual_sec = (t1_ms - t0_ms) / 1000.0
            target_sec = ESTIMATED_PERIOD_MINUTES * 60.0

            new_lines = int(round(SNAPSHOT_LAST_LINES * (target_sec / actual_sec)))

            # max_lines = DEFAULT_SNAPSHOT_LAST_LINES (bei dir: initialer Startwert)
            if new_lines > DEFAULT_SNAPSHOT_LAST_LINES:
                new_lines = DEFAULT_SNAPSHOT_LAST_LINES

            if new_lines != SNAPSHOT_LAST_LINES:
                print(f"🧩 SNAPSHOT-AUTO: target={ESTIMATED_PERIOD_MINUTES:.1f}min actual={actual_sec/60:.1f}min -> next_lines={new_lines}")

            # für nächsten Lauf übernehmen
            SNAPSHOT_LAST_LINES = new_lines
        else:
            print("⚠️ SNAPSHOT-AUTO: Zeitraum konnte nicht bestimmt werden -> last_lines unverändert.")


    if USE_START_VALUES_FROM_PARAMETER_CSV:
        effective_specs = apply_start_values_from_file(PARAM_SPECS, PARAMETER_CSV_PATH)
    else:
        effective_specs = PARAM_SPECS

    # Startwerte (Grid-Zentrum) als Strings wie in results.csv
    global START_PARAMS_STR
    START_PARAMS_STR = {k: fmt_de(effective_specs[k][0]) for k in PARAM_SPECS.keys()}

    keys, combos = build_param_grid(effective_specs)

    max_runs = len(combos)

    # CSV Header
    header_cols = [
        "run_time", "run", "total",
        "equity", "realized", "unrealized",
        "opens", "closes", "open_end",
        # Quality-Metriken (Trade-basiert)
        "sum_wins", "sum_losses_abs", "profit_factor", "win_trades", "loss_trades"
    ] + list(PARAM_SPECS.keys())

    with open(RESULTS_CSV_FILE, "w", encoding="utf-8", newline="") as f_csv:
        f_csv.write(";".join(header_cols) + "\n")

        # -----------------------------
        # PARALLEL
        # -----------------------------
        if ENABLE_PARALLEL:
            import os            
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

            # ✅ NEW BEST Tracking (nur für Log-Ausgabe; CSV bleibt vollständig)
            best_equity_seen = None
            best_closes_seen = None
            best_run_seen = None

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
                    # ✅ Quick Win D: effizient auf mindestens ein fertiges Future warten (kein list(...), kein as_completed-Neustart)
                    done, _ = wait(futures.keys(), return_when=FIRST_COMPLETED)

                    # Es können auch mehrere gleichzeitig fertig sein -> alle abarbeiten
                    for fut in done:
                        run_id = futures.pop(fut)
                        try:
                            rid, metrics, params = fut.result()
                        except Exception as e:
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
                        balance_str = f"{m['equity']:.2f}".replace(".", ",")

                        # ✅ Quick Win: Console-Output stark reduzieren
                        if next_to_write % 100 == 0 or next_to_write == 1 or next_to_write == max_runs:
                            print(f"{run_time_str} | Run {next_to_write}/{max_runs} | "
                                f"Balance={balance_str} | closes={m['closes']} | {_param_str(p)}")

                        # ✅ NEW BEST Tracking (Equity besser oder bei gleicher Equity mehr closes)
                        eq = round(float(m["equity"]), 2)
                        cl = int(m.get("closes", 0))

                        is_better = False
                        if best_equity_seen is None:
                            is_better = True
                        elif eq > best_equity_seen:
                            is_better = True
                        elif eq == best_equity_seen and (best_closes_seen is None or cl > best_closes_seen):
                            is_better = True

                        if is_better:
                            best_equity_seen = eq
                            best_closes_seen = cl
                            best_run_seen = next_to_write

                            best_de = f"{eq:.2f}".replace(".", ",")
                            print(
                                f"NEW BEST | Run {next_to_write}/{max_runs} | Equity={best_de} | closes={cl} "
                                f"| PF={metrics.get('profit_factor', 0.0):.3f} | {_param_str(p)}"
                            )

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
                            # Quality-Metriken (Trade-basiert)
                            fmt_de(m.get("sum_wins", 0.0)),
                            fmt_de(m.get("sum_losses_abs", 0.0)),
                            fmt_de(m.get("profit_factor", 0.0)),
                            str(m.get("win_trades", 0)),
                            str(m.get("loss_trades", 0)),
                        ] + [fmt_de(p[k]) for k in PARAM_SPECS.keys()]

                        f_csv.write(";".join(csv_vals) + "\n")

                        next_to_write += 1


            # --- Nach dem vollständigen Durchlauf: besten Parametersatz exportieren ---
            f_csv.flush()
            try:
                os.fsync(f_csv.fileno())
            except Exception:
                pass

            export_best_params_from_results(
                results_csv=RESULTS_CSV_FILE,
                out_parameter_csv=PARAMETER_CSV_PATH
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
            balance_str = f"{metrics['equity']:.2f}".replace(".", ",")
            print(f"{run_time_str} | Durchlauf {i}/{max_runs} | Balance={balance_str} | Trades={metrics['closes']} | {param_str}")

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
                # Quality-Metriken (Trade-basiert)
                fmt_de(metrics.get("sum_wins", 0.0)),
                fmt_de(metrics.get("sum_losses_abs", 0.0)),
                fmt_de(metrics.get("profit_factor", 0.0)),
                str(metrics.get("win_trades", 0)),
                str(metrics.get("loss_trades", 0)),
            ] + [fmt_de(params[k]) for k in PARAM_SPECS.keys()]

            f_csv.write(";".join(csv_vals) + "\n")

    # --- Nach dem vollständigen Durchlauf: besten Parametersatz exportieren ---
    export_best_params_from_results(
        results_csv=RESULTS_CSV_FILE,
        out_parameter_csv=PARAMETER_CSV_PATH
    )

        
if __name__ == "__main__":
    
    mp.freeze_support()

    run_idx = 0

    try:
        while True:
            run_idx += 1
            print(f"\n===== PARAMETER_ANALYSIS RUN #{run_idx} | {datetime.now().strftime('%d.%m.%Y %H:%M:%S')} CET =====")

            t_start = time.perf_counter()

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

            t_end = time.perf_counter()
            dur_s = t_end - t_start
            hh = int(dur_s // 3600)
            mm = int((dur_s % 3600) // 60)
            ss = int(dur_s % 60)
            print(f"⏱️ Batch-Rechenzeit: {hh:02d}:{mm:02d}:{ss:02d} ({dur_s:.2f}s)")

            if not LOOP_ENABLED:
                break

            if LOOP_SLEEP_SECONDS > 0:
                print(f"--- Warte {LOOP_SLEEP_SECONDS} Sekunden bis zum nächsten Lauf ---")
                time.sleep(LOOP_SLEEP_SECONDS)

    except KeyboardInterrupt:
        print("\n[STOP] KeyboardInterrupt - Loop beendet.")

