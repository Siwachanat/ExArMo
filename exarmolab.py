#!/usr/bin/env python3
"""
ExArMo Lab — Motor Tester GUI  (v2.0, light theme, paper-ready)
===============================================================
Companion to the DEDICATED lab firmware `src/main.cpp` v2.0 (NOT the ExArMo
rehab firmware). All quantities are MOTOR-SHAFT units from the device link.

WHAT CHANGED FROM v1 (and why nothing showed up before)
-------------------------------------------------------
[g2-A] `dev["last"]` was the ONLY channel for firmware messages, and
       `dev_send()` overwrote it with "> K" every single keepalive. So
       EV,FOCFAIL / EV,WATCHDOG / ACK lines were clobbered within a second of
       arriving and the footer banner could essentially never fire. TX and RX
       are now separate, faults are STICKY, and there is a real scrolling
       console on the Diagnostics tab.
[g2-B] The step engine assumed the arm reached the load cell after a fixed
       ~2 s "engage" wait. It never checked. If the arm was short of the cell
       (or pushing the wrong way) every step recorded 0 g with no complaint.
       Engagement now WAITS FOR CONTACT — a real rise in grams — and aborts
       with a clear message if contact never happens.
[g2-C] No way to verify push DIRECTION before a sweep. A direction toggle
       ('Ps±1') and a manual jog live on the Diagnostics tab now.
[g2-D] Telemetry gained id, voltage.q and a health/flags word, so the GUI can
       distinguish "no current commanded" from "current commanded but not
       measured" from "FOC never initialised".
[g2-E] Connect now resets the board (O0), sets the telemetry rate and asks for
       a status dump, instead of trusting whatever state the board was left in.
[g2-F] Keepalive raised to 2 Hz against the firmware's 3 s watchdog.

Tabs:
 0  Diagnostics       console, live flags, jog, direction, self-test
 1  KV · Back-EMF     spin at speed steps, type multimeter V, live KV fit
 2  KT · Add weight   freewheel → rotate arm horizontal → HOLD; add weights,
                      record averaged Iq per step; fit τ vs Iq → Kt
 3  KT · Loadcell     Iq steps; per step wait `settle` (discard) then average
                      the loadcell robustly; fit Kt              [2nd serial]
 4  Heat over force   constant Iq; log loadcell+temperature every 1 s with a
                      high-temperature auto-stop                 [2nd serial]
 5  Capstan torque    same engine as 3 through the capstan; output Kt and
                      optional efficiency vs the motor Kt from tab 3
 6  Thermal rise      [g3-A] hold one current, log the temperature curve, and
                      fit the motor's thermal model: tau, steady-state rise,
                      thermal resistance, and the continuous current that
                      corresponds to an allowed winding rise

[g3-A] TEMPERATURE NOW COMES FROM THE DRIVER BOARD.
    Lab firmware v2.7.1 reads a 100k NTC on GPIO3/PA2 and publishes it as an 11th
    telemetry field, sampled on the SAME clock as Iq. Until now temperature
    arrived on the load-cell Arduino's own serial port, on its own timebase,
    which is fine for "did it get hot" and useless for "how fast did it get
    hot" — two devices, two clocks, no common t=0. The load-cell stream is
    still read and is still the automatic fallback when the board has no bead
    fitted; temp_src() says which one is live, and the fallback is never
    silent, because a thermal number whose provenance you cannot state is not
    a measurement.

Device telemetry (11 fields):
    D,t_ms,state,angle,vel,iq_meas,iq_cmd,id_meas,vq,flags,temp_C
    flags bit5 = thermistor healthy. temp_C is 0 when that bit is CLEAR — an
    unread sensor must never be mistaken for a cold motor, so this program
    gates on the flag and never on the value.
Loadcell/temp Arduino protocol (2nd serial, 115200): one line per sample,
"grams" or "grams,tempC"  e.g.  "512.3,41.7"

Run:  pip install pyserial   →   python ExarmoLabGui.py
"""

import tkinter as tk
import tkinter.ttk as ttk
import tkinter.messagebox as messagebox
import threading, time, math, csv, os, re, json, collections
from datetime import datetime
import serial, serial.tools.list_ports

BAUD_DEV = 921600
BAUD_LC  = 115200
TELEM_MS = 20
KEEPALIVE_S = 0.5          # [g2-F] 2 Hz against the firmware's 3 s watchdog
G_ACC    = 9.80665

# ── light theme (paper-friendly) ───────────────────────────────
BG      = "#f2f4f8"
SURFACE = "#ffffff"
FIELD   = "#eef1f6"
BORDER  = "#d5dbe6"
TEXT    = "#1c2433"
MUTED   = "#5c6a80"
FAINT   = "#8b96a8"
BLUE    = "#2563eb"
GREEN   = "#118a52"
RED     = "#d3455b"
AMBER   = "#b45309"
PURPLE  = "#7c3aed"

F_TITLE = ("Segoe UI", 24, "bold")
F_H     = ("Segoe UI", 13, "bold")
F_LBL   = ("Segoe UI", 13)
F_SM    = ("Segoe UI", 11)
F_BTN   = ("Segoe UI", 13, "bold")
F_MONO  = ("Consolas", 16)
F_BIG   = ("Consolas", 40, "bold")

STATE_NAMES = {0: "IDLE (free)", 1: "VELOCITY", 2: "HOLDING", 3: "CURRENT"}

FLAG_BITS = [(0x01, "FOC init"), (0x02, "motor enabled"),
             (0x04, "FOC armed (driving)"), (0x08, "current sense"), (0x10, "Vbus"),
             (0x20, "thermistor (GPIO3)")]        # [g3-A]

running = True

# ── device link (lab firmware) ─────────────────────────────────
dev = dict(ser=None, lock=threading.Lock())
# [g2-A] three SEPARATE channels. v1 had one string that the keepalive echo
# overwrote twice a second, which is why firmware faults were never visible.
link = dict(tx="", rx="", fault="", fw="")
console = collections.deque(maxlen=500)
console_seq = [0]          # monotonic — len() saturates once the deque is full
console_lock = threading.Lock()

T = dict(state=0, ang=0.0, vel=0.0, iq=0.0, iqc=0.0, idq=0.0, vq=0.0,
         flags=-1, t_rx=0.0, nfields=0,
         temp=None, temp_ok=False)              # [g3-A] driver-board thermistor
# Producer/consumer discipline: the two reader THREADS append to these while
# the Tk thread and the experiment worker threads read them. A bounded deque
# evicts from the left on every append, so a concurrent read raises
# "deque mutated during iteration". That race has been here all along — it used
# to kill the tick chain outright and look like "the numbers just stopped".
# Never touch these directly; go through snap_hist() / snap_lc().
hist_lock = threading.Lock()
iq_hist  = collections.deque(maxlen=800)     # (t, iq_meas)
iqc_hist = collections.deque(maxlen=800)     # (t, iq_cmd from firmware)
rpm_hist = collections.deque(maxlen=800)     # (t, rpm)
ang_hist = collections.deque(maxlen=800)     # (t, shaft angle rad, accumulated)
# [g3-A] Temperature moves in minutes, not milliseconds, so this one is sized
# for a whole thermal run rather than for a 60 s plot window: 12000 samples at
# the 20 ms telemetry rate is only 4 minutes, but the experiment below decimates
# to its own log period and keeps its own rows — this deque is for the live
# chart and the short averages.
temp_hist = collections.deque(maxlen=12000)  # (t, degC) from the DRIVER board


def snap_hist(dq):
    with hist_lock:
        return list(dq)


def snap_lc():
    with lc_lock:
        return list(lc_buf)


def clog(text, kind="rx"):
    with console_lock:
        console.append((time.strftime("%H:%M:%S"), kind, text))
        console_seq[0] += 1


def dev_send(cmd):
    with dev["lock"]:
        s = dev["ser"]
        if s is None or not s.is_open:
            link["fault"] = "device not connected"
            return False
        try:
            s.write((cmd + "\n").encode())
            link["tx"] = cmd
            if cmd != "K":                       # don't spam the console
                clog(cmd, "tx")
            return True
        except Exception as e:
            link["fault"] = f"tx error: {e}"
            clog(f"tx error: {e}", "err")
            return False


def dev_reader():
    last_keep = 0.0
    while running:
        s = dev["ser"]
        if s is None or not s.is_open:
            time.sleep(0.2)
            continue
        if time.time() - last_keep > KEEPALIVE_S:        # watchdog food
            dev_send("K")
            last_keep = time.time()
        try:
            raw = s.readline()
        except Exception as e:
            link["fault"] = f"rx error: {e}"
            time.sleep(0.2)
            continue
        if not raw:
            continue
        line = raw.decode(errors="replace").strip()
        if not line:
            continue

        if line.startswith("D,"):
            p = line.split(",")
            T["nfields"] = len(p)
            if len(p) >= 13:
                # 13 fields = the ExArMo REHAB firmware is flashed, not the lab
                # firmware — every lab command would misbehave
                link["fault"] = "WRONG FIRMWARE: flash the labtest main.cpp"
                continue
            if len(p) >= 6:
                try:
                    # float("nan") and float("inf") both PARSE, and Arduino
                    # prints exactly those words. One such sample used to reach
                    # the plots, produce NaN canvas coordinates, raise TclError
                    # inside the periodic tick, and silently kill the whole
                    # live-update chain — every readout frozen, no error shown.
                    vals = [float(x) for x in p[3:7]] if len(p) >= 7 else [float(x) for x in p[3:6]] + [0.0]
                    if not all(math.isfinite(v) for v in vals):
                        clog("dropped a non-finite telemetry sample", "err")
                        continue
                    T["state"] = int(p[2])
                    T["ang"], T["vel"], T["iq"], T["iqc"] = vals
                    # v2 extras (absent on the old 7-field firmware)
                    _id = float(p[7]) if len(p) >= 8 else 0.0
                    _vq = float(p[8]) if len(p) >= 9 else 0.0
                    T["idq"] = _id if math.isfinite(_id) else 0.0
                    T["vq"] = _vq if math.isfinite(_vq) else 0.0
                    T["flags"] = int(float(p[9])) if len(p) >= 10 else -1
                    now = time.time()
                    T["t_rx"] = now
                    # [g3-A] field 11 = motor temperature, valid only while
                    # flags bit5 is set. The firmware publishes 0.0 with the
                    # bit CLEAR when the bead is open or shorted, and 0 degC is
                    # a number this program would otherwise plot, average and
                    # fit quite happily. Gate on the bit.
                    with hist_lock:
                        iq_hist.append((now, T["iq"]))
                        iqc_hist.append((now, T["iqc"]))
                        rpm_hist.append((now, T["vel"] * 60.0 / (2 * math.pi)))
                        ang_hist.append((now, T["ang"]))
                    T["temp_ok"] = bool(T["flags"] >= 0 and (T["flags"] & 0x20))
                    T["temp"] = None
                    if len(p) >= 11 and T["temp_ok"]:
                        try:
                            _tc = float(p[10])
                        except ValueError:
                            _tc = float("nan")
                        if math.isfinite(_tc):
                            T["temp"] = _tc
                            with hist_lock:
                                temp_hist.append((now, _tc))
                except ValueError:
                    pass
            continue

        # everything that is not telemetry is a message worth keeping
        link["rx"] = line
        clog(line, "err" if ("FAIL" in line or "WATCHDOG" in line) else "rx")
        if line.startswith("EV,BOOT,"):
            link["fw"] = line.split(",", 2)[-1]
            link["fault"] = ""
        elif "FOCFAIL" in line:
            link["fault"] = "initFOC FAILED — motor cannot move (check magnet / pole pairs / power)"
        elif "SENSEFAIL" in line:
            link["fault"] = "CURRENT SENSE DEAD — commanding current, measuring none"
        elif "WATCHDOG" in line:
            link["fault"] = "WATCHDOG tripped — host went silent, motor released"
        elif "RUNAWAY" in line:
            link["fault"] = ("RUNAWAY trip — the shaft was free and accelerated away. "
                             "Load it against the cell before jogging, or lower Pv.")
        # [g3-A] the comma matters: "EV,TEMP," is the trip, "EV,TEMPFAIL" is a
        # broken sensor and "EV,TEMPDUMP" is just the 'T' report.
        elif line.startswith("EV,TEMP,"):
            link["fault"] = ("OVER-TEMPERATURE — the firmware stopped the motor. "
                             "Let it cool; it refuses torque until it does.")
        elif line.startswith("EV,TEMPFAIL"):
            link["fault"] = ("THERMISTOR FAULT — open or shorted on GPIO3/PA2. "
                             "Send T on the Diagnostics console for the raw volts.")
        elif line.startswith("EV,TEMPOK"):
            link["fault"] = ""
        elif line.startswith("EV,SELFTEST,"):
            link["fault"] = ""
        elif line.startswith("EV,ALIGN,"):
            if ",1," not in line:
                link["fault"] = "RE-ALIGN FAILED — is the shaft free to turn?"
            elif "pp_ok=0" in line:
                link["fault"] = "POLE-PAIR CHECK FAILED — torque per amp will be wrong"
            else:
                link["fault"] = "" 


def dev_connect(port):
    dev_disconnect()
    try:
        s = serial.Serial(port, BAUD_DEV, timeout=0.2)
        time.sleep(0.4)
        s.reset_input_buffer()
        with dev["lock"]:
            dev["ser"] = s
        link["fault"] = ""
        clog(f"--- connected {port} @ {BAUD_DEV} ---", "sys")
        # [g2-E] never trust whatever state the board was left in
        dev_send("O0")
        dev_send(f"D{TELEM_MS}")
        dev_send("L")
        dev_status.config(text=f"● {port}", fg=GREEN)
    except Exception as e:
        dev_status.config(text=f"● {e}", fg=RED)
        clog(f"connect failed: {e}", "err")


def dev_disconnect():
    with dev["lock"]:
        if dev["ser"] is not None:
            try:
                dev["ser"].write(b"O0\n"); dev["ser"].close()
            except Exception:
                pass
            dev["ser"] = None


def dev_alive():
    return T["t_rx"] > 0 and (time.time() - T["t_rx"]) < 1.0


# ── loadcell / temperature link (Arduino) ──────────────────────
lc = dict(ser=None, lock=threading.Lock(), last="")
# [g2-G] The load cell is the TORQUE REFERENCE for every Kt number this program
# produces, and it is the one instrument in the chain nobody had verified. Note
# that weightscale/wdisplay.py divides its stream by a hard-coded 2.44 while
# this program did not — so the two tools disagreed about what a gram is. Until
# it is checked against known masses, "grams" here is an arbitrary unit.
# [g3-B] CALIBRATION MODEL: grams = (raw − tare) × scale
#
# `tare` is in RAW units, not grams, because that is where the offset
# physically is — a resting preload, the beam's own weight, the amplifier's
# zero. Putting it before the multiply means one representation serves all
# three calibration modes: a multi-point fit gives grams = a·raw + b, which is
# this same line with scale = a and tare = −b/a.
#
# There was no offset term at all before, only a multiplier, so any resting
# load rode along in every reading. The old "Zero" button captured a reference
# for the span calculation and then threw it away.
lc_cal = {"scale": 1.0, "tare": 0.0, "mode": "manual",
          "points": [], "r2": None, "when": ""}
LC_CAL_FILE = os.path.join("labdata", "loadcell_cal.json")
lc_lock = threading.Lock()
lc_buf = collections.deque(maxlen=8000)      # (t, grams, tempC or None)
lc_raw_buf = collections.deque(maxlen=8000)  # (t, RAW counts) — calibration
                                             # must see the uncalibrated stream

_num = re.compile(r"[-+]?\d+(?:\.\d+)?")
_letters = re.compile(r"[A-Za-z]")        # [g3-C] see lc_reader


def lc_cal_load():
    """Restore the calibration saved by the last session.

    Without this the scale reset to 1.0 on every launch and nothing recorded
    what it had been, so two runs in the labdata folder could be in different
    units with no way to tell them apart afterwards."""
    try:
        with open(LC_CAL_FILE) as f:
            d = json.load(f)
        for k in ("scale", "tare", "r2"):
            if d.get(k) is not None:
                lc_cal[k] = float(d[k])
        lc_cal["mode"] = d.get("mode", "manual")
        lc_cal["points"] = [(float(a), float(b)) for a, b in d.get("points", [])]
        lc_cal["when"] = d.get("when", "")
        return True
    except Exception:
        return False


def lc_cal_save():
    try:
        os.makedirs("labdata", exist_ok=True)
        with open(LC_CAL_FILE, "w") as f:
            json.dump({"scale": lc_cal["scale"], "tare": lc_cal["tare"],
                       "mode": lc_cal["mode"], "points": lc_cal["points"],
                       "r2": lc_cal["r2"], "when": lc_cal["when"]}, f, indent=2)
        return True
    except Exception:
        return False


def lc_cal_line():
    """One comment line stamped at the top of every log file."""
    r2 = "" if lc_cal["r2"] is None else f"{lc_cal['r2']:.5f}"
    return (f"# loadcell scale={lc_cal['scale']:.6g} tare_raw={lc_cal['tare']:.6g} "
            f"mode={lc_cal['mode']} r2={r2} "
            f"calibrated={lc_cal['when'] or 'never'}")


def open_log(path, header, with_cal=True):
    """Open a run log, stamp the calibration, write the header.

    A grams column is only meaningful alongside the calibration that produced
    it. Recording it in the file means a run stays interpretable after the
    cell is re-calibrated — which, being a comment line, pandas reads with
    read_csv(path, comment='#')."""
    f = open(path, "w", newline="")
    if with_cal:
        f.write(lc_cal_line() + "\n")
    wr = csv.writer(f)
    wr.writerow(header)
    return f, wr


lc_cal_load()


def lc_reader():
    while running:
        s = lc["ser"]
        if s is None or not s.is_open:
            time.sleep(0.2)
            continue
        try:
            raw = s.readline()
        except Exception:
            time.sleep(0.2)
            continue
        if not raw:
            continue
        line = raw.decode(errors="replace").strip()
        # [g3-C] Only accept lines that are purely a numeric record. The old
        # parser pulled the first number out of ANY line, so one friendly
        # banner from the Arduino — "HX711 ready v1.0" — entered the buffer as
        # a reading of 711 g at 1.0 degC, and a boot message lands in exactly
        # the window a calibration or a tare is captured in.
        if not line or line[0] == "#" or _letters.search(line):
            continue
        nums = _num.findall(line)
        if not nums:
            continue
        try:
            rawv = float(nums[0])
            grams = (rawv - lc_cal["tare"]) * lc_cal["scale"]   # [g3-B]
            temp = float(nums[1]) if len(nums) > 1 else None
            now = time.time()
            with lc_lock:
                lc_buf.append((now, grams, temp))
                lc_raw_buf.append((now, rawv))
            lc["last"] = line
        except ValueError:
            pass


def lc_connect(port):
    lc_disconnect()
    try:
        s = serial.Serial(port, BAUD_LC, timeout=0.2)
        time.sleep(0.3)
        with lc["lock"]:
            lc["ser"] = s
        lc_status.config(text=f"● {port}", fg=GREEN)
    except Exception as e:
        lc_status.config(text=f"● {e}", fg=RED)


def lc_disconnect():
    with lc["lock"]:
        if lc["ser"] is not None:
            try:
                lc["ser"].close()
            except Exception:
                pass
            lc["ser"] = None


def lc_window(t0, t1):
    """samples with t0 <= t <= t1"""
    return [s for s in snap_lc() if t0 <= s[0] <= t1]


def lc_latest(seconds=0.4):
    now = time.time()
    vals = [g for (t, g, _) in snap_lc() if now - t <= seconds]
    return robust_mean(vals)[0] if vals else None


def snap_lc_raw():
    with lc_lock:
        return list(lc_raw_buf)


def lc_raw_latest(seconds=1.0):
    """[g3-B] Trimmed mean of the RAW stream. Calibration must never be
    computed from the calibrated value — that folds the old scale into the new
    one, so a second calibration silently squares the error."""
    now = time.time()
    vals = [v for (t, v) in snap_lc_raw() if now - t <= seconds]
    return robust_mean(vals)[0] if vals else None


def lc_raw_settled(seconds=2.0):
    """→ (mean, drift, n) over the window, or (None, None, 0).

    `drift` is the difference between the second half of the window and the
    first. A calibration point captured while the cell is still ringing down
    from the mass being placed is simply a wrong point, and it is wrong in a
    way that looks fine in the table — it lands somewhere plausible and then
    bends the fitted line. Averaging harder does not fix it, because the error
    is a trend and not noise; the only defence is to notice the trend."""
    now = time.time()
    win = [(t, v) for (t, v) in snap_lc_raw() if now - t <= seconds]
    if len(win) < 6:
        return (None, None, len(win))
    half = win[len(win) // 2:]
    first = win[:len(win) // 2]
    m, _ = robust_mean([v for _, v in win])
    a, _ = robust_mean([v for _, v in first])
    b, _ = robust_mean([v for _, v in half])
    return (m, (b - a) if (a is not None and b is not None) else None, len(win))


def lc_drift_note(drift):
    """A drift worth mentioning, expressed in grams at the current scale."""
    if drift is None:
        return ""
    g = abs(drift * lc_cal["scale"])
    if g < 0.5:
        return ""
    return (f"  ⚠ the reading is still moving ({g:.1f} g across the sample "
            f"window) — let it settle and take it again.")


# ── temperature source [g3-A] ──────────────────────────────────
# Two possible sources, and which one is live changes what a temperature
# MEANS. The driver board's thermistor sits on the motor and shares the
# firmware's clock with Iq; the load-cell Arduino's sensor is wherever it was
# taped and runs on its own timebase, so its samples cannot be aligned with a
# current step to better than the two devices' drift. Prefer the driver, fall
# back to the Arduino, and always be able to say which — every place that shows
# or logs a temperature also shows the source.
def temp_src():
    """'driver' | 'loadcell' | None"""
    if T["temp_ok"] and T["temp"] is not None and dev_alive():
        return "driver"
    now = time.time()
    if any(tp is not None and now - t <= 5.0 for (t, _, tp) in snap_lc()):
        return "loadcell"
    return None


def temp_window(t0, t1, src=None):
    """[(t, degC)] from whichever source is live, oldest first."""
    src = src or temp_src()
    if src == "driver":
        return [(t, c) for (t, c) in snap_hist(temp_hist) if t0 <= t <= t1]
    if src == "loadcell":
        return [(t, tp) for (t, _, tp) in snap_lc()
                if tp is not None and t0 <= t <= t1]
    return []


def temp_now(seconds=2.0, src=None):
    now = time.time()
    vals = [c for (_, c) in temp_window(now - seconds, now, src)]
    return robust_mean(vals)[0] if vals else None


def temp_label():
    s = temp_src()
    return {"driver": "driver board (GPIO3)",
            "loadcell": "loadcell Arduino"}.get(s, "no temperature sensor")


def robust_mean(vals, trim=0.2):
    """trimmed mean + std: sort, drop `trim` fraction each side, average."""
    if not vals:
        return None, None
    v = sorted(vals)
    k = int(len(v) * trim)
    core = v[k:len(v) - k] if len(v) - 2 * k >= 1 else v
    m = sum(core) / len(core)
    sd = (sum((x - m) ** 2 for x in core) / len(core)) ** 0.5
    return m, sd


def _mean_rpm(pts):
    """Mean speed over a span, from the ANGLE endpoints."""
    if len(pts) < 4:
        return None
    (t0, a0), (t1, a1) = pts[0], pts[-1]
    dt = t1 - t0
    return None if dt < 1e-3 else (a1 - a0) / dt * 60.0 / (2 * math.pi)


def kv_speed(window=1.0, nsub=4):
    """(mean rpm, spread rpm) over `window`, measured from shaft ANGLE.

    Two separate improvements over averaging the velocity field:

    1. ACCURACY. `vel` is a differentiated, low-pass-filtered estimate, so
       averaging it inherits both the encoder's per-sample quantisation
       (0.38 rad/s at 1 kHz) and the filter's lag. Shaft angle is absolute and
       accumulates full rotations, so (a1-a0)/dt over a whole second is a mean
       speed with essentially no noise — the endpoints are all that matter.

    2. AN HONEST STEADY TEST. The old indicator compared the sample standard
       deviation against 1% of target. Sample scatter does not shrink when the
       speed is genuinely steady, so that test could stay red forever, or go
       green on a drifting average. What matters for a back-EMF reading is
       whether the MEAN is holding still, so this splits the window into
       sub-windows and reports the spread of their means. Real drift shows up;
       per-sample noise does not."""
    now = time.time()
    pts = [(t, a) for (t, a) in snap_hist(ang_hist) if now - t <= window]
    if len(pts) < 8:
        return (None, None)
    mean = _mean_rpm(pts)
    if mean is None:
        return (None, None)
    sub = []
    for k in range(nsub):
        lo = now - window + k * window / nsub
        hi = lo + window / nsub
        seg = [p for p in pts if lo <= p[0] <= hi]
        v = _mean_rpm(seg)
        if v is not None:
            sub.append(v)
    spread = (max(sub) - min(sub)) if len(sub) >= 2 else None
    return (mean, spread)


def sense_alive():
    """measured-current path considered alive if it shows real signal while
    the firmware is commanding current"""
    now = time.time()
    meas = [abs(i) for (t, i) in snap_hist(iq_hist) if now - t <= 2.0]
    cmd = [abs(i) for (t, i) in snap_hist(iqc_hist) if now - t <= 2.0]
    if not meas or not cmd:
        return True                      # no data yet: don't cry wolf
    if max(cmd) < 0.05:
        return True                      # nothing commanded: can't judge
    return max(meas) > 0.25 * max(cmd)


def iqc_avg(seconds=1.0):
    now = time.time()
    return robust_mean([i for (t, i) in snap_hist(iqc_hist) if now - t <= seconds])


def iq_avg(seconds=1.0):
    now = time.time()
    return robust_mean([i for (t, i) in snap_hist(iq_hist) if now - t <= seconds])


# ── logging ────────────────────────────────────────────────────
def serial_no():
    return re.sub(r"[^A-Za-z0-9_\-]", "-", e_serial.get().strip())


def log_path(experiment):
    sn = serial_no()
    if not sn:
        return None
    os.makedirs("labdata", exist_ok=True)
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    return f"labdata/{sn}_{experiment}_{ts}.csv"


# ── first-order exponential fit [g3-A] ─────────────────────────
# T(t) = A + B·exp(−(t−t0)/tau)   — A is the asymptote, B is negative while
# heating and positive while cooling. With tau FIXED the remaining two
# parameters are linear, so the whole fit is a one-dimensional search over tau
# with an exact least-squares solve inside it: no gradients, no initial-guess
# sensitivity, no iteration that can fail to converge in front of the operator.
def _lsq_exp(ts, cs, tau):
    t0 = ts[0]
    e = [math.exp(-(t - t0) / tau) for t in ts]
    n = len(ts); s1 = sum(e); s2 = sum(x * x for x in e)
    sy = sum(cs); sye = sum(c * x for c, x in zip(cs, e))
    det = n * s2 - s1 * s1
    if abs(det) < 1e-9:
        return None
    A = (s2 * sy - s1 * sye) / det
    B = (n * sye - s1 * sy) / det
    return A, B, sum((c - (A + B * x)) ** 2 for c, x in zip(cs, e))


def _seed_tau(ts, cs):
    """A rough tau from dT/dt = (T_inf − T)/tau, which is a straight line in
    (T, dT/dt). Only used to centre the search below — it is unbiased but very
    noisy, because differentiating a 0.1 degC-resolution sensor is."""
    k = 2
    sm = [sum(cs[max(0, i - k):i + k + 1]) / len(cs[max(0, i - k):i + k + 1])
          for i in range(len(cs))]
    xs, ys = [], []
    for i in range(1, len(sm) - 1):
        dt = ts[i + 1] - ts[i - 1]
        if dt > 1e-6:
            xs.append(sm[i]); ys.append((sm[i + 1] - sm[i - 1]) / dt)
    f = linfit(xs, ys) if len(xs) >= 6 else None
    if not f or f[0] >= -1e-12:
        return None
    return -1.0 / f[0]


def expfit(ts, cs):
    """→ (tau_s, asymptote_C, B, r2) or None. r2 is against the TEMPERATURE
    data, not against the derivative, so it means what a reader expects."""
    if len(ts) < 8:
        return None
    span = ts[-1] - ts[0]
    if span <= 0:
        return None
    seed = _seed_tau(ts, cs) or span / 2.0
    seed = min(max(seed, span / 100.0), span * 20.0)
    lo, hi = seed / 10.0, seed * 10.0
    best = None
    for _ in range(4):                       # log-grid, then zoom in 4 times
        for i in range(41):
            tau = lo * (hi / lo) ** (i / 40.0)
            r = _lsq_exp(ts, cs, tau)
            if r and (best is None or r[2] < best[3]):
                best = (tau, r[0], r[1], r[2])
        if best is None:
            return None
        lo, hi = best[0] / 2.5, best[0] * 2.5
    tau, A, B, sse = best
    my = sum(cs) / len(cs)
    sst = sum((c - my) ** 2 for c in cs)
    return tau, A, B, (1.0 - sse / sst if sst > 1e-12 else 1.0)


def linfit(xs, ys):
    n = len(xs)
    mx = sum(xs) / n; my = sum(ys) / n
    sxx = sum((x - mx) ** 2 for x in xs)
    if sxx < 1e-12:
        return None
    a = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
    b = my - a * mx
    ss_res = sum((y - (a * x + b)) ** 2 for x, y in zip(xs, ys))
    ss_tot = sum((y - my) ** 2 for y in ys)
    r2 = 1.0 - ss_res / ss_tot if ss_tot > 1e-12 else 1.0
    return a, b, r2


# ── UI helpers ─────────────────────────────────────────────────
root = tk.Tk()
root.title("ExArMo Lab — Motor Tester")
# Fit the screen we actually have instead of assuming a 1660x980 desktop.
_sw, _sh = root.winfo_screenwidth(), root.winfo_screenheight()
root.geometry(f"{min(1660, _sw - 80)}x{min(980, _sh - 120)}+20+20")
root.minsize(1000, 560)
root.configure(bg=BG)


def card(parent):
    o = tk.Frame(parent, bg=BORDER, padx=1, pady=1)
    i = tk.Frame(o, bg=SURFACE, padx=22, pady=18)
    i.pack(fill="both", expand=True)
    return o, i


def safe_tick(fn, period):
    """Run a periodic callback so that an exception cannot end the chain.

    Every live readout in this program depends on its `root.after` loop being
    re-armed. A single raise inside one tick used to unschedule it for good,
    which presents as "the numbers stopped updating" with nothing in the log
    and no traceback anywhere the operator can see. Now the error goes to the
    console and the loop carries on."""
    def wrapper():
        try:
            fn()
        except Exception as exc:
            clog(f"{getattr(fn, '__name__', 'tick')} error: {exc!r}", "err")
        finally:
            root.after(period, wrapper)
    return wrapper


def scroll_column(parent):
    """A vertically scrollable host for a tab's left-hand control column.

    The control columns have grown well past a laptop screen, and a button you
    cannot reach is a button that does not exist. Returns (holder, inner):
    pack the holder, put the card in the inner frame. The canvas viewport is
    kept exactly as wide as its content so nothing at the right edge gets
    clipped — only vertical scrolling is ever needed."""
    holder = tk.Frame(parent, bg=BG)
    cv = tk.Canvas(holder, bg=BG, highlightthickness=0, bd=0)
    sb = ttk.Scrollbar(holder, orient="vertical", command=cv.yview)
    cv.configure(yscrollcommand=sb.set)
    cv.pack(side="left", fill="both", expand=True)
    sb.pack(side="right", fill="y")
    inner = tk.Frame(cv, bg=BG)
    cv.create_window((0, 0), window=inner, anchor="nw")

    def _cfg(e):
        cv.configure(scrollregion=cv.bbox("all"), width=e.width)
    inner.bind("<Configure>", _cfg)

    def _wheel(e):
        # Windows sends delta in steps of 120; macOS sends small values (often
        # +/-1); X11 sends Button-4/5 instead of a delta at all. Normalise to
        # one notch so the wheel feels the same everywhere.
        delta = getattr(e, "delta", 0)
        if delta:
            cv.yview_scroll(-1 if delta > 0 else 1, "units")
        elif getattr(e, "num", 0) == 4:
            cv.yview_scroll(-1, "units")
        elif getattr(e, "num", 0) == 5:
            cv.yview_scroll(1, "units")

    def _bind(_e):
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            cv.bind_all(seq, _wheel)

    def _unbind(_e):
        for seq in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
            cv.unbind_all(seq)

    cv.bind("<Enter>", _bind)
    cv.bind("<Leave>", _unbind)
    return holder, inner


def section(parent, text):
    tk.Label(parent, text=text.upper(), bg=SURFACE, fg=FAINT,
             font=("Segoe UI", 10, "bold")).pack(anchor="w", pady=(0, 8))


def btn(parent, text, bg, fg, cmd, width=None):
    b = tk.Button(parent, text=text, command=cmd, bg=bg, fg=fg,
                  activebackground=bg, activeforeground=fg, relief="flat",
                  bd=0, font=F_BTN, padx=18, pady=10, cursor="hand2",
                  highlightthickness=0)
    if width:
        b.config(width=width)
    return b


def entry_row(parent, label, default, width=8):
    f = tk.Frame(parent, bg=SURFACE)
    f.pack(fill="x", pady=3)
    tk.Label(f, text=label, bg=SURFACE, fg=TEXT, font=F_LBL).pack(side="left")
    e = tk.Entry(f, bg=FIELD, fg=BLUE, insertbackground=TEXT, relief="flat",
                 font=("Consolas", 14, "bold"), width=width, justify="center",
                 highlightthickness=1, highlightbackground=BORDER,
                 highlightcolor=BLUE)
    e.insert(0, str(default))
    e.pack(side="right", ipady=3)
    return e


def mkstatus(parent):
    l = tk.Label(parent, text="●  Ready", bg=SURFACE, fg=MUTED, font=F_LBL,
                 wraplength=330, justify="left")
    l.pack(anchor="w", pady=(8, 0))

    def set_(t, c):
        l.config(text="●  " + t, fg=c)
    return set_


def big_value(parent, caption, color=BLUE):
    v = tk.Label(parent, text="—", bg=SURFACE, fg=color, font=F_BIG)
    v.pack()
    tk.Label(parent, text=caption, bg=SURFACE, fg=FAINT, font=F_SM).pack()
    return v


STYLE = ttk.Style(); STYLE.theme_use("clam")
STYLE.configure("Treeview", background=SURFACE, fieldbackground=SURFACE,
                foreground=TEXT, rowheight=28, font=("Consolas", 12),
                borderwidth=0)
STYLE.configure("Treeview.Heading", background=FIELD, foreground=MUTED,
                font=("Segoe UI", 10, "bold"), borderwidth=0)


def clear_table(tbl):
    for it in tbl.get_children():
        tbl.delete(it)


def drop_last_row(tbl):
    kids = tbl.get_children()
    if kids:
        tbl.delete(kids[-1])


def confirm_reset(n, what="rows"):
    """Ask before discarding collected data.

    A reset that fires by accident costs a whole run — on this bench that can
    be twenty minutes of adding weights by hand — so it asks, but only when
    there is actually something to lose."""
    if n <= 0:
        return True
    return messagebox.askyesno("Reset data",
                               f"Discard {n} {what} and start recording again?")


def mktable(parent, cols, height=8):
    t = ttk.Treeview(parent, columns=[c[0] for c in cols], show="headings",
                     height=height)
    for cid, txt, w in cols:
        t.heading(cid, text=txt)
        t.column(cid, width=w, anchor="center")
    t.pack(pady=(8, 6))
    return t


def draw_ts(cv, series, color, ylabel, marks=(), y2=None, color2=PURPLE,
            unit1="", unit2="", label1="", label2=""):
    """Time-series plot, last 60 s. series / y2 = list[(t, v)].

    Both series are drawn as MAGNITUDE. Running the motor CCW makes Iq
    negative, and plotting it signed sent the current trace DOWNWARD at every
    step while the force went up — two curves that mirror each other when the
    physics says they should track. Sign is a direction convention and belongs
    in the readouts, not in a trend chart whose job is to show that torque and
    force rise together. Every fit downstream already uses abs().

    Each series is auto-scaled independently on its own axis, so the min/max
    labels below are what make the chart readable at all — without them two
    normalised curves share a frame and neither has a value.
    """
    cv.delete("all")
    w = int(cv.winfo_width() or 600); h = int(cv.winfo_height() or 240)
    cv.create_rectangle(1, 1, w - 1, h - 1, outline=BORDER, fill="#fbfcfe")
    now = time.time(); t0 = now - 60.0
    top, bot = 30, h - 18                       # leave room for the header row

    def plot(data, col):
        pts = [(t, abs(v)) for (t, v) in data
               if t >= t0 and v is not None and math.isfinite(v)]
        if len(pts) < 2:
            return None
        vs = [v for _, v in pts]
        lo, hi = min(vs), max(vs)
        if hi - lo < 1e-9:                      # flat line: keep it centred
            lo -= 0.5; hi += 0.5
        pad = 0.1 * (hi - lo)
        lo -= pad; hi += pad
        poly = []
        for t, v in pts:
            x = (t - t0) / 60.0 * (w - 20) + 10
            y = bot - (v - lo) / (hi - lo) * (bot - top)
            poly += [x, y]
        cv.create_line(*poly, fill=col, width=2)
        return min(vs), max(vs)

    for tm in marks:                            # step boundaries, behind traces
        if tm >= t0:
            x = (tm - t0) / 60.0 * (w - 20) + 10
            cv.create_line(x, top - 4, x, bot, fill=BORDER, dash=(3, 4))

    r1 = plot(series, color)
    r2 = plot(y2, color2) if y2 else None

    cv.create_text(12, 8, text=ylabel, fill=MUTED, font=F_SM, anchor="nw")
    # numeric range per series, in that series' own colour
    if r1:
        cv.create_text(12, h - 14,
                       text=f"{label1 or 'left'}  {r1[0]:.1f} – {r1[1]:.1f} {unit1}",
                       fill=color, font=F_SM, anchor="nw")
    if r2:
        cv.create_text(w - 12, h - 14,
                       text=f"{label2 or 'right'}  {r2[0]:.2f} – {r2[1]:.2f} {unit2}",
                       fill=color2, font=F_SM, anchor="ne")


def draw_scatter(cv, xs, ys, fit=None, xlabel="", ylabel="", color=BLUE):
    """Scatter of the raw points with the fitted line through them.

    Every tab reports a slope and an R², but a number cannot show you WHICH
    point is wrong. On these rigs the failures are all shape failures — a
    dead-zone point sitting on the floor, a step that saturated, one outlier
    dragging the slope — and they are obvious in a picture and invisible in a
    correlation coefficient. The axes are anchored at the origin so the
    intercept (friction, preload, offset) is always in view: that term is
    physics here, not a nuisance."""
    cv.delete("all")
    w = int(cv.winfo_width() or 320); h = int(cv.winfo_height() or 200)
    L, R, T, B = 50, 12, 16, 30
    cv.create_rectangle(1, 1, w - 1, h - 1, outline=BORDER, fill="#fbfcfe")
    pts = [(x, y) for x, y in zip(xs, ys)
           if x is not None and y is not None
           and math.isfinite(x) and math.isfinite(y)]
    if not pts:
        cv.create_text(w / 2, h / 2, text="no points yet", fill=FAINT, font=F_SM)
        return
    xmin = min(p[0] for p in pts); xmax = max(p[0] for p in pts)
    ymin = min(p[1] for p in pts); ymax = max(p[1] for p in pts)
    if fit:
        a, b, _ = fit
        for xx in (xmin, xmax):
            ymin = min(ymin, a * xx + b); ymax = max(ymax, a * xx + b)
    xmin = min(xmin, 0.0); ymin = min(ymin, 0.0)      # keep the intercept visible
    if xmax - xmin < 1e-12: xmax = xmin + 1.0
    if ymax - ymin < 1e-12: ymax = ymin + 1.0
    px = 0.08 * (xmax - xmin); py = 0.12 * (ymax - ymin)
    xmax += px; ymax += py

    def X(v): return L + (v - xmin) / (xmax - xmin) * (w - L - R)
    def Y(v): return h - B - (v - ymin) / (ymax - ymin) * (h - B - T)

    cv.create_line(L, h - B, w - R, h - B, fill=BORDER)
    cv.create_line(L, T, L, h - B, fill=BORDER)
    if fit:
        a, b, _ = fit
        cv.create_line(X(xmin), Y(a * xmin + b), X(xmax), Y(a * xmax + b),
                       fill=GREEN, width=2)
    for x, y in pts:
        cv.create_oval(X(x) - 3.5, Y(y) - 3.5, X(x) + 3.5, Y(y) + 3.5,
                       fill=color, outline="")
    cv.create_text(L - 5, Y(ymax), text=f"{ymax:.3g}", fill=MUTED, font=F_SM, anchor="e")
    cv.create_text(L - 5, Y(ymin), text=f"{ymin:.3g}", fill=MUTED, font=F_SM, anchor="e")
    cv.create_text(X(xmin), h - B + 5, text=f"{xmin:.3g}", fill=MUTED, font=F_SM, anchor="nw")
    cv.create_text(w - R, h - B + 5, text=f"{xmax:.3g}", fill=MUTED, font=F_SM, anchor="ne")
    cv.create_text(L + 5, T - 4, text=ylabel, fill=MUTED, font=F_SM, anchor="nw")
    cv.create_text((L + w - R) / 2, h - 9, text=xlabel, fill=FAINT, font=F_SM)


def draw_bars(cv, labels, values, ylabel="", warn_at=None):
    """Bar chart with the mean drawn across it — for comparing what should be
    three identical quantities. Phase-to-phase resistance is exactly that: any
    real difference between the bars is a winding fault, and a picture makes an
    outlier obvious at a glance."""
    cv.delete("all")
    w = int(cv.winfo_width() or 320); h = int(cv.winfo_height() or 200)
    L, R, T, B = 56, 12, 18, 30
    cv.create_rectangle(1, 1, w - 1, h - 1, outline=BORDER, fill="#fbfcfe")
    vals = [v for v in values if v is not None and math.isfinite(v)]
    if not vals:
        cv.create_text(w / 2, h / 2, text="no readings yet", fill=FAINT, font=F_SM)
        return
    vmax = max(vals) * 1.25
    vmin = 0.0
    mean = sum(vals) / len(vals)
    n = len(labels)
    slot = (w - L - R) / max(n, 1)

    def Y(v): return h - B - (v - vmin) / (vmax - vmin) * (h - B - T)

    cv.create_line(L, h - B, w - R, h - B, fill=BORDER)
    spread = (max(vals) - min(vals)) / mean * 100 if mean else 0
    bad = warn_at is not None and spread > warn_at
    for i, (lab, v) in enumerate(zip(labels, values)):
        if v is None or not math.isfinite(v):
            continue
        x0 = L + i * slot + slot * 0.22
        x1 = L + i * slot + slot * 0.78
        cv.create_rectangle(x0, Y(v), x1, h - B,
                            fill=(RED if bad else BLUE), outline="")
        cv.create_text((x0 + x1) / 2, Y(v) - 8, text=f"{v:.4g}",
                       fill=TEXT, font=F_SM)
        cv.create_text((x0 + x1) / 2, h - B + 12, text=lab, fill=MUTED, font=F_SM)
    cv.create_line(L, Y(mean), w - R, Y(mean), fill=AMBER, dash=(4, 3))
    cv.create_text(w - R, Y(mean) - 8, text=f"mean {mean:.4g}", fill=AMBER,
                   font=F_SM, anchor="ne")
    cv.create_text(L + 4, T - 6, text=ylabel, fill=MUTED, font=F_SM, anchor="nw")


# ── header ─────────────────────────────────────────────────────
head = tk.Frame(root, bg=SURFACE)
head.pack(fill="x")
hb = tk.Frame(head, bg=SURFACE); hb.pack(side="left", padx=22, pady=12)
tk.Label(hb, text="Ex", bg=SURFACE, fg=AMBER, font=F_TITLE).pack(side="left")
tk.Label(hb, text="ArMo Lab", bg=SURFACE, fg=TEXT, font=F_TITLE).pack(side="left")

sn_f = tk.Frame(head, bg=SURFACE); sn_f.pack(side="left", padx=30)
tk.Label(sn_f, text="Motor serial no.", bg=SURFACE, fg=MUTED, font=F_LBL).pack(side="left", padx=(0, 8))
e_serial = tk.Entry(sn_f, bg=FIELD, fg=TEXT, insertbackground=TEXT, relief="flat",
                    font=("Consolas", 15, "bold"), width=14, justify="center",
                    highlightthickness=1, highlightbackground=BORDER, highlightcolor=BLUE)
e_serial.pack(side="left", ipady=4)


def port_picker(parent, label, connect_fn, baud):
    f = tk.Frame(parent, bg=SURFACE); f.pack(side="left", padx=14)
    tk.Label(f, text=label, bg=SURFACE, fg=MUTED, font=F_SM).pack(side="left", padx=(0, 6))
    var = tk.StringVar()
    ports = [p.device for p in serial.tools.list_ports.comports()] or ["—"]
    var.set(ports[0])
    om = tk.OptionMenu(f, var, *ports)
    om.config(bg=FIELD, fg=TEXT, relief="flat", bd=0, highlightthickness=0, font=F_SM)
    om.pack(side="left")

    def refresh():
        m = om["menu"]; m.delete(0, "end")
        for p in [q.device for q in serial.tools.list_ports.comports()] or ["—"]:
            m.add_command(label=p, command=lambda v=p: var.set(v))
    tk.Button(f, text="↻", command=refresh, bg=FIELD, fg=MUTED, relief="flat",
              bd=0, font=F_SM, padx=6, cursor="hand2", highlightthickness=0).pack(side="left", padx=3)
    tk.Button(f, text="Connect", command=lambda: connect_fn(var.get()), bg=FIELD,
              fg=BLUE, relief="flat", bd=0, font=("Segoe UI", 11, "bold"),
              padx=10, pady=3, cursor="hand2", highlightthickness=0).pack(side="left")
    st = tk.Label(f, text="● off", bg=SURFACE, fg=FAINT, font=F_SM)
    st.pack(side="left", padx=(6, 0))
    return st


conn_f = tk.Frame(head, bg=SURFACE); conn_f.pack(side="right", padx=18)
dev_status = port_picker(conn_f, "Driver", dev_connect, BAUD_DEV)
lc_status = port_picker(conn_f, "Loadcell/Temp", lc_connect, BAUD_LC)

# tab bar
tabs_bar = tk.Frame(root, bg=SURFACE)
tabs_bar.pack(fill="x")
tk.Frame(root, bg=BORDER, height=1).pack(fill="x")

# [g2-A] sticky fault banner — a firmware fault stays on screen until it is
# cleared by a good event, instead of being overwritten by the next keepalive.
banner = tk.Label(root, text="", bg="#fdecee", fg=RED, font=("Segoe UI", 12, "bold"),
                  anchor="w", padx=18, pady=6)

body = tk.Frame(root, bg=BG)
body.pack(fill="both", expand=True, padx=24, pady=18)

foot = tk.Frame(root, bg=SURFACE)
foot.pack(side="bottom", fill="x")
tk.Frame(root, bg=BORDER, height=1).pack(side="bottom", fill="x")
foot_state = tk.Label(foot, text="—", bg=SURFACE, fg=MUTED,
                      font=("Segoe UI", 12, "bold"))
foot_state.pack(side="left", padx=(22, 16), pady=6)
foot_line = tk.Label(foot, text="", bg=SURFACE, fg=FAINT, font=("Consolas", 12),
                     anchor="w")
foot_line.pack(side="left", fill="x", expand=True)


def foot_tick():
    live = dev_alive()
    foot_state.config(text=STATE_NAMES.get(T["state"], "?") + ("" if live else "  (no telemetry)"),
                      fg=GREEN if (live and T["state"]) else (MUTED if live else RED))
    foot_line.config(text=f"rx: {link['rx'][-90:]}    tx: {link['tx'][-20:]}", fg=FAINT)
    if link["fault"]:
        banner.config(text="⚠  " + link["fault"] + "     (Diagnostics tab has the full console)")
        banner.pack(fill="x", before=body)
    else:
        banner.pack_forget()


TABS = []
cur_tab = [0]


def add_tab(name, frame):
    idx = len(TABS)
    b = tk.Label(tabs_bar, text=name, bg=SURFACE, fg=MUTED,
                 font=("Segoe UI", 13, "bold"), padx=16, pady=9, cursor="hand2")
    b.pack(side="left", padx=(14 if idx == 0 else 2, 2))
    b.bind("<Button-1>", lambda e, k=idx: show_tab(k))
    TABS.append((b, frame))


def show_tab(k):
    cur_tab[0] = k
    for i, (b, f) in enumerate(TABS):
        if i == k:
            b.config(bg=FIELD, fg=BLUE)
            f.pack(fill="both", expand=True)
        else:
            b.config(bg=SURFACE, fg=MUTED)
            f.pack_forget()


def stop_all():
    dev_send("O0")


# ═════════════ TAB 0 · DIAGNOSTICS ═════════════════════════════
# This tab exists because v1 gave you no way to answer the only question that
# matters when nothing happens: WHICH link is broken — FOC init, the command
# path, the direction, or the current sense?
dg_fr = tk.Frame(body, bg=BG)

dg_sc_o, dg_sc = scroll_column(dg_fr); dg_sc_o.pack(side="left", fill="y", padx=(0, 14))
dg_l_o, dg_l = card(dg_sc); dg_l_o.pack(fill="both", expand=True)
section(dg_l, "Firmware health")
dg_flag_lbls = []
for _bit, _name in FLAG_BITS:
    r = tk.Frame(dg_l, bg=SURFACE); r.pack(fill="x", pady=2)
    dot = tk.Label(r, text="●", bg=SURFACE, fg=FAINT, font=("Segoe UI", 14))
    dot.pack(side="left", padx=(0, 8))
    tk.Label(r, text=_name, bg=SURFACE, fg=TEXT, font=F_LBL).pack(side="left")
    dg_flag_lbls.append(dot)
dg_fw = tk.Label(dg_l, text="firmware: —", bg=SURFACE, fg=FAINT, font=F_SM)
dg_fw.pack(anchor="w", pady=(8, 0))

section(dg_l, "Push direction  (Ps±1)")
dir_var = tk.IntVar(value=1)
dr = tk.Frame(dg_l, bg=SURFACE); dr.pack(fill="x", pady=(0, 6))


def set_dir():
    dev_send(f"Ps{dir_var.get()}")


for _txt, _v in (("+1  (CW)", 1), ("−1  (CCW)", -1)):
    tk.Radiobutton(dr, text=_txt, variable=dir_var, value=_v, command=set_dir,
                   bg=SURFACE, fg=TEXT, selectcolor=FIELD, font=F_LBL,
                   activebackground=SURFACE, highlightthickness=0).pack(side="left", padx=(0, 14))
tk.Label(dg_l, text="Jog, watch the grams. If the arm moves AWAY\nfrom the cell, flip this sign, then re-run the test.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(0, 8))

section(dg_l, "Manual jog")
dg_jog_i = entry_row(dg_l, "Jog current (A)", 0.5)
dg_jog_t = entry_row(dg_l, "Jog time (s)", 2.0)
dg_lever = entry_row(dg_l, "Loadcell lever arm (m)", 0.10)


def engage_until_contact(z, thresh_g, i_start, i_max, step, dwell, alive=None,
                         report=None):
    """Raise the push current until the cell ACTUALLY reads force.

    A fixed engage current is a guess about breakaway torque, and breakaway is
    exactly the thing we do not know yet: static friction plus the gravity
    component has to be overcome before the first gram reaches the cell. Guess
    low and the arm never arrives (and you end up pushing it by hand); guess
    high and first contact is a slam. So don't guess — start low, step up, and
    stop the moment contact is real.

    The current at which contact happens is itself a measurement: it is the
    breakaway current, and it should agree with the friction intercept the Kt
    fit reports. Returns (True, current) or (False, None)."""
    i = i_start
    while i <= i_max + 1e-9:
        dev_send(f"C{i:.3f}")
        if report:
            report(i)
        t_end = time.time() + dwell
        while time.time() < t_end:
            if alive is not None and not alive():
                return (False, None)
            time.sleep(0.1)
            gg = lc_latest(0.5)
            if gg is not None and (gg - z) >= thresh_g:
                return (True, i)
        i += step
    return (False, None)


def _baseline():
    """Zero the load cell with NO current applied. Absolute grams are
    meaningless here — the arm's own weight is already sitting on the cell, so
    only the CHANGE caused by current tells you anything."""
    dev_send("O0")
    time.sleep(0.8)
    return lc_latest(0.6)


def dg_jog():
    try:
        i = float(dg_jog_i.get()); t = max(0.2, min(20.0, float(dg_jog_t.get())))
    except ValueError:
        dg_set("Check the numbers", AMBER); return

    def run():
        dg_set("Zeroing (no current)…", BLUE)
        base = _baseline()
        t_start = time.time()
        dev_send(f"C{i:.3f}")
        dg_set(f"Jogging at {i:.2f} A for {t:.1f} s…", BLUE)
        time.sleep(t)
        m, _ = iq_avg(min(t, 1.0))
        g = lc_latest(0.6)
        dev_send("C0"); stop_all()
        peak = max([abs(r) for (ts, r) in snap_hist(rpm_hist) if ts >= t_start] or [0.0])
        d = None if (g is None or base is None) else (g - base)
        txt = (f"Iq meas {0.0 if m is None else m:+.3f} A · peak {peak:.0f} rpm · "
               f"Δ loadcell {'--' if d is None else f'{d:+.1f} g'} "
               f"(from {'--' if base is None else f'{base:.1f}'} g)")
        if peak > 60 and (d is None or abs(d) < 5):
            root.after(0, lambda: dg_set(txt + "  — shaft was FREE (spun up, no force). "
                                         "Load the arm against the cell and jog again.", AMBER))
        elif d is not None and d < -3:
            root.after(0, lambda: dg_set(txt + "  — NEGATIVE: current is LIFTING the arm OFF "
                                         "the cell, not pressing it. Flip the direction above.", RED))
        else:
            root.after(0, lambda: dg_set(txt, GREEN))
    threading.Thread(target=run, daemon=True).start()


sweep_hist = []          # [(slope_g_per_A, kt_mNm_per_A)] across runs


def dg_sweep():
    """Direction + linearity sweep.

    Judged by a least-squares FIT, not by comparing endpoints. The earlier
    version tested `last_delta < 2.5 * first_delta`, which any constant
    mechanical preload destroys: an arm already leaning on the cell adds the
    same offset to every point, so a perfectly linear response reads as
    "not proportional". Slope is what carries the physics — tau = Kt*Iq + tau_f
    is exactly the model the Kt tabs fit — and slope is immune to that offset.
    The intercept is worth reading too: it IS the preload, in grams."""
    try:
        lever = float(dg_lever.get())
    except ValueError:
        dg_set("Check the lever arm", AMBER); return

    def run():
        if lc["ser"] is None:
            root.after(0, lambda: dg_set("Connect the load cell first", RED)); return
        dg_set("Sweep: zeroing (no current)…", BLUE)
        base = _baseline()
        if base is None:
            root.after(0, lambda: dg_set("No load-cell data", RED)); return
        steps = [0.2, 0.4, 0.6, 0.8, 1.0]
        ok, i_contact = engage_until_contact(base, 8.0, 0.2, 1.5, 0.1, 1.2)
        if not ok:
            dev_send("C0"); stop_all()
            root.after(0, lambda: dg_set(
                "No contact up to 1.5 A — arm not loaded against the cell, or wrong direction.", RED))
            return
        # start at contact: below breakaway the arm is not touching, and a
        # 0 g point drags the slope down while pretending to be data
        steps = [s for s in steps if s >= i_contact - 1e-9] or [i_contact]
        pts = []
        for i in steps:
            dev_send(f"C{i:.3f}")
            root.after(0, lambda i=i: dg_set(f"Sweep: {i:.2f} A…", BLUE))
            time.sleep(1.6)
            gg = lc_latest(0.6)
            m, _ = iq_avg(1.0)
            if gg is not None:
                pts.append((i, gg - base, abs(m) if m is not None else i))
        dev_send("C0"); stop_all()

        rows = " · ".join(f"{i:.1f}A→{d:+.0f}g" for i, d, _ in pts)
        if len(pts) < 3:
            root.after(0, lambda: dg_set("Sweep incomplete — load-cell dropouts. " + rows, AMBER))
            return

        fit = linfit([p[2] for p in pts], [p[1] for p in pts])   # grams vs |Iq meas|
        if fit is None:
            root.after(0, lambda: dg_set(rows + "  fit failed", AMBER)); return
        slope, intercept, r2 = fit
        stats = (f"slope {slope:+.1f} g/A · friction intercept {intercept:+.0f} g · "
                 f"R²={r2:.3f} · breakaway {i_contact:.2f} A")

        if slope < -2:
            msg = ("FALLING with current → the motor is UNLOADING the cell. "
                   "Flip the direction above (Ps) and sweep again.")
            col = RED
        elif abs(slope) < 2:
            msg = ("No torque response → the arm is not loaded against the cell, "
                   "or Iq is clamped. Check Pi and the fixture.")
            col = RED
        elif r2 < 0.90:
            msg = ("Response is NOT linear (R² low) → suspect the dq frame or the "
                   "current-loop tuning. Check id on the right.")
            col = AMBER
        else:
            kt = slope * 1e-3 * G_ACC * lever * 1000.0        # mNm/A, from SLOPE
            msg = f"LINEAR — good. Kt from slope ≈ {kt:.1f} mNm/A."
            col = GREEN
            # cross-check against the independent back-EMF number, if tab 1 has one
            try:
                kv = float(kv_res.get("kv", "")) if kv_res.get("kv") else None
            except ValueError:
                kv = None
            if kv:
                kt_kv = 9.55 / kv * 1000.0
                ratio = kt_kv / kt if kt > 1e-9 else 0
                if ratio > 1.3 or ratio < 0.77:
                    msg += (f" But back-EMF says {kt_kv:.0f} mNm/A — a factor of "
                            f"{ratio:.1f} apart. Linearity is fine, so this is a pure "
                            f"SCALE error: shunt value, amp gain, or the lever arm. "
                            f"Torque magnitudes cannot be trusted until it is resolved.")
                    col = AMBER
                else:
                    msg += f" Back-EMF agrees ({kt_kv:.0f} mNm/A)."
        # Slope across runs is the discriminator: a wrong scale factor (shunt,
        # gain, lever) is CONSTANT, so it cannot move between runs. A wrong
        # commutation angle moves every time the rotor rests somewhere new,
        # because torque falls by cos(error) and the error tracks position.
        if slope > 2:
            sweep_hist.append((slope, slope * 1e-3 * G_ACC * lever * 1000.0))
        if len(sweep_hist) >= 2:
            kts = [k for _, k in sweep_hist[-4:]]
            spread = max(kts) / min(kts) if min(kts) > 1e-9 else 1.0
            hist = " | ".join(f"{k:.0f}" for k in kts)
            msg += f"  ·  Kt across runs: {hist} mNm/A"
            if spread > 1.25:
                msg += (f" — varies {spread:.1f}x between runs. A scale error cannot "
                        f"do that; a wrong commutation angle can. Free the shaft and "
                        f"press RE-ALIGN, then sweep again.")
                col = AMBER
        root.after(0, lambda: dg_set(rows + "   " + stats + "   " + msg, col))
    threading.Thread(target=run, daemon=True).start()


jb = tk.Frame(dg_l, bg=SURFACE); jb.pack(fill="x", pady=(4, 2))
btn(jb, "↻ JOG", BLUE, "white", dg_jog, width=8).pack(side="left", padx=(0, 6))
btn(jb, "■ STOP", RED, "white", stop_all, width=8).pack(side="left")
btn(dg_l, "📈 DIRECTION + LINEARITY SWEEP  (0.2 → 1.0 A, 5 pts)", FIELD, BLUE,
    dg_sweep).pack(fill="x", pady=(6, 0))

section(dg_l, "Current-sense self-test")
tk.Label(dg_l, text="Block the shaft (arm resting on the cell),\nthen run. Firmware pushes 1.0 A for 1 s and\nreports commanded vs measured.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(0, 6))
btn(dg_l, "✓ RUN SELF-TEST (Z)", FIELD, GREEN, lambda: dev_send("Z")).pack(fill="x")
btn(dg_l, "ℹ Status dump (L)", FIELD, BLUE, lambda: dev_send("L")).pack(fill="x", pady=(6, 0))

section(dg_l, "Sensor alignment")
tk.Label(dg_l, text="initFOC only finds a correct zero-electric-angle\nif the shaft was FREE when it ran. Aligned against\na loaded arm it is silently wrong: Iq still tracks\nits setpoint and id still reads ~0, but real torque\nfalls by cos(error) — and changes with position.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(0, 6))


def dg_realign():
    dev_send("O0")
    root.after(400, lambda: dev_send("A"))
    root.after(500, lambda: dev_send("L"))
    dg_set("Re-aligning — the shaft must be FREE to turn. Watch the console.", BLUE)


btn(dg_l, "⟳ RE-ALIGN  (free the shaft first)", FIELD, AMBER, dg_realign).pack(fill="x")

section(dg_l, "Load cell calibration")
tk.Label(dg_l, text="Everything here is measured AGAINST the load cell,\nso if its grams are wrong every Kt is wrong by the\nsame factor — and it will still look perfectly linear.\nCheck it against known masses before trusting a Kt.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(0, 6))
# [g3-B] Three modes, and YOU pick which one is in force:
#   manual  — you type scale and tare; the boxes are the truth
#   point1  — Zero, then one known mass; quick, and blind to linearity
#   multi   — several known masses, least-squares line through them
# The mode matters because only one thing may own `lc_cal` at a time. In
# manual the tick pushes the boxes into lc_cal; in the other two the computed
# result owns it and the boxes merely display it. Without that rule the
# 200 ms tick would overwrite a fresh calibration with whatever stale text
# happened to be sitting in the entry.
lc_mode = tk.StringVar(value=lc_cal["mode"] if lc_cal["mode"] in
                       ("manual", "point1", "multi") else "manual")
_mr = tk.Frame(dg_l, bg=SURFACE); _mr.pack(fill="x", pady=(0, 4))
for _txt, _v in (("Manual", "manual"), ("1-point", "point1"), ("Multi-point", "multi")):
    tk.Radiobutton(_mr, text=_txt, variable=lc_mode, value=_v,
                   command=lambda: dg_lc_mode_changed(),
                   bg=SURFACE, fg=TEXT, selectcolor=FIELD, font=F_SM,
                   activebackground=SURFACE,
                   highlightthickness=0).pack(side="left", padx=(0, 8))

dg_lc_scale = entry_row(dg_l, "Scale  (g per raw unit)", f"{lc_cal['scale']:.6g}")
dg_lc_tare = entry_row(dg_l, "Tare  (raw units)", f"{lc_cal['tare']:.6g}")
dg_lc_known = entry_row(dg_l, "Known mass (g)", 500.0)
dg_lc_live = tk.Label(dg_l, text="", bg=SURFACE, fg=MUTED, font=F_MONO)
dg_lc_live.pack(anchor="w", pady=(4, 2))
_lc_zero = {"v": None}


def dg_lc_sync_entries():
    for e, v in ((dg_lc_scale, lc_cal["scale"]), (dg_lc_tare, lc_cal["tare"])):
        e.delete(0, "end"); e.insert(0, f"{v:.6g}")


def dg_lc_commit(msg, colour=GREEN):
    lc_cal["mode"] = lc_mode.get()
    lc_cal["when"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    dg_lc_sync_entries()
    ok = lc_cal_save()
    dg_set(msg + ("" if ok else "  (could not write labdata/loadcell_cal.json)"),
           colour if ok else AMBER)


def dg_lc_mode_changed():
    m = lc_mode.get()
    lc_cal["mode"] = m
    if m == "manual":
        dg_set("Manual: the Scale and Tare boxes are now in force. "
               "Type values and they take effect immediately.", BLUE)
    elif m == "point1":
        dg_set("1-point: unload the cell → Tare now → put the known mass on → "
               "Calibrate.", BLUE)
    else:
        dg_set("Multi-point: add the empty cell as a 0 g point first, then each "
               "known mass, then Fit.", BLUE)
    lc_cal_save()


def dg_lc_tare_now():
    """Set the zero from the present RAW reading, whatever the mode."""
    v, drift, n = lc_raw_settled(2.0)
    if v is None:
        dg_set("No load-cell data (need ~2 s of samples)", RED); return
    lc_cal["tare"] = v
    _lc_zero["v"] = v
    note = lc_drift_note(drift)
    dg_lc_commit(f"Tared at raw {v:.1f} — the cell should now read ~0 g." + note,
                 AMBER if note else GREEN)


def dg_lc_apply_manual():
    try:
        s = float(dg_lc_scale.get()); t = float(dg_lc_tare.get())
    except ValueError:
        dg_set("Scale and Tare must both be numbers", AMBER); return
    if abs(s) < 1e-12:
        dg_set("A scale of 0 makes every reading 0 g", AMBER); return
    lc_mode.set("manual")
    lc_cal["scale"] = s; lc_cal["tare"] = t; lc_cal["r2"] = None
    dg_lc_commit(f"Applied manually: scale {s:.6g}, tare {t:.6g}.", GREEN)


def dg_lc_calibrate():
    """One known mass against the captured zero."""
    if _lc_zero["v"] is None:
        dg_set("Press 'Tare now' first, with nothing on the cell", AMBER); return
    v, drift, n = lc_raw_settled(2.0)
    if v is None:
        dg_set("No load-cell data (need ~2 s of samples)", RED); return
    try:
        known = float(dg_lc_known.get())
    except ValueError:
        dg_set("Check the known mass", AMBER); return
    if known <= 0:
        dg_set("The known mass must be greater than zero", AMBER); return
    delta = v - _lc_zero["v"]
    if abs(delta) < 1e-6:
        dg_set("The raw reading did not change — is the mass actually on the cell?",
               RED); return
    lc_mode.set("point1")
    lc_cal["tare"] = _lc_zero["v"]
    lc_cal["scale"] = known / delta
    lc_cal["r2"] = None
    note = lc_drift_note(drift)
    dg_lc_commit(f"1-point: {known:.1f} g moved the raw value by {delta:.1f} → "
                 f"scale {lc_cal['scale']:.6g}. Every Kt scales by the same factor."
                 + note, AMBER if note else GREEN)


def dg_lc_add_point():
    """Record (known mass, raw reading) as one point of the multi-point fit."""
    v, drift, n = lc_raw_settled(2.0)
    if v is None:
        dg_set("No load-cell data (need ~2 s of samples)", RED); return
    try:
        known = float(dg_lc_known.get())
    except ValueError:
        dg_set("Check the known mass", AMBER); return
    lc_cal["points"].append((known, v))
    dg_lc_points_redraw()
    lc_cal_save()
    note = lc_drift_note(drift)
    dg_set(f"Point {len(lc_cal['points'])}: {known:.1f} g at raw {v:.1f}. "
           f"Add more masses, then Fit." + note +
           (" Add a 0 g point (empty cell) too — it is what pins the tare."
            if not any(abs(m) < 1e-9 for m, _ in lc_cal["points"]) else ""),
           AMBER if note else BLUE)


def dg_lc_fit():
    """Least squares through the points: slope is the scale, intercept the tare.

    This is the same argument the Kt logbook makes about dividing one point:
    the offset is real — resting preload, beam imbalance, amplifier zero — and
    dividing mass by reading folds that offset into the slope, worst at the
    lightest masses. Fitting the line estimates the offset instead of pretending
    it is zero."""
    pts = lc_cal["points"]
    if len(pts) < 2:
        dg_set("Need at least 2 points — and they should span the range you "
               "actually measure in", AMBER); return
    raws = [r for _, r in pts]; masses = [m for m, _ in pts]
    if max(raws) - min(raws) < 1e-6:
        dg_set("Every point has the same raw reading — nothing to fit", RED); return
    f = linfit(raws, masses)                    # grams = a·raw + b
    if f is None:
        dg_set("The points do not support a fit", RED); return
    a, b, r2 = f
    if abs(a) < 1e-12:
        dg_set("Fitted slope is zero — check the points", RED); return
    lc_mode.set("multi")
    lc_cal["scale"] = a
    lc_cal["tare"] = -b / a
    lc_cal["r2"] = r2
    dg_lc_points_redraw()
    resid = max(abs(m - (a * r + b)) for m, r in pts)
    warn = ""
    if r2 < 0.999:
        warn = ("  ⚠ r² is poor for a load cell — suspect a mass that moved, a "
                "point taken before the reading settled, or the cell being "
                "loaded off-axis.")
    dg_lc_commit(f"Fit of {len(pts)} points: scale {a:.6g} g/raw, tare {-b/a:.1f} raw, "
                 f"r² = {r2:.5f}, worst residual {resid:.2f} g." + warn,
                 AMBER if warn else GREEN)


def dg_lc_clear_points():
    if not confirm_reset(len(lc_cal["points"]), "calibration points"):
        return
    lc_cal["points"] = []
    lc_cal["r2"] = None
    dg_lc_points_redraw()
    lc_cal_save()
    dg_set("Calibration points cleared. Scale and tare are unchanged.", BLUE)


def dg_lc_drop_point():
    if lc_cal["points"]:
        lc_cal["points"].pop()
        dg_lc_points_redraw()
        lc_cal_save()
        dg_set(f"Removed the last point — {len(lc_cal['points'])} left.", BLUE)


cb = tk.Frame(dg_l, bg=SURFACE); cb.pack(fill="x", pady=(4, 0))
btn(cb, "Tare now", FIELD, MUTED, dg_lc_tare_now, width=9).pack(side="left", padx=(0, 5))
btn(cb, "Apply typed", FIELD, BLUE, dg_lc_apply_manual, width=11).pack(side="left", padx=(0, 5))
btn(cb, "Calibrate", FIELD, GREEN, dg_lc_calibrate, width=10).pack(side="left")

cb2 = tk.Frame(dg_l, bg=SURFACE); cb2.pack(fill="x", pady=(5, 0))
btn(cb2, "+ Add point", FIELD, BLUE, dg_lc_add_point, width=11).pack(side="left", padx=(0, 5))
btn(cb2, "Fit", FIELD, GREEN, dg_lc_fit, width=6).pack(side="left", padx=(0, 5))
btn(cb2, "↶", FIELD, MUTED, dg_lc_drop_point, width=3).pack(side="left", padx=(0, 5))
btn(cb2, "Clear", FIELD, RED, dg_lc_clear_points, width=7).pack(side="left")

dg_lc_table = mktable(dg_l, [("m", "known g", 78), ("r", "raw", 86),
                             ("f", "fit g", 72), ("e", "err g", 68)], height=6)


def dg_lc_points_redraw():
    clear_table(dg_lc_table)
    a = lc_cal["scale"]; t = lc_cal["tare"]
    for m, r in lc_cal["points"]:
        fitg = (r - t) * a
        dg_lc_table.insert("", "end", values=(f"{m:.1f}", f"{r:.1f}",
                                              f"{fitg:.1f}", f"{fitg - m:+.2f}"))


dg_lc_points_redraw()
tk.Label(dg_l, text="Saved to labdata/loadcell_cal.json and stamped as a\n"
                    "'#' comment line at the top of every run CSV, so a log\n"
                    "stays readable after the cell is re-calibrated.\n"
                    "pandas: read_csv(path, comment='#')",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(6, 0))

section(dg_l, "Bus-current check  ·  is Iq real?")
tk.Label(dg_l, text="The one link never measured independently: whether\nthe current in the WINDINGS equals the Iq we believe.\nStall the shaft, read DC bus amps off the PSU at 0 A\nand at a test current, and enter both. Copper loss is\n1.5·Iq²·R, so a 4x current error shows up as 16x in\npower — impossible to miss.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(0, 6))
dg_bus_iq = entry_row(dg_l, "Test Iq commanded (A)", 2.0)
dg_bus_idle = entry_row(dg_l, "Bus current, IDLE (A)", 0.15)
dg_bus_load = entry_row(dg_l, "Bus current, pushing (A)", 0.0)
dg_bus_v = entry_row(dg_l, "Bus voltage (V)", 24.0)
dg_bus_r = entry_row(dg_l, "Phase resistance (ohm)", 0.54)


def dg_bus_check():
    try:
        iq = float(dg_bus_iq.get()); i0 = float(dg_bus_idle.get())
        i1 = float(dg_bus_load.get()); vb = float(dg_bus_v.get())
        r = float(dg_bus_r.get())
    except ValueError:
        dg_set("Check the numbers", AMBER); return
    p = (i1 - i0) * vb
    if p <= 0:
        dg_set("Pushing current is not above idle — is the shaft stalled and current flowing?", RED)
        return
    # copper loss = 3 * I_rms^2 * R_phase = 1.5 * I_peak^2 * R_phase
    i_act = math.sqrt(p / (1.5 * r))
    ratio = i_act / iq if iq else 0
    txt = (f"{p:.2f} W of copper loss → real current ≈ {i_act:.2f} A "
           f"vs {iq:.2f} A believed  ({ratio:.2f}x)")
    if 0.7 < ratio < 1.4:
        dg_set(txt + "  — the current path is honest. The discrepancy is elsewhere "
                     "(KV convention, or the torque geometry).", GREEN)
    elif ratio < 0.7:
        dg_set(txt + "  — LESS current is flowing than reported: the sense scale reads "
                     "HIGH, so the loop under-drives. That is your missing torque.", RED)
    else:
        dg_set(txt + "  — MORE current is flowing than reported: the sense scale reads LOW.", RED)


btn(dg_l, "∑ Compute real current", FIELD, BLUE, dg_bus_check).pack(fill="x", pady=(4, 0))
dg_set = mkstatus(dg_l)

dg_m_o, dg_m = card(dg_fr); dg_m_o.pack(side="left", fill="both", expand=True, padx=(0, 14))
section(dg_m, "Serial console  ·  everything the firmware says")
dg_txt = tk.Text(dg_m, bg="#0f1419", fg="#c8d3e0", insertbackground="#c8d3e0",
                 font=("Consolas", 11), relief="flat", height=22, wrap="none")
dg_txt.pack(fill="both", expand=True)
dg_txt.tag_config("tx", foreground="#7dd3fc")
dg_txt.tag_config("rx", foreground="#c8d3e0")
dg_txt.tag_config("err", foreground="#fca5a5")
dg_txt.tag_config("sys", foreground="#fcd34d")
dg_n = [0]


def dg_console_tick():
    with console_lock:
        n = console_seq[0]
        if n != dg_n[0]:
            rows = list(console)
            dg_n[0] = n
        else:
            rows = None
    if rows is not None:
        dg_txt.config(state="normal")
        dg_txt.delete("1.0", "end")
        for ts, kind, text in rows:
            dg_txt.insert("end", f"{ts} {'>' if kind == 'tx' else ' '} {text}\n", kind)
        dg_txt.see("end")
        dg_txt.config(state="disabled")


cmd_row = tk.Frame(dg_m, bg=SURFACE); cmd_row.pack(fill="x", pady=(8, 0))
tk.Label(cmd_row, text="send:", bg=SURFACE, fg=MUTED, font=F_LBL).pack(side="left", padx=(0, 8))
dg_cmd = tk.Entry(cmd_row, bg=FIELD, fg=TEXT, insertbackground=TEXT, relief="flat",
                  font=("Consolas", 13), highlightthickness=1,
                  highlightbackground=BORDER, highlightcolor=BLUE)
dg_cmd.pack(side="left", fill="x", expand=True, ipady=4)


def dg_send_cmd(_e=None):
    c = dg_cmd.get().strip()
    if c:
        dev_send(c)
        dg_cmd.delete(0, "end")


dg_cmd.bind("<Return>", dg_send_cmd)
tk.Button(cmd_row, text="Send", command=dg_send_cmd, bg=FIELD, fg=BLUE,
          relief="flat", bd=0, font=("Segoe UI", 11, "bold"), padx=12, pady=4,
          cursor="hand2", highlightthickness=0).pack(side="left", padx=(8, 0))
tk.Label(dg_m, text="e.g.  L   Z   C0.5   O0   Pi4   Ps-1   Pv20   Pm2   Pt0   MMS0001001   MMD10",
         bg=SURFACE, fg=FAINT, font=F_SM).pack(anchor="w", pady=(4, 0))

dg_r_o, dg_r = card(dg_fr); dg_r_o.pack(side="left", fill="y")
section(dg_r, "Live · commanded vs measured")
dg_iqc = big_value(dg_r, "Iq COMMANDED (A)", AMBER)
dg_iqm = big_value(dg_r, "Iq MEASURED (A)", BLUE)
dg_verdict = tk.Label(dg_r, text="", bg=SURFACE, fg=MUTED, font=F_LBL,
                      wraplength=280, justify="left")
dg_verdict.pack(pady=(10, 0))
dg_extra = tk.Label(dg_r, text="", bg=SURFACE, fg=FAINT, font=("Consolas", 12),
                    justify="left")
dg_extra.pack(anchor="w", pady=(10, 0))
add_tab("0 · Diagnostics", dg_fr)


def dg_tick():
    # [g3-B] Only MANUAL mode lets the entry boxes drive the calibration. In
    # 1-point and multi-point the computed result is the truth and the boxes
    # are a readout — otherwise this tick would overwrite a fresh fit 200 ms
    # after it was made, with whatever text was left in the entry.
    if lc_mode.get() == "manual":
        try:
            lc_cal["scale"] = float(dg_lc_scale.get())
            lc_cal["tare"] = float(dg_lc_tare.get())
        except (ValueError, tk.TclError):
            pass
    _rawv = lc_raw_latest(1.0)
    _g = lc_latest(1.0)
    if _rawv is None:
        dg_lc_live.config(text="raw   --        →     --  g", fg=FAINT)
    else:
        _r2 = "" if lc_cal["r2"] is None else f"   r²={lc_cal['r2']:.4f}"
        dg_lc_live.config(
            text=f"raw {_rawv:9.1f}   →  {(_g if _g is not None else 0.0):8.1f} g"
                 f"   [{lc_mode.get()}]{_r2}", fg=MUTED)
    fl = T["flags"]
    idle = (T["state"] == 0)
    for i, (bit, _n) in enumerate(FLAG_BITS):
        if fl < 0:
            dg_flag_lbls[i].config(fg=FAINT)          # old 7-field firmware
        elif bit in (0x02, 0x04) and idle:
            # "motor enabled" and "driver powered" are SUPPOSED to be off in
            # IDLE — that is the true-freewheel design, not a fault. Grey, not
            # red, so a limp shaft never looks like a broken board.
            dg_flag_lbls[i].config(fg=FAINT)
        elif bit == 0x20 and not (fl & bit):
            # [g3-A] AMBER, not red: no thermistor fitted is a perfectly valid
            # way to run a KV or Kt test. It is only a fault for the thermal
            # tabs, and they say so themselves rather than colouring the whole
            # board broken.
            dg_flag_lbls[i].config(fg=AMBER)
        else:
            dg_flag_lbls[i].config(fg=GREEN if (fl & bit) else RED)
    dg_fw.config(text=f"firmware: {link['fw'] or '—'}   ({T['nfields']} telemetry fields)")
    dg_iqc.config(text=f"{T['iqc']:+.3f}")
    dg_iqm.config(text=f"{T['iq']:+.3f}")
    # the actual diagnosis, spelled out
    if not dev_alive():
        dg_verdict.config(text="No telemetry. Connect the driver port, or send D20.", fg=RED)
    elif fl >= 0 and not (fl & 0x01):
        dg_verdict.config(text="initFOC FAILED. The motor physically cannot move: check the AS5047P magnet, pole pairs and bus power.", fg=RED)
    elif fl >= 0 and not (fl & 0x10):
        dg_verdict.config(text="Vbus reading is out of range — phase voltage may be capped at 0. Set it with Pu24.", fg=RED)
    elif idle:
        dg_verdict.config(text="IDLE — bridge is open, shaft is free. Current reads exactly 0 by design; "
                               "sensing cannot be judged until a mode is entered. Jog to test.", fg=MUTED)
    elif abs(T["iqc"]) < 0.05:
        dg_verdict.config(text="Firmware is commanding ~0 A. Nothing is wrong with sensing yet — send a current (jog) first.", fg=MUTED)
    elif abs(T["iq"]) < 0.25 * abs(T["iqc"]):
        dg_verdict.config(text="Current is COMMANDED but not MEASURED. Shunt/ADC path or torque mode: try Pm1, check Pq, check M0_IB/M0_IC wiring.", fg=RED)
    elif abs(T["idq"]) > 0.5 * abs(T["iq"]) and abs(T["iq"]) > 0.2:
        # id should sit near zero: all current on the q axis is what makes
        # torque proportional to Iq. A large id means the dq frame is rotated
        # away from the rotor, so Kt per amp is neither constant nor correct.
        dg_verdict.config(text=f"|id| = {abs(T['idq']):.2f} A is large next to |iq| = {abs(T['iq']):.2f} A. "
                               "The commutation angle is off, so torque will NOT scale with current. "
                               "Suspect the current-sense phase mapping (skip_align) or the sensor zero angle.", fg=RED)
    else:
        dg_verdict.config(text="Command and measurement agree, id is small. If there is still no force, the push DIRECTION is wrong — flip Ps.", fg=GREEN)
    g = lc_latest(1.0)
    _tc = temp_now(2.0)
    dg_extra.config(text=(f"state    {STATE_NAMES.get(T['state'], '?')}\n"
                          f"angle    {math.degrees(T['ang']):+8.1f} deg\n"
                          f"velocity {T['vel']:+8.2f} rad/s\n"
                          f"id meas  {T['idq']:+8.3f} A\n"
                          f"voltage q{T['vq']:+8.3f} V\n"
                          f"loadcell {'--' if g is None else f'{g:8.1f} g'}\n"
                          f"temp     {'--' if _tc is None else f'{_tc:8.1f} C'}   ({temp_label()})"))


# ═════════════ TAB 1 · PHASE RESISTANCE ═══════════════════════
# Manual entry from a 4-wire Kelvin measurement (Fluke 289, low-ohm + REL).
# Nothing here talks to the driver: the point is a reference measurement that
# does NOT go through the motor controller, so it can be trusted when the
# controller itself is under suspicion.
r_fr = tk.Frame(body, bg=BG)
rs = dict(rows=[], res={})
PAIRS = ("AB", "AC", "BC")

r_sc_o, r_sc = scroll_column(r_fr); r_sc_o.pack(side="left", fill="y", padx=(0, 14))
r_l_o, r_l = card(r_sc); r_l_o.pack(fill="both", expand=True)
section(r_l, "Winding termination")
term_var = tk.StringVar(value="star")
tf_ = tk.Frame(r_l, bg=SURFACE); tf_.pack(fill="x", pady=(0, 4))
for _t, _v in (("Star (Y)", "star"), ("Delta (Δ)", "delta")):
    tk.Radiobutton(tf_, text=_t, variable=term_var, value=_v, bg=SURFACE, fg=TEXT,
                   selectcolor=FIELD, font=F_LBL, activebackground=SURFACE,
                   highlightthickness=0, command=lambda: r_compute()).pack(side="left", padx=(0, 16))
tk.Label(r_l, text="Star:  R_LL = 2·R_phase   →   R_phase = R_LL / 2\n"
                   "Delta: R_LL = R_ph ∥ 2R_ph = ⅔·R_ph   →   R_phase = 1.5·R_LL",
         bg=SURFACE, fg=FAINT, font=("Consolas", 11), justify="left").pack(anchor="w", pady=(0, 8))

section(r_l, "Measured phase-to-phase (Ω) · 4-wire Kelvin")
tk.Label(r_l, text="Fluke 289, low-ohm range, REL to null the leads.\nThree readings per pair — reseat the clips between\nreadings so contact resistance shows up as scatter.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(0, 6))

grid = tk.Frame(r_l, bg=SURFACE); grid.pack(fill="x")
tk.Label(grid, text="", bg=SURFACE, width=5).grid(row=0, column=0)
for c in range(3):
    tk.Label(grid, text=f"#{c+1}", bg=SURFACE, fg=MUTED, font=F_SM).grid(row=0, column=c + 1, padx=3)
r_entries = {}
for rix, pair in enumerate(PAIRS):
    tk.Label(grid, text=pair, bg=SURFACE, fg=TEXT, font=F_LBL, width=5,
             anchor="w").grid(row=rix + 1, column=0, pady=2)
    for c in range(3):
        e = tk.Entry(grid, bg=FIELD, fg=BLUE, insertbackground=TEXT, relief="flat",
                     font=("Consolas", 13, "bold"), width=9, justify="center",
                     highlightthickness=1, highlightbackground=BORDER, highlightcolor=BLUE)
        e.grid(row=rix + 1, column=c + 1, padx=3, pady=2, ipady=2)
        e.bind("<KeyRelease>", lambda _e: r_compute())
        r_entries[(pair, c)] = e

r_temp = entry_row(r_l, "Winding temperature (°C)", 25.0)
r_kt = entry_row(r_l, "Kt for Km (mN·m/A, optional)", 86.8)

rb = tk.Frame(r_l, bg=SURFACE); rb.pack(fill="x", pady=(8, 2))
btn(rb, "∑ Compute", FIELD, BLUE, lambda: r_compute(), width=10).pack(side="left", padx=(0, 6))
btn(rb, "⤓ Save CSV", FIELD, GREEN, lambda: r_save(), width=10).pack(side="left")


def r_clear():
    n = sum(1 for e in r_entries.values() if e.get().strip())
    if not confirm_reset(n, "readings"):
        return
    for e in r_entries.values():
        e.delete(0, "end")
    r_compute()
    r_set("Data reset — enter readings again", BLUE)


btn(r_l, "↺ Reset data", FIELD, RED, r_clear).pack(fill="x", pady=(6, 0))
r_set = mkstatus(r_l)

r_r_sc_o, r_r_sc = scroll_column(r_fr); r_r_sc_o.pack(side="left", fill="y")
r_r_o, r_r = card(r_r_sc); r_r_o.pack(fill="both", expand=True)
section(r_r, "Per pair")
r_table = mktable(r_r, [("p", "pair", 70), ("m", "mean Ω", 100),
                        ("s", "std Ω", 90), ("d", "vs mean", 90)], height=4)
section(r_r, "Result")
rr = tk.Frame(r_r, bg=SURFACE); rr.pack()
rc1 = tk.Frame(rr, bg=SURFACE); rc1.pack(side="left", padx=12)
r_lbl_ph = tk.Label(rc1, text="—", bg=SURFACE, fg=GREEN, font=("Consolas", 28, "bold"))
r_lbl_ph.pack(); tk.Label(rc1, text="R_phase [Ω]", bg=SURFACE, fg=FAINT, font=F_SM).pack()
rc2 = tk.Frame(rr, bg=SURFACE); rc2.pack(side="left", padx=12)
r_lbl_km = tk.Label(rc2, text="—", bg=SURFACE, fg=GREEN, font=("Consolas", 28, "bold"))
r_lbl_km.pack(); tk.Label(rc2, text="Km [mN·m/√W]", bg=SURFACE, fg=FAINT, font=F_SM).pack()
r_lbl_note = tk.Label(r_r, text="enter at least one pair", bg=SURFACE, fg=FAINT,
                      font=F_LBL, wraplength=330, justify="left")
r_lbl_note.pack(pady=(8, 0))
section(r_r, "Balance across pairs")
r_cv = tk.Canvas(r_r, width=340, height=190, bg=SURFACE, highlightthickness=0)
r_cv.pack(fill="x", pady=(0, 4))


def r_pair_stats():
    out = {}
    for pair in PAIRS:
        vals = []
        for c in range(3):
            t = r_entries[(pair, c)].get().strip()
            if t:
                try:
                    vals.append(float(t))
                except ValueError:
                    pass
        if vals:
            m = sum(vals) / len(vals)
            sd = (sum((x - m) ** 2 for x in vals) / len(vals)) ** 0.5
            out[pair] = (m, sd, len(vals))
    return out


def r_compute():
    st = r_pair_stats()
    for it in r_table.get_children():
        r_table.delete(it)
    means = [st[p][0] if p in st else None for p in PAIRS]
    have = [m for m in means if m is not None]
    draw_bars(r_cv, list(PAIRS), means, ylabel="phase-to-phase Ω", warn_at=2.0)
    if not have:
        r_lbl_ph.config(text="—"); r_lbl_km.config(text="—")
        r_lbl_note.config(text="enter at least one pair", fg=FAINT)
        return
    grand = sum(have) / len(have)
    for p in PAIRS:
        if p in st:
            m, sd, n = st[p]
            r_table.insert("", "end", values=(p, f"{m:.4f}", f"{sd:.4f}",
                                              f"{(m-grand)/grand*100:+.2f}%"))
    r_ll = grand
    star = term_var.get() == "star"
    r_phase = r_ll / 2.0 if star else 1.5 * r_ll
    rs["res"] = dict(r_ll=r_ll, r_phase=r_phase, term=term_var.get())
    r_lbl_ph.config(text=f"{r_phase:.4f}")
    try:
        kt = float(r_kt.get()) * 1e-3
        km = kt / math.sqrt(r_phase) if r_phase > 0 else None
        r_lbl_km.config(text=f"{km*1000:.1f}" if km else "—")
        rs["res"]["km"] = km
    except (ValueError, ZeroDivisionError):
        r_lbl_km.config(text="—")
    spread = (max(have) - min(have)) / grand * 100 if len(have) > 1 and grand else 0.0
    rs["res"]["imbalance_pct"] = spread
    note = (f"R_LL mean {r_ll:.4f} Ω · {'star' if star else 'delta'} → "
            f"R_phase {r_phase:.4f} Ω · imbalance {spread:.2f}%")
    if len(have) < 3:
        r_lbl_note.config(text=note + "  · enter all three pairs to judge balance", fg=MUTED)
    elif spread > 2.0:
        # This is the check that would have caught the dead motor immediately.
        r_lbl_note.config(text=note + "  · IMBALANCE > 2% — the three pairs should be "
                                      "identical. Suspect a shorted or open winding, or a "
                                      "bad joint. Re-seat the clips and re-measure before "
                                      "trusting any Kt from this motor.", fg=RED)
    else:
        r_lbl_note.config(text=note + "  · pairs balanced", fg=GREEN)


def r_save():
    st = r_pair_stats()
    if not st:
        r_set("Nothing to save", AMBER); return
    path = log_path("phase-resistance")
    if not path:
        r_set("Enter the motor serial number first", RED); return
    r_compute()
    res = rs.get("res", {})
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["pair", "r1_ohm", "r2_ohm", "r3_ohm", "mean_ohm", "std_ohm"])
        for p in PAIRS:
            vals = [r_entries[(p, c)].get().strip() for c in range(3)]
            if p in st:
                m, sd, _ = st[p]
                w.writerow([p] + vals + [f"{m:.5f}", f"{sd:.5f}"])
        w.writerow([])
        w.writerow(["termination", res.get("term", "")])
        w.writerow(["r_line_to_line_ohm", f"{res.get('r_ll', 0):.5f}"])
        w.writerow(["r_phase_ohm", f"{res.get('r_phase', 0):.5f}"])
        w.writerow(["imbalance_pct", f"{res.get('imbalance_pct', 0):.3f}"])
        w.writerow(["winding_temp_C", r_temp.get().strip()])
        w.writerow(["kt_mNm_per_A", r_kt.get().strip()])
        if res.get("km"):
            w.writerow(["km_mNm_per_sqrtW", f"{res['km']*1000:.4f}"])
        w.writerow(["method", "4-wire Kelvin, Fluke 289 low-ohm + REL, 3 readings per pair"])
    r_set(f"Saved → {path}", GREEN)


add_tab("1 · Phase R", r_fr)
r_compute()

# ═════════════ TAB 1 · KV back-EMF ═════════════════════════════
kv_fr = tk.Frame(body, bg=BG)
kv = dict(steps=[], idx=0, spinning=False, points=[])

# How the back-EMF voltage was measured decides the Kt conversion, and getting
# it wrong is a silent factor-of-2 class error. For a sinusoidal PMSM with
# lambda = flux linkage per phase (peak), p = pole pairs:
#     phase peak  E = lambda*p*w        torque tau = 1.5*p*lambda*iq
#     phase rms   E = lambda*p*w/sqrt2
#     line-line   E = sqrt3 * phase
# so with k = V per (rad/s mech) = 9.5493/KV, Kt = C*k with C as below.
# The familiar "8.27/KV" shorthand is the line-to-line PEAK case; a multimeter
# on AC volts across two leads gives line-to-line RMS, which is 11.70/KV.
BEMF_KINDS = {
    "ll_rms": ("line-to-line, RMS  (multimeter AC volts)", 1.5 * math.sqrt(2.0 / 3.0)),
    "ll_pk":  ("line-to-line, peak (scope)", 1.5 / math.sqrt(3.0)),
    "ph_rms": ("phase-to-neutral, RMS", 1.5 * math.sqrt(2.0)),
    "ph_pk":  ("phase-to-neutral, peak", 1.5),
}

kv_sc_o, kv_sc = scroll_column(kv_fr); kv_sc_o.pack(side="left", fill="y", padx=(0, 14))
kv_l_o, kv_l = card(kv_sc); kv_l_o.pack(fill="both", expand=True)
section(kv_l, "Test setup · DUT terminals OPEN")
kv_start = entry_row(kv_l, "Start speed (DUT rpm)", 300)
kv_end = entry_row(kv_l, "End speed (DUT rpm)", 1500)
kv_n = entry_row(kv_l, "Number of steps", 6)
kv_ratio = entry_row(kv_l, "Coupling ratio (DUT/drive)", 1.0)
kv_win = entry_row(kv_l, "Speed averaging window (s)", 3.0)
section(kv_l, "What the meter measures")
kv_kind = tk.StringVar(value="ll_rms")
for _k, (_lab, _c) in BEMF_KINDS.items():
    tk.Radiobutton(kv_l, text=f"{_lab}   →  Kt = {_c*9.5493:.2f}/KV",
                   variable=kv_kind, value=_k, bg=SURFACE, fg=TEXT,
                   selectcolor=FIELD, font=F_SM, activebackground=SURFACE,
                   highlightthickness=0, anchor="w",
                   command=lambda: kv_fit()).pack(anchor="w")
tk.Label(kv_l, text="KV itself is just 1/slope and does not depend on this;\n"
                    "Kt does, by up to 2.4x across these four conventions.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(2, 6))


def kv_build():
    try:
        lo = float(kv_start.get()); hi = float(kv_end.get()); n = max(2, int(kv_n.get()))
    except ValueError:
        kv_set("Check the numbers", AMBER); return
    kv["steps"] = [lo + (hi - lo) * i / (n - 1) for i in range(n)]
    kv["idx"] = 0; kv_step_ui()
    kv_set(f"{n} steps ready", GREEN)


btn(kv_l, "⚙  Build steps", FIELD, BLUE, kv_build).pack(pady=(6, 12), fill="x")
section(kv_l, "Step control")
sc = tk.Frame(kv_l, bg=SURFACE); sc.pack()


def kv_ratio_v():
    try:
        return max(0.01, float(kv_ratio.get()))
    except ValueError:
        return 1.0


def kv_send():
    dut = kv["steps"][kv["idx"]]
    dev_send(f"V{dut / kv_ratio_v() * 2 * math.pi / 60:.2f}")
    kv_set(f"Step {kv['idx']+1}/{len(kv['steps'])}: {dut:.0f} rpm", BLUE)


def kv_move(d):
    if not kv["steps"]:
        return
    kv["idx"] = max(0, min(len(kv["steps"]) - 1, kv["idx"] + d))
    kv_step_ui()
    if kv["spinning"]:
        kv_send()


def kv_spin():
    if not kv["steps"]:
        kv_build()
    kv["spinning"] = True; kv_send()


def kv_stop():
    kv["spinning"] = False; dev_send("V0"); stop_all()
    kv_set("Stopped — shaft released", RED)


btn(sc, "◀", FIELD, TEXT, lambda: kv_move(-1), width=3).pack(side="left", padx=3)
kv_lbl_step = tk.Label(sc, text="—", bg=SURFACE, fg=TEXT, font=("Segoe UI", 16, "bold"), width=7)
kv_lbl_step.pack(side="left")
btn(sc, "▶", FIELD, TEXT, lambda: kv_move(+1), width=3).pack(side="left", padx=3)
kv_lbl_target = tk.Label(kv_l, text="—", bg=SURFACE, fg=AMBER, font=("Consolas", 28, "bold"))
kv_lbl_target.pack(pady=(6, 0))
tk.Label(kv_l, text="target rpm (DUT)", bg=SURFACE, fg=FAINT, font=F_SM).pack()


def kv_step_ui():
    kv_lbl_step.config(text=f"{kv['idx']+1} / {len(kv['steps'])}" if kv["steps"] else "—")
    kv_lbl_target.config(text=f"{kv['steps'][kv['idx']]:.0f}" if kv["steps"] else "—")


bb = tk.Frame(kv_l, bg=SURFACE); bb.pack(pady=(10, 2))
btn(bb, "▶ SPIN", GREEN, "white", kv_spin, width=8).pack(side="left", padx=(0, 6))
btn(bb, "■ STOP", RED, "white", kv_stop, width=8).pack(side="left")

section(kv_l, "Velocity-loop tuning")
tk.Label(kv_l, text="If the speed hunts or wanders, it is this loop —\nSimpleFOC's defaults are generic, and a coupled DUT\nadds cogging as a periodic load torque. Lower P and\nraise the filter to trade response for steadiness;\nfor KV only steadiness matters.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(0, 6))
kv_vp = entry_row(kv_l, "Velocity P", 0.20)
kv_vi = entry_row(kv_l, "Velocity I", 5.0)
kv_vf = entry_row(kv_l, "Velocity LPF Tf (s)", 0.020)


def kv_apply_pid():
    """Sent through the SimpleFOC Commander motor passthrough:
    MVP/MVI set the velocity PID gains, MVF its input filter."""
    try:
        p = float(kv_vp.get()); i = float(kv_vi.get()); f = float(kv_vf.get())
    except ValueError:
        kv_set("Check the numbers", AMBER); return
    dev_send(f"MVP{p:.4f}")
    dev_send(f"MVI{i:.4f}")
    dev_send(f"MVF{f:.4f}")
    kv_set(f"Sent P={p} I={i} Tf={f}s — re-run the step and watch the drift.", GREEN)


btn(kv_l, "⚙ Apply velocity gains", FIELD, BLUE, kv_apply_pid).pack(fill="x", pady=(4, 0))
kv_set = mkstatus(kv_l)

kv_m_o, kv_m = card(kv_fr); kv_m_o.pack(side="left", fill="both", expand=True, padx=(0, 14))
section(kv_m, "Live speed")
kv_rpm = big_value(kv_m, "DUT rpm (measured)")
kv_steady = tk.Label(kv_m, text="", bg=SURFACE, fg=FAINT, font=("Segoe UI", 14, "bold"))
kv_steady.pack(pady=(4, 8))
kv_chart = tk.Canvas(kv_m, width=560, height=240, bg=SURFACE, highlightthickness=0)
kv_chart.pack(pady=4, fill="x")

kv_rsc_o, kv_rsc = scroll_column(kv_fr); kv_rsc_o.pack(side="left", fill="y")
kv_r_o, kv_r = card(kv_rsc); kv_r_o.pack(fill="both", expand=True)
section(kv_r, "Log a point · back-EMF from multimeter")
pf = tk.Frame(kv_r, bg=SURFACE); pf.pack(fill="x", pady=(0, 6))
tk.Label(pf, text="Phase pair measured:", bg=SURFACE, fg=TEXT, font=F_LBL).pack(side="left")
kv_pair_var = tk.StringVar(value="AB")
for _p in ("AB", "AC", "BC"):
    tk.Radiobutton(pf, text=_p, variable=kv_pair_var, value=_p, bg=SURFACE, fg=TEXT,
                   selectcolor=FIELD, font=F_LBL, activebackground=SURFACE,
                   highlightthickness=0).pack(side="left", padx=(8, 0))

vf = tk.Frame(kv_r, bg=SURFACE); vf.pack(fill="x")
kv_volt = tk.Entry(vf, bg=FIELD, fg=AMBER, insertbackground=TEXT, relief="flat",
                   font=("Consolas", 18, "bold"), width=8, justify="center",
                   highlightthickness=1, highlightbackground=BORDER, highlightcolor=BLUE)
kv_volt.pack(side="left", ipady=5)
tk.Label(vf, text="V", bg=SURFACE, fg=MUTED, font=F_LBL).pack(side="left", padx=(6, 10))


def kv_steady_rpm(window=None):
    """Speed MAGNITUDE and its drift, from shaft angle. See kv_speed().

    Magnitude because spinning CCW gives negative rpm, and V = a*n + b would
    then fit a NEGATIVE slope that kv_fit() rejects as "bad slope" — a good
    CCW run made unusable by a sign convention. KV is defined on back-EMF
    magnitude."""
    if window is None:
        try:
            window = max(0.5, float(kv_win.get()))
        except (ValueError, tk.TclError):
            window = 3.0
    m, spread = kv_speed(window)
    return (None, None) if m is None else (abs(m), spread)


def kv_log():
    try:
        v = float(kv_volt.get())
    except ValueError:
        kv_set("Type the voltage first", AMBER); return
    m, spread = kv_steady_rpm()
    if m is None:
        kv_set("No telemetry yet", AMBER); return
    dut = m * kv_ratio_v()
    dr = (spread or 0.0) * kv_ratio_v()
    tgt = kv["steps"][kv["idx"]] if kv["steps"] else dut
    pair = kv_pair_var.get()
    kv["points"].append((tgt, dut, v, dr, pair))
    kv_table.insert("", "end", values=(pair, f"{tgt:.0f}", f"{dut:.0f}",
                                       f"{v:.3f}", f"±{dr:.1f}"))
    kv_volt.delete(0, "end"); kv_fit()
    # the meter reading and the speed must describe the SAME interval; a point
    # logged while the speed was still moving pairs a voltage with a speed the
    # motor was not actually holding
    if dr > max(2.0, 0.01 * abs(dut)):
        kv_set(f"Logged, but the speed drifted {dr:.1f} rpm over the window — "
               f"this point pairs a meter reading with a speed that was still moving.", AMBER)
    else:
        kv_set(f"Logged at {dut:.0f} rpm (drift {dr:.1f} rpm)", GREEN)


def kv_undo():
    if kv["points"]:
        kv["points"].pop(); kv_table.delete(kv_table.get_children()[-1]); kv_fit()


btn(vf, "+ Log point", BLUE, "white", kv_log).pack(side="left")
kv_volt.bind("<Return>", lambda e: kv_log())
kv_table = mktable(kv_r, [("ph", "phase", 60), ("t", "target rpm", 85),
                          ("m", "meas rpm", 95), ("v", "back-EMF V", 90),
                          ("d", "drift", 65)])
kb = tk.Frame(kv_r, bg=SURFACE); kb.pack(pady=(0, 10))


def kv_export():
    if not kv["points"]:
        kv_set("Nothing to save", AMBER); return
    path = log_path("kv-backemf")
    if not path:
        kv_set("Enter the motor serial number first", RED); return
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["phase_pair", "target_rpm", "measured_rpm", "backemf_V",
                    "speed_drift_rpm"])
        for r in kv["points"]:
            w.writerow([r[4], f"{r[0]:.1f}", f"{r[1]:.1f}", f"{r[2]:.4f}", f"{r[3]:.2f}"])
        w.writerow([])
        w.writerow(["kv_rpm_per_V", kv_res.get("kv", "")])
        w.writerow(["bemf_measurement", BEMF_KINDS[kv_kind.get()][0]])
        w.writerow(["kt_mNm_per_A", kv_res.get("kt", "")])
        w.writerow(["kt_formula", f"{BEMF_KINDS[kv_kind.get()][1]*9.5493:.4f}/KV"])
    kv_set(f"Saved → {path}", GREEN)


def kv_reset():
    if not confirm_reset(len(kv["points"]), "logged points"):
        return
    kv["points"].clear()
    clear_table(kv_table)
    kv_fit()
    kv_set("Data reset — table and fit cleared", BLUE)


btn(kb, "⌫ Undo", FIELD, MUTED, kv_undo).pack(side="left", padx=(0, 6))
btn(kb, "↺ Reset", FIELD, RED, kv_reset).pack(side="left", padx=(0, 6))
btn(kb, "⤓ Save CSV", FIELD, GREEN, kv_export).pack(side="left")
section(kv_r, "Result · V = a·n + b → KV = 1/a")
rf = tk.Frame(kv_r, bg=SURFACE); rf.pack()
c1 = tk.Frame(rf, bg=SURFACE); c1.pack(side="left", padx=14)
kv_lbl_kv = tk.Label(c1, text="—", bg=SURFACE, fg=GREEN, font=("Consolas", 30, "bold"))
kv_lbl_kv.pack(); tk.Label(c1, text="KV [rpm/V]", bg=SURFACE, fg=FAINT, font=F_SM).pack()
c2 = tk.Frame(rf, bg=SURFACE); c2.pack(side="left", padx=14)
kv_lbl_kt = tk.Label(c2, text="—", bg=SURFACE, fg=GREEN, font=("Consolas", 30, "bold"))
kv_lbl_kt.pack(); tk.Label(c2, text="Kt [mNm/A]", bg=SURFACE, fg=FAINT, font=F_SM).pack()
kv_lbl_r2 = tk.Label(kv_r, text="log ≥ 2 points", bg=SURFACE, fg=FAINT, font=F_LBL)
kv_lbl_r2.pack(pady=(8, 0))
section(kv_r, "V = a·n + b")
kv_scatter = tk.Canvas(kv_r, width=340, height=200, bg=SURFACE, highlightthickness=0)
kv_scatter.pack(fill="x", pady=(0, 4))
kv_res = {}


def kv_fit():
    xs = [p[1] for p in kv["points"]]; ys = [p[2] for p in kv["points"]]
    if len(kv["points"]) < 2:
        kv_lbl_kv.config(text="—"); kv_lbl_kt.config(text="—")
        kv_lbl_r2.config(text="log ≥ 2 points")
        draw_scatter(kv_scatter, xs, ys, None, "measured rpm", "back-EMF V")
        return
    fit = linfit(xs, ys)
    draw_scatter(kv_scatter, xs, ys, fit, "measured rpm", "back-EMF V")
    if fit is None or fit[0] <= 1e-9:
        kv_lbl_r2.config(text="bad slope — check points"); return
    a, b, r2 = fit
    kvv = 1.0 / a
    C = BEMF_KINDS[kv_kind.get()][1]
    kt = C * 9.5493 / kvv                      # N·m/A, dq (peak-phase) current
    kv_res["kv"] = f"{kvv:.2f}"
    kv_res["kt"] = f"{kt*1000:.2f}"
    kv_res["kind"] = kv_kind.get()
    kv_lbl_kv.config(text=f"{kvv:.1f}")
    kv_lbl_kt.config(text=f"{kt*1000:.1f}")
    txt = f"R² = {r2:.4f} · offset {b*1000:+.0f} mV · {len(kv['points'])} pts"
    # per-pair breakdown: the three should agree, exactly as for resistance
    pairs = {}
    for p in kv["points"]:
        pairs.setdefault(p[4], []).append(p)
    if len(pairs) > 1:
        per = {}
        for name, pts in pairs.items():
            if len(pts) >= 2:
                f2 = linfit([q[1] for q in pts], [q[2] for q in pts])
                if f2 and f2[0] > 1e-9:
                    per[name] = 1.0 / f2[0]
        if len(per) > 1:
            spread = (max(per.values()) - min(per.values())) / (sum(per.values()) / len(per)) * 100
            txt += "  ·  " + " ".join(f"{k}:{v:.1f}" for k, v in sorted(per.items()))
            txt += f" ({spread:.1f}% spread)"
            if spread > 3.0:
                txt += " ⚠ pairs disagree — check the winding"
    # a large intercept means the fit is not passing through the origin, which
    # a back-EMF line physically must
    if abs(b) > 0.25:
        txt += f"  ⚠ offset {b*1000:+.0f} mV is large for a back-EMF line"
    kv_lbl_r2.config(text=txt)


add_tab("2 · KV · Back-EMF", kv_fr)

# ═════════════ TAB 2 · KT add-weight ═══════════════════════════
w_fr = tk.Frame(body, bg=BG)
wt = dict(rows=[], holding=False, ang0=0.0, ang0_set=False)

w_sc_o, w_sc = scroll_column(w_fr); w_sc_o.pack(side="left", fill="y", padx=(0, 14))
w_l_o, w_l = card(w_sc); w_l_o.pack(fill="both", expand=True)
section(w_l, "Setup · rotate arm HORIZONTAL first (shaft is free in IDLE)")
w_len = entry_row(w_l, "Arm length L to weights (m)", 0.10)
w_arm = entry_row(w_l, "Arm effective weight at tip (g)", 25.0)
tk.Label(w_l, text="= the mass which, placed AT RADIUS L, makes the same\n"
                   "gravity torque as the real arm:  m_eff = Σ(mᵢ·rᵢ) / L.\n"
                   "A uniform bar contributes HALF its mass (CoM at L/2);\n"
                   "a hook or pan at the tip counts in full.\n"
                   "It shifts the friction intercept, NOT Kt — the slope is\n"
                   "immune to any constant torque. Measure it if you want the\n"
                   "intercept to mean friction+cogging; otherwise leave it.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(0, 4))
_arm_zero = {"v": None}


def w_arm_lc_zero():
    """Step 1: nothing on the cell."""
    v = lc_latest(1.0)
    if v is None:
        w_set("No load-cell data — connect it first", RED); return
    _arm_zero["v"] = v
    w_set(f"Zero {v:.1f} g. Now rest the arm HORIZONTALLY on the cell, "
          f"contacting at exactly radius L, motor in IDLE.", BLUE)


def w_arm_lc_capture():
    """Step 2: arm resting on the cell at radius L.

    Supporting the arm at radius L with the pivot at the shaft makes the
    scale force times L equal the arm's gravity torque — which is the
    definition of the effective tip mass. So the cell reads m_eff directly,
    with no need to find the centre of mass or weigh anything separately."""
    if _arm_zero["v"] is None:
        w_set("Press Zero first, with nothing on the cell", AMBER); return
    v = lc_latest(1.0)
    if v is None:
        w_set("No load-cell data", RED); return
    m_eff = v - _arm_zero["v"]
    if m_eff <= 0:
        w_set(f"Reading went the wrong way ({m_eff:+.1f} g) — is the arm "
              f"resting ON the cell?", RED); return
    w_arm.delete(0, "end"); w_arm.insert(0, f"{m_eff:.1f}")
    w_set(f"Arm effective weight = {m_eff:.1f} g (measured at radius L)", GREEN)


_ab = tk.Frame(w_l, bg=SURFACE); _ab.pack(fill="x", pady=(0, 6))
tk.Label(_ab, text="from load cell:", bg=SURFACE, fg=MUTED, font=F_SM).pack(side="left", padx=(0, 6))
btn(_ab, "Zero", FIELD, MUTED, w_arm_lc_zero, width=5).pack(side="left", padx=(0, 4))
btn(_ab, "Capture", FIELD, GREEN, w_arm_lc_capture, width=8).pack(side="left")
w_iqmx = entry_row(w_l, "Max Iq protection (A)", 4.0)


def w_hold():
    # Capture the HORIZONTAL reference BEFORE energising: in IDLE the shaft is
    # free and the arm is sitting where you placed it, so this angle is the
    # true horizontal. Every later sag is measured against it.
    #
    # But only ONCE per data set. Pressing HOLD again part-way through a run —
    # after the arm has already sagged — would re-zero the reference to the
    # sagged position. Every later tilt would then be under-reported, the
    # cos() correction would under-correct, and the SLOPE would inflate. The
    # rows already collected were measured against the original reference, so
    # changing it mid-set silently mixes two different geometries.
    if wt["rows"] and wt.get("ang0_set"):
        w_set(f"HOLDING — keeping the original horizontal reference "
              f"({math.degrees(wt['ang0']):+.1f}°). Level the arm and press "
              f"'Re-zero horizontal' if you have re-positioned it.", AMBER)
    else:
        wt["ang0"] = T["ang"]
        wt["ang0_set"] = True
    try:
        dev_send(f"Pi{float(w_iqmx.get()):.2f}")
    except ValueError:
        pass
    dev_send("H")
    wt["holding"] = True
    if not (wt["rows"] and wt.get("ang0_set")):
        w_set(f"HOLDING (horizontal reference {math.degrees(wt['ang0']):+.1f}°) — "
              f"add a weight, enter grams, Record", GREEN)


def w_stop():
    wt["holding"] = False
    stop_all()
    w_set("Released — shaft free", RED)


def w_rezero():
    wt["ang0"] = T["ang"]
    wt["ang0_set"] = True
    w_set(f"Horizontal reference set to {math.degrees(wt['ang0']):+.1f}°. "
          f"Rows already recorded used the previous reference — reset the data "
          f"if you have changed the geometry.", BLUE)


hb2 = tk.Frame(w_l, bg=SURFACE); hb2.pack(pady=(8, 2))
btn(hb2, "⚓ HOLD", GREEN, "white", w_hold, width=9).pack(side="left", padx=(0, 6))
btn(hb2, "■ RELEASE", RED, "white", w_stop, width=10).pack(side="left")
btn(w_l, "⌖ Re-zero horizontal (arm levelled, motor released)", FIELD, MUTED,
    w_rezero).pack(fill="x", pady=(4, 0))
section(w_l, "Record a step")
w_add = entry_row(w_l, "Total added weight on arm (g)", 0.0)


def w_record():
    if not wt["holding"]:
        w_set("HOLD first", AMBER); return
    try:
        add_g = float(w_add.get()); L = float(w_len.get()); arm_g = float(w_arm.get())
    except ValueError:
        w_set("Check the numbers", AMBER); return
    if T["state"] != 2:
        w_set(f"Firmware is not HOLDING (state = {STATE_NAMES.get(T['state'],'?')}). "
              "Press HOLD again and watch the Diagnostics console.", RED)
        return
    m, sd = iq_avg(1.0)
    if m is None:
        w_set("No telemetry — connect first", AMBER); return
    # A PD hold has finite stiffness, so the arm sags further with every added
    # weight: error = Iq / Kp. Gravity torque is m·g·L·cos(tilt), and ignoring
    # the cosine bends the SLOPE — it grows with load, so it is not absorbed by
    # the intercept the way a constant would be. Measure the tilt from the
    # encoder rather than trusting a gain value.
    tilt = T["ang"] - wt.get("ang0", 0.0)
    tau_flat = (add_g + arm_g) * 1e-3 * G_ACC * L
    tau = tau_flat * math.cos(tilt)
    tilt_deg = math.degrees(tilt)
    wt["rows"].append((add_g, add_g + arm_g, tau, abs(m), sd or 0.0, tilt_deg))
    w_table.insert("", "end", values=(f"{add_g:.0f}", f"{tau*1000:.1f}",
                                      f"{abs(m):.3f}", f"±{(sd or 0)*1000:.0f}m",
                                      f"{tilt_deg:+.1f}°"))
    w_fit()
    if abs(tilt_deg) > 5:
        w_set(f"Recorded {tau*1000:.1f} mNm at {abs(m):.3f} A — but the arm has sagged "
              f"{tilt_deg:+.1f}°. Corrected by cos(), but the correction is only as good "
              f"as the horizontal reference — raise the hold stiffness (Pp), or "
              f"RELEASE, re-level, HOLD and re-zero between steps.", AMBER)
    else:
        w_set(f"Recorded: {tau*1000:.1f} mNm at {abs(m):.3f} A (tilt {tilt_deg:+.1f}°)", GREEN)


btn(w_l, "➕ Record value", BLUE, "white", w_record).pack(pady=(4, 8), fill="x")


def w_end():
    if not wt["rows"]:
        w_set("No rows to save", AMBER); return
    path = log_path("kt-weight")
    if not path:
        w_set("Enter the motor serial number first", RED); return
    _f, wcsv = open_log(path, ["added_g", "total_g", "tau_Nm_cos_corrected",
                               "iq_A", "iq_std_A", "arm_tilt_deg"])
    with _f as f:
        for r in wt["rows"]:
            wcsv.writerow([f"{r[0]:.1f}", f"{r[1]:.1f}", f"{r[2]:.5f}",
                           f"{r[3]:.4f}", f"{r[4]:.4f}", f"{r[5]:.2f}"])
        wcsv.writerow([]); wcsv.writerow(["arm_effective_g", w_arm.get().strip()])
        wcsv.writerow(["lever_L_m", w_len.get().strip()])
        wcsv.writerow([]); wcsv.writerow(["kt_mNm_per_A", w_res.get("kt", "")])
    w_stop()
    w_set(f"Saved {len(wt['rows'])} rows → {path}", GREEN)


def w_undo():
    if not wt["rows"]:
        w_set("Nothing to undo", AMBER); return
    r = wt["rows"].pop()
    drop_last_row(w_table)
    w_fit()
    w_set(f"Removed the last step ({r[0]:.0f} g at {r[3]:.3f} A)", BLUE)


def w_reset():
    if not confirm_reset(len(wt["rows"]), "recorded steps"):
        return
    wt["rows"].clear()
    clear_table(w_table)
    w_fit()
    w_set("Data reset — add weights and record again", BLUE)


_wb = tk.Frame(w_l, bg=SURFACE); _wb.pack(fill="x", pady=(6, 0))
btn(_wb, "⌫ Undo last", FIELD, MUTED, w_undo).pack(side="left", padx=(0, 6))
btn(_wb, "↺ Reset data", FIELD, RED, w_reset).pack(side="left")

btn(w_l, "⏹ END — save log & release", FIELD, GREEN, w_end).pack(fill="x", pady=(6, 0))
w_set = mkstatus(w_l)

w_m_o, w_m = card(w_fr); w_m_o.pack(side="left", fill="y", padx=(0, 14))
section(w_m, "Live · holding current")
w_iq = big_value(w_m, "Iq (A, 1 s robust average)", BLUE)
w_state = tk.Label(w_m, text="—", bg=SURFACE, fg=MUTED, font=F_MONO)
w_state.pack(pady=(8, 0))
w_ang = tk.Label(w_m, text="", bg=SURFACE, fg=FAINT, font=F_MONO)
w_ang.pack(pady=(4, 0))

w_rsc_o, w_rsc = scroll_column(w_fr); w_rsc_o.pack(side="left", fill="y")
w_r_o, w_r = card(w_rsc); w_r_o.pack(fill="both", expand=True)
section(w_r, "Steps")
w_table = mktable(w_r, [("g", "added g", 70), ("t", "τ mNm", 80),
                        ("i", "Iq A", 80), ("s", "std", 60),
                        ("a", "tilt", 60)], height=10)
section(w_r, "Result · τ = Kt·Iq + τf")
w_lbl_kt = tk.Label(w_r, text="—", bg=SURFACE, fg=GREEN, font=("Consolas", 30, "bold"))
w_lbl_kt.pack()
tk.Label(w_r, text="Kt [mNm/A]  (motor)", bg=SURFACE, fg=FAINT, font=F_SM).pack()
w_lbl_r2 = tk.Label(w_r, text="record ≥ 2 steps", bg=SURFACE, fg=FAINT, font=F_LBL)
w_lbl_r2.pack(pady=(6, 0))
section(w_r, "τ = Kt·Iq + τf")
w_scatter = tk.Canvas(w_r, width=340, height=200, bg=SURFACE, highlightthickness=0)
w_scatter.pack(fill="x", pady=(0, 4))
w_res = {}


def w_fit():
    xs = [r[3] for r in wt["rows"]]; ys = [r[2] * 1000 for r in wt["rows"]]
    if len(wt["rows"]) < 2:
        # a stale Kt left on screen after an undo or reset is worse than none
        w_lbl_kt.config(text="—")
        w_lbl_r2.config(text="record ≥ 2 steps")
        w_res.pop("kt", None)
        draw_scatter(w_scatter, xs, ys, None, "Iq (A)", "τ (mN·m)")
        return
    fit = linfit([r[3] for r in wt["rows"]], [r[2] for r in wt["rows"]])
    if fit is None:
        return
    draw_scatter(w_scatter, xs, ys, (fit[0] * 1000, fit[1] * 1000, fit[2]),
                 "Iq (A)", "τ (mN·m)")
    a, b, r2 = fit
    w_res["kt"] = f"{a*1000:.2f}"
    w_lbl_kt.config(text=f"{a*1000:.1f}")
    txt = f"R² = {r2:.4f} · friction {b*1000:+.1f} mNm · {len(wt['rows'])} pts"
    if b < -0.005:
        # tau_gravity = Kt*Iq + tau_friction. Friction OPPOSES the sag, so it
        # helps hold the arm up and the intercept must be POSITIVE. A negative
        # one means the motor is fighting more torque than the entered masses
        # account for — almost always an under-counted arm weight.
        miss = -b / (1e-3 * G_ACC * max(float(w_len.get() or 0.1), 1e-6))
        txt += f"  ⚠ negative friction is impossible — arm weight looks ~{miss:.0f} g light"
        w_lbl_r2.config(text=txt, fg=RED)
    else:
        w_lbl_r2.config(text=txt, fg=FAINT)


add_tab("3 · KT · Weights", w_fr)


# ═════════════ step-test engine (tabs 3 & 5) ═══════════════════
def build_step_tab(exp_name, title_note, gear_default, with_eff):
    fr = tk.Frame(body, bg=BG)
    st = dict(rows=[], run=False, marks=[], breakaway=None)

    sc_o, sc = scroll_column(fr); sc_o.pack(side="left", fill="y", padx=(0, 14))
    l_o, l = card(sc); l_o.pack(fill="both", expand=True)
    section(l, f"Setup · {title_note}")
    e_i0 = entry_row(l, "Iq start (A)", 0.5)
    e_i1 = entry_row(l, "Iq end (A)", 3.0)
    e_ns = entry_row(l, "Number of steps", 6)
    e_ts = entry_row(l, "Step time (s)", 2.0)
    e_st = entry_row(l, "Settle discard (s)", 0.7)
    e_en = entry_row(l, "Engage current (A)", 0.30)
    e_rp = entry_row(l, "Current ramp (A/s)", 2.0)
    # [g2-B] contact detection replaces the old blind fixed-time engage
    e_cg = entry_row(l, "Contact threshold (g)", 15.0)
    e_em = entry_row(l, "Engage max (A)", 1.5)
    e_lv = entry_row(l, "Loadcell lever arm (m)", 0.10)
    e_gr = entry_row(l, "Gear ratio (out/motor)", gear_default)
    e_mk = entry_row(l, "Motor Kt for efficiency (mNm/A)", 83.7) if with_eff else None
    set_ = mkstatus(l)

    def runner():
        try:
            i0 = float(e_i0.get()); i1 = float(e_i1.get()); n = max(2, int(e_ns.get()))
            ts = max(0.8, float(e_ts.get())); settle = min(ts - 0.3, max(0.1, float(e_st.get())))
            lever = float(e_lv.get())
            i_eng = max(0.02, float(e_en.get())); ramp = max(0.1, float(e_rp.get()))
            thresh_g = max(1.0, float(e_cg.get()))
            i_engmax = max(i_eng, float(e_em.get()))
        except ValueError:
            set_("Check the numbers", AMBER); st["run"] = False; return
        if lc["ser"] is None:
            set_("Connect the loadcell serial first", RED); st["run"] = False; return
        if not dev_alive():
            set_("No telemetry from the driver — connect it first", RED); st["run"] = False; return
        if T["flags"] > 0 and not (T["flags"] & 0x01):
            set_("Firmware reports initFOC FAILED — the motor cannot move. See Diagnostics.", RED)
            st["run"] = False; return

        st["rows"].clear(); st["marks"].clear()
        for it in table.get_children():
            table.delete(it)

        set_("Taring — arm should be RESTING on the loadcell", BLUE)
        dev_send(f"Pr{ramp:.2f}")
        t0 = time.time(); time.sleep(0.8)
        z, _ = robust_mean([g for (_, g, _) in lc_window(t0, time.time())])
        z = z or 0.0

        # ENGAGE: make first contact ONCE, gently — then never leave contact.
        # The current is RAMPED until the cell responds, so a stiction breakaway
        # higher than the entered engage current no longer means "no contact".
        st["marks"].append(time.time())
        ok, i_contact = engage_until_contact(
            z, thresh_g, i_eng, i_engmax, 0.1, 1.2,
            alive=lambda: st["run"],
            report=lambda i: root.after(0, lambda i=i: set_(
                f"Engaging — {i:.2f} A, waiting for contact…", BLUE)))
        if not ok:
            dev_send("C0"); stop_all(); st["run"] = False
            m, _ = iq_avg(1.0)
            hint = ("the current sense reads ~0 as well — check the Diagnostics tab"
                    if (m is None or abs(m) < 0.1) else
                    "current IS flowing, so the arm is very likely pushing the WRONG WAY "
                    "— flip the direction (Ps) on the Diagnostics tab")
            root.after(0, lambda: set_(
                f"NO CONTACT up to {i_engmax:.2f} A: {hint}.", RED))
            return
        st["breakaway"] = i_contact
        root.after(0, lambda: set_(f"Contact at {i_contact:.2f} A (breakaway) — running steps", GREEN))

        # never sweep below the current that was needed to make contact: those
        # points sit in the friction dead-zone and only bias the fit
        i0 = max(i0, i_contact)
        currents = [i0 + (i1 - i0) * i / (n - 1) for i in range(n)]
        prev = i_contact
        for k, iq in enumerate(currents):
            if not st["run"]:
                break
            dev_send(f"C{iq:.3f}")
            t_step = time.time(); st["marks"].append(t_step)
            settle_eff = max(settle, abs(iq - prev) / ramp + 0.4)
            settle_eff = min(settle_eff, ts - 0.2)
            prev = iq
            time.sleep(settle_eff)                   # discard: force not settled
            t_use0 = time.time()
            time.sleep(max(0.05, ts - settle_eff))
            samples = lc_window(t_use0, time.time())
            gm, gs = robust_mean([g for (_, g, _) in samples])
            im, _ = iq_avg(ts - settle)
            used_cmd = False
            if im is None or (abs(im) < 0.25 * iq and iq >= 0.1):
                # measured current path dead — fit with the commanded value
                icm, _ = iqc_avg(ts - settle)
                im = icm if icm is not None else iq
                used_cmd = True
                root.after(0, lambda: set_(
                    "Current sense reads ~0 — using COMMANDED Iq for the fit. "
                    "Run the self-test (Z) on the Diagnostics tab.", AMBER))
            if gm is None:
                root.after(0, lambda k=k: set_(f"Step {k+1}: no loadcell data", RED))
                continue
            grams = gm - z
            tau = grams * 1e-3 * G_ACC * lever
            st["rows"].append((iq, abs(im or iq), grams, gs or 0, tau, used_cmd))
            root.after(0, lambda r=st["rows"][-1]:
                       table.insert("", "end", values=(f"{r[0]:.2f}", f"{r[1]:.3f}",
                                    f"{r[2]:.1f}", f"±{r[3]:.1f}", f"{r[4]*1000:.1f}")))
            root.after(0, fit)
            if not used_cmd:
                root.after(0, lambda k=k, n=n: set_(f"Step {k+1}/{n} done", BLUE))
        dev_send("C0"); stop_all()
        st["run"] = False
        root.after(0, save)

    def start():
        if st["run"]:
            return
        st["run"] = True
        threading.Thread(target=runner, daemon=True).start()

    def stop():
        st["run"] = False
        dev_send("C0"); stop_all()
        set_("Stopped", RED)

    def fit():
        xs = [r[1] for r in st["rows"]]; ys = [r[4] * 1000 for r in st["rows"]]
        if len(st["rows"]) < 2:
            lbl_kt.config(text="—")
            lbl_r2.config(text="run ≥ 2 steps")
            draw_scatter(scatter, xs, ys, None, "Iq meas (A)", "τ (mN·m)")
            return
        f = linfit([r[1] for r in st["rows"]], [r[4] for r in st["rows"]])
        if f is None:
            return
        draw_scatter(scatter, xs, ys, (f[0] * 1000, f[1] * 1000, f[2]),
                     "Iq meas (A)", "τ (mN·m)")
        a, b, r2 = f
        lbl_kt.config(text=f"{a*1000:.1f}")
        extra = f"R² = {r2:.4f} · friction {b*1000:+.1f} mNm"
        if st.get("breakaway"):
            extra += f" · breakaway {st['breakaway']:.2f} A"
        if any(r[5] for r in st["rows"]):
            extra += " · ⚠ COMMANDED Iq used"
        if with_eff and e_mk is not None:
            try:
                ktm = float(e_mk.get()) * 1e-3
                N = float(e_gr.get())
                eff = a / (ktm * N) * 100.0
                extra += f" · efficiency {eff:.1f}%"
            except ValueError:
                pass
        lbl_r2.config(text=extra)

    def save():
        if not st["rows"]:
            return
        path = log_path(exp_name)
        if not path:
            set_("Enter the motor serial number first", RED); return
        _f, w = open_log(path, ["iq_cmd_A", "iq_meas_A", "grams", "grams_std",
                                "tau_Nm", "iq_from_command"])
        with _f as f:
            for r in st["rows"]:
                w.writerow([f"{r[0]:.3f}", f"{r[1]:.4f}", f"{r[2]:.2f}",
                            f"{r[3]:.2f}", f"{r[4]:.5f}", int(r[5])])
            w.writerow([]); w.writerow(["kt_out_mNm_per_A", lbl_kt.cget("text")])
        set_(f"Done — saved → {path}", GREEN)

    def undo():
        if st["run"]:
            set_("Stop the sweep first", AMBER); return
        if not st["rows"]:
            set_("Nothing to undo", AMBER); return
        r = st["rows"].pop()
        drop_last_row(table)
        fit()
        set_(f"Removed the last step ({r[0]:.2f} A, {r[2]:.1f} g)", BLUE)

    def reset():
        if st["run"]:
            set_("Stop the sweep first", AMBER); return
        if not confirm_reset(len(st["rows"]), "steps"):
            return
        st["rows"].clear(); st["marks"].clear(); st["breakaway"] = None
        clear_table(table)
        fit()
        set_("Data reset — press RUN to record again", BLUE)

    bb = tk.Frame(l, bg=SURFACE); bb.pack(pady=(8, 2))
    btn(bb, "▶ RUN", GREEN, "white", start, width=8).pack(side="left", padx=(0, 6))
    btn(bb, "■ STOP", RED, "white", stop, width=8).pack(side="left")
    bb2 = tk.Frame(l, bg=SURFACE); bb2.pack(fill="x", pady=(4, 2))
    btn(bb2, "⌫ Undo last", FIELD, MUTED, undo).pack(side="left", padx=(0, 6))
    btn(bb2, "↺ Reset data", FIELD, RED, reset).pack(side="left")

    m_o, m = card(fr); m_o.pack(side="left", fill="both", expand=True, padx=(0, 14))
    section(m, "Loadcell force (blue) · measured Iq (purple, own scale) · dashed = steps")
    cv = tk.Canvas(m, width=620, height=300, bg=SURFACE, highlightthickness=0)
    cv.pack(fill="both", expand=True, pady=4)
    live = tk.Label(m, text="", bg=SURFACE, fg=MUTED, font=F_MONO)
    live.pack()

    def tick():
        alive = sense_alive()
        y2 = snap_hist(iq_hist) if alive else snap_hist(iqc_hist)
        lab = ("force vs current — both as MAGNITUDE, so they rise together"
               if alive else
               "force vs COMMANDED current (magnitude) — sense reads 0!")
        _lc = snap_lc()
        draw_ts(cv, [(t, g) for (t, g, _) in _lc], BLUE, lab,
                marks=st["marks"], y2=y2,
                unit1="g", unit2="A",
                label1="|force|", label2=("|Iq| meas" if alive else "|Iq| CMD"))
        s = _lc[-1] if _lc else None
        base = f"loadcell {s[1]:.1f} g   " if s else "no loadcell data   "
        live.config(text=base + f"Iq meas {T['iq']:+.2f} / cmd {T['iqc']:+.2f} A   "
                                f"[{STATE_NAMES.get(T['state'], '?')}]",
                    fg=MUTED if alive else RED)

    safe_tick(tick, 150)()

    rsc_o, rsc = scroll_column(fr); rsc_o.pack(side="left", fill="y")
    r_o, r = card(rsc); r_o.pack(fill="both", expand=True)
    section(r, "Steps")
    table = mktable(r, [("c", "Iq cmd", 70), ("i", "Iq meas", 80), ("g", "grams", 80),
                        ("s", "std", 65), ("t", "τ mNm", 85)], height=10)
    section(r, "Result · τ = Kt·Iq")
    lbl_kt = tk.Label(r, text="—", bg=SURFACE, fg=GREEN, font=("Consolas", 30, "bold"))
    lbl_kt.pack()
    tk.Label(r, text=("Kt_out [mNm/A] (after capstan)" if with_eff else "Kt [mNm/A] (motor)"),
             bg=SURFACE, fg=FAINT, font=F_SM).pack()
    lbl_r2 = tk.Label(r, text="run ≥ 2 steps", bg=SURFACE, fg=FAINT, font=F_LBL)
    lbl_r2.pack(pady=(6, 0))
    section(r, "τ = Kt·Iq")
    scatter = tk.Canvas(r, width=340, height=200, bg=SURFACE, highlightthickness=0)
    scatter.pack(fill="x", pady=(0, 4))
    draw_scatter(scatter, [], [], None, "Iq meas (A)", "τ (mN·m)")
    return fr


add_tab("4 · KT · Loadcell", build_step_tab("kt-loadcell", "motor direct → loadcell", 1.0, False))

# ═════════════ TAB 4 · Heat over force ═════════════════════════
h_fr = tk.Frame(body, bg=BG)
ht = dict(run=False, rows=[], t0=0.0, file=None, wr=None, marks=[], overt=False)

h_sc_o, h_sc = scroll_column(h_fr); h_sc_o.pack(side="left", fill="y", padx=(0, 14))
h_l_o, h_l = card(h_sc); h_l_o.pack(fill="both", expand=True)
section(h_l, "Setup · continuous-current thermal test")
h_iq = entry_row(h_l, "Test Iq (A)", 2.0)
h_lim = entry_row(h_l, "High-temp protection (°C)", 80.0)
h_lv = entry_row(h_l, "Loadcell lever arm (m)", 0.10)
h_set = mkstatus(h_l)


def h_runner():
    try:
        iq = float(h_iq.get()); tlim = float(h_lim.get()); lever = float(h_lv.get())
    except ValueError:
        h_set("Check the numbers", AMBER); ht["run"] = False; return
    if lc["ser"] is None:
        h_set("Connect the loadcell/temp serial first", RED); ht["run"] = False; return
    if not dev_alive():
        h_set("No telemetry from the driver — connect it first", RED); ht["run"] = False; return
    path = log_path("heat-force")
    if not path:
        h_set("Enter the motor serial number first", RED); ht["run"] = False; return
    ht["rows"].clear(); ht["marks"] = [time.time()]
    ht["file"], ht["wr"] = open_log(
        path, ["t_s", "iq_meas_A", "grams", "tau_Nm", "temp_C", "note"])
    dev_send(f"C{iq:.3f}")
    ht["t0"] = time.time()
    h_set(f"Running at {iq:.2f} A — logging 1 Hz → {os.path.basename(path)}", BLUE)
    while ht["run"]:
        time.sleep(1.0)
        now = time.time()
        win = lc_window(now - 1.0, now)
        gm, _ = robust_mean([g for (_, g, _) in win])
        # [g3-A] temperature now prefers the driver board's own thermistor and
        # falls back to the load-cell Arduino's, instead of only ever reading
        # the latter.
        _tv = [c for (_, c) in temp_window(now - 1.0, now)]
        tm, _ = robust_mean(_tv) if _tv else (None, None)
        im, _ = iq_avg(1.0)
        tau = (gm or 0.0) * 1e-3 * G_ACC * lever
        note = ""
        if tm is not None and tm >= tlim:
            note = "OVERTEMP-STOP"
        # a watchdog trip or fault mid-run must not be logged as valid data
        if T["state"] != 3:
            note = note or "FIRMWARE-LEFT-CURRENT-MODE"
        row = (now - ht["t0"], abs(im or iq), gm or 0.0, tau, tm)
        ht["rows"].append(row)
        ht["wr"].writerow([f"{row[0]:.1f}", f"{row[1]:.3f}", f"{row[2]:.1f}",
                           f"{row[3]:.5f}", "" if tm is None else f"{tm:.1f}", note])
        ht["file"].flush()
        root.after(0, lambda r=row: h_live_row(r))
        if note == "OVERTEMP-STOP":
            ht["overt"] = True
            root.after(0, lambda tm=tm: h_set(
                f"OVERTEMP {tm:.1f}°C ≥ {tlim:.0f}°C — stopped, log saved", RED))
            break
        if note == "FIRMWARE-LEFT-CURRENT-MODE":
            ht["overt"] = True
            root.after(0, lambda: h_set(
                "Firmware left CURRENT mode mid-test (watchdog or fault) — "
                "stopped. See the Diagnostics console.", RED))
            break
    dev_send("C0"); stop_all()
    ht["run"] = False
    try:
        ht["file"].close()
    except Exception:
        pass
    if not ht["overt"]:
        root.after(0, lambda: h_set(f"Saved → {path}", GREEN))
    ht["overt"] = False


def h_start():
    if ht["run"]:
        return
    ht["run"] = True
    threading.Thread(target=h_runner, daemon=True).start()


def h_stop():
    ht["run"] = False


def h_reset():
    if ht["run"]:
        h_set("Stop the run first", AMBER); return
    if not confirm_reset(len(ht["rows"]), "logged samples"):
        return
    ht["rows"].clear(); ht["marks"] = []
    clear_table(h_table)
    h_set("Data reset — the saved CSV from the last run is untouched", BLUE)


hb3 = tk.Frame(h_l, bg=SURFACE); hb3.pack(pady=(8, 2))
btn(hb3, "▶ RUN", GREEN, "white", h_start, width=8).pack(side="left", padx=(0, 6))
btn(hb3, "■ STOP", RED, "white", h_stop, width=8).pack(side="left")
_hb = tk.Frame(h_l, bg=SURFACE); _hb.pack(fill="x", pady=(4, 2))
btn(_hb, "↺ Reset data", FIELD, RED, h_reset).pack(side="left")
tk.Label(h_l, text="Goal: find the max Iq the motor holds\ncontinuously without overheating — that\nbecomes ExArMo's working current limit.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(10, 0))

h_m_o, h_m = card(h_fr); h_m_o.pack(side="left", fill="both", expand=True, padx=(0, 14))
section(h_m, "Temperature (purple) · force (blue)")
h_cv = tk.Canvas(h_m, width=640, height=320, bg=SURFACE, highlightthickness=0)
h_cv.pack(fill="both", expand=True, pady=4)
h_live = tk.Label(h_m, text="", bg=SURFACE, fg=MUTED, font=F_MONO)
h_live.pack()


def h_tick():
    _lc = snap_lc()
    _now = time.time()
    draw_ts(h_cv, [(t, g) for (t, g, _) in _lc], BLUE, "force and temperature",
            marks=ht["marks"], y2=temp_window(_now - 60.0, _now),
            unit1="g", unit2="°C", label1="|force|", label2="temp")
    s = _lc[-1] if _lc else None
    tc = temp_now(2.0)
    if s:
        h_live.config(text=f"{s[1]:.1f} g   {('%.1f' % tc) if tc is not None else '--'} °C "
                           f"({temp_label()})   Iq {T['iq']:+.2f} A")


h_rsc_o, h_rsc = scroll_column(h_fr); h_rsc_o.pack(side="left", fill="y")
h_r_o, h_r = card(h_rsc); h_r_o.pack(fill="both", expand=True)
section(h_r, "Log (1 Hz)")
h_table = mktable(h_r, [("t", "t s", 60), ("i", "Iq A", 70), ("g", "grams", 75),
                        ("tau", "τ mNm", 80), ("T", "°C", 60)], height=14)


def h_live_row(r):
    h_table.insert("", "end", values=(f"{r[0]:.0f}", f"{r[1]:.2f}", f"{r[2]:.0f}",
                                      f"{r[3]*1000:.1f}", "--" if r[4] is None else f"{r[4]:.1f}"))
    kids = h_table.get_children()
    if kids:
        h_table.see(kids[-1])


add_tab("5 · Heat / Force", h_fr)

# ═════════════ TAB 5 · Capstan torque ══════════════════════════
add_tab("6 · Capstan · Torque", build_step_tab("capstan-torque",
        "motor → capstan → loadcell (output side)", 9.0, True))

# ═════════════ TAB 6 · Thermal rise  [g3-A] ════════════════════
# WHAT THIS MEASURES, AND WHY IT IS NOT THE HEAT/FORCE TAB.
# Tab 5 answers "does it survive N amps" by watching a number climb toward a
# limit. This tab answers the question that actually sets ExArMo's continuous
# current rating: how the motor's temperature RESPONDS to a known dissipation.
# Hold one current, log the curve, and fit a first-order thermal model
#
#       T(t) = T_amb + dT_inf * (1 - exp(-t/tau))
#
# from which R_th = dT_inf / P_cu and the continuous current for any allowed
# winding rise falls straight out. Copper loss for three phases driven by FOC
# is P_cu = 1.5 * Iq^2 * R_phase — it is 3/2 and not 3 because Iq is the peak
# of the phase current, not its RMS, and forgetting that overstates the loss
# by a factor of two and halves the R_th you report.
#
# THE FIT DOES NOT NEED THE RUN TO REACH STEADY STATE. Waiting for a real
# plateau on a 5008 takes 30-45 minutes and everybody stops early; reading
# dT_inf off a curve that was still climbing then understates it badly.
# Differentiating the model gives
#
#       dT/dt = (T_inf - T)/tau  =  (-1/tau)*T + T_inf/tau
#
# which is a straight line in (T, dT/dt) — so a least-squares fit of the
# SLOPE against the TEMPERATURE recovers both tau and T_inf from the transient
# alone. r^2 is reported because that line is also the honest warning when the
# data is too noisy or too short to support the extrapolation.
th_fr = tk.Frame(body, bg=BG)
th = dict(run=False, rows=[], t0=0.0, file=None, wr=None, marks=[],
          phase="", stopped="", src="", fit=None)

th_sc_o, th_sc = scroll_column(th_fr); th_sc_o.pack(side="left", fill="y", padx=(0, 14))
th_l_o, th_l = card(th_sc); th_l_o.pack(fill="both", expand=True)
section(th_l, "Setup · thermal step response")
th_iq   = entry_row(th_l, "Test Iq (A)", 2.0)
th_heat = entry_row(th_l, "Heat for (min)", 20.0)
th_cool = entry_row(th_l, "Then cool for (min)", 10.0)
th_per  = entry_row(th_l, "Log every (s)", 2.0)
th_lim  = entry_row(th_l, "Abort at (°C)", 80.0)
th_res  = entry_row(th_l, "Phase resistance R (Ω)", 0.54)
th_rise = entry_row(th_l, "Allowed rise for rating (K)", 60.0)
th_set = mkstatus(th_l)


def th_pcu(iq, r):
    """Copper loss [W] for a FOC drive commanding peak q-axis current iq."""
    return 1.5 * iq * iq * r


def th_runner():
    try:
        iq = float(th_iq.get()); heat_s = float(th_heat.get()) * 60.0
        cool_s = float(th_cool.get()) * 60.0; per = float(th_per.get())
        tlim = float(th_lim.get())
    except ValueError:
        th_set("Check the numbers", AMBER); th["run"] = False; return
    if per < 0.5:
        th_set("Log period below 0.5 s serves no purpose here", AMBER)
        th["run"] = False; return
    if not dev_alive():
        th_set("No telemetry from the driver — connect it first", RED)
        th["run"] = False; return
    src = temp_src()
    if src is None:
        th_set("No temperature source. Fit the thermistor on GPIO3/PA2, or "
               "connect the loadcell/temp Arduino.", RED)
        th["run"] = False; return
    path = log_path("thermal-rise")
    if not path:
        th_set("Enter the motor serial number first", RED); th["run"] = False; return

    t_amb = temp_now(3.0, src)
    if t_amb is None:
        th_set("Temperature source went quiet before the run started", RED)
        th["run"] = False; return

    th["src"] = src
    th["rows"].clear(); th["marks"] = [time.time()]; th["fit"] = None
    th["stopped"] = ""
    th["file"], th["wr"] = open_log(
        path, ["t_s", "phase", "iq_cmd_A", "iq_meas_A", "temp_C",
               "rise_K", "p_cu_W", "temp_source", "note"])
    p_cu = th_pcu(iq, float(th_res.get() or 0.0))

    th["t0"] = time.time()
    th["phase"] = "heat"
    dev_send(f"C{iq:.3f}")
    th_set(f"Heating at {iq:.2f} A ({p_cu:.1f} W) — ambient {t_amb:.1f} °C, "
           f"temperature from the {temp_label()}", BLUE)

    def log_sample(phase, iq_cmd):
        now = time.time()
        tm = temp_now(max(1.0, per * 0.5), th["src"])
        im, _ = iq_avg(min(2.0, per))
        note = ""
        if tm is None:
            note = "NO-TEMP-SAMPLE"
        if phase == "heat" and T["state"] != 3:
            # exactly the trap tab 5 already learned: a watchdog trip or an
            # over-temp stop mid-run leaves the motor cold-ish and the log
            # looking like a valid, gentle curve.
            note = note or "FIRMWARE-LEFT-CURRENT-MODE"
        row = (now - th["t0"], phase, iq_cmd, abs(im or 0.0), tm,
               None if tm is None else tm - t_amb)
        th["rows"].append(row)
        th["wr"].writerow([f"{row[0]:.1f}", phase, f"{iq_cmd:.3f}",
                           f"{row[3]:.3f}",
                           "" if tm is None else f"{tm:.2f}",
                           "" if tm is None else f"{row[5]:.2f}",
                           f"{p_cu:.2f}", th["src"], note])
        th["file"].flush()
        root.after(0, lambda r=row: th_live_row(r))
        return tm, note

    # ---- heating ----
    next_t = time.time()
    while th["run"] and (time.time() - th["t0"]) < heat_s:
        next_t += per
        time.sleep(max(0.0, next_t - time.time()))
        if not th["run"]:
            break
        tm, note = log_sample("heat", iq)
        if tm is not None and tm >= tlim:
            th["stopped"] = f"ABORT at {tm:.1f} °C ≥ {tlim:.0f} °C"
            break
        if note == "FIRMWARE-LEFT-CURRENT-MODE":
            th["stopped"] = ("the firmware left CURRENT mode mid-run "
                             "(watchdog, over-temp or fault) — see Diagnostics")
            break

    # ---- cooling ----
    # The cool-down is not padding. It is the SAME time constant measured with
    # the heat source switched off, so it is an independent check on tau that
    # does not depend on knowing R_phase or the current at all.
    dev_send("C0"); stop_all()
    if th["run"] and cool_s > 0 and not th["stopped"]:
        th["phase"] = "cool"
        th["marks"].append(time.time())
        root.after(0, lambda: th_set(
            f"Cooling — logging for {cool_s/60.0:.0f} more min "
            f"(this gives a second, independent tau)", BLUE))
        t_cool0 = time.time()
        next_t = time.time()
        while th["run"] and (time.time() - t_cool0) < cool_s:
            next_t += per
            time.sleep(max(0.0, next_t - time.time()))
            if not th["run"]:
                break
            log_sample("cool", 0.0)

    th["run"] = False
    th["phase"] = ""
    try:
        th["file"].close()
    except Exception:
        pass
    msg = th["stopped"]
    root.after(0, lambda: th_set(
        (f"{msg} — log saved → {os.path.basename(path)}" if msg
         else f"Done — {len(th['rows'])} samples → {os.path.basename(path)}. Press FIT."),
        RED if msg else GREEN))
    root.after(0, th_fit)


def th_start():
    if th["run"]:
        return
    th["run"] = True
    threading.Thread(target=th_runner, daemon=True).start()


def th_stop():
    th["run"] = False
    dev_send("C0"); stop_all()


def th_reset():
    if th["run"]:
        th_set("Stop the run first", AMBER); return
    if not confirm_reset(len(th["rows"]), "logged samples"):
        return
    th["rows"].clear(); th["marks"] = []; th["fit"] = None
    clear_table(th_table)
    for _l in th_out.values():
        _l.config(text="—")
    th_set("Data reset — the saved CSV from the last run is untouched", BLUE)


thb = tk.Frame(th_l, bg=SURFACE); thb.pack(pady=(8, 2))
btn(thb, "▶ RUN", GREEN, "white", th_start, width=8).pack(side="left", padx=(0, 6))
btn(thb, "■ STOP", RED, "white", th_stop, width=8).pack(side="left")
_thb = tk.Frame(th_l, bg=SURFACE); _thb.pack(fill="x", pady=(4, 2))
btn(_thb, "∿ Fit thermal model", FIELD, BLUE, lambda: th_fit()).pack(side="left")
btn(_thb, "↺ Reset", FIELD, RED, th_reset).pack(side="left", padx=(6, 0))
tk.Label(th_l, text="Motor at rest, still air, bead on the stator end-winding\n"
                    "or the can. The number this produces is only as good as\n"
                    "where that bead is — record it in the logbook.",
         bg=SURFACE, fg=FAINT, font=F_SM, justify="left").pack(anchor="w", pady=(10, 0))

# ── middle: live chart ──
th_m_o, th_m = card(th_fr); th_m_o.pack(side="left", fill="both", expand=True, padx=(0, 14))
section(th_m, "Temperature (purple) · Iq (blue)")
th_cv = tk.Canvas(th_m, width=640, height=300, bg=SURFACE, highlightthickness=0)
th_cv.pack(fill="both", expand=True, pady=4)
th_live = tk.Label(th_m, text="", bg=SURFACE, fg=MUTED, font=F_MONO)
th_live.pack()

th_res_f = tk.Frame(th_m, bg=SURFACE); th_res_f.pack(fill="x", pady=(10, 0))
th_out = {}
for _key, _cap in (("tau", "τ  (min)"), ("dinf", "ΔT∞  (K)"),
                   ("rth", "R_th  (K/W)"), ("icont", "I cont  (A)")):
    _c = tk.Frame(th_res_f, bg=SURFACE); _c.pack(side="left", expand=True)
    th_out[_key] = big_value(_c, _cap)
th_fit_note = tk.Label(th_m, text="", bg=SURFACE, fg=FAINT, font=F_SM,
                       justify="left", wraplength=620)
th_fit_note.pack(anchor="w", pady=(6, 0))


def th_fit():
    """Fit tau and T_inf from the HEATING transient (see the note above), and
    tau again from the COOL-DOWN as an independent check."""
    rows = [r for r in th["rows"] if r[1] == "heat" and r[4] is not None]
    if len(rows) < 8:
        th_fit_note.config(text="Need at least 8 heating samples with a "
                                "temperature before anything can be fitted.",
                           fg=AMBER)
        return
    ts = [r[0] for r in rows]
    cs = [r[4] for r in rows]
    f = expfit(ts, cs)
    if not f or f[2] >= 0.0:
        # B >= 0 while heating means the curve is not rising toward a limit.
        th_fit_note.config(
            text="The temperature is not rising toward a limit in this data — "
                 "either the run is far too short, or nothing is heating up. "
                 "No τ can be extracted.", fg=AMBER)
        return
    tau, t_inf, _B, r2 = f
    t_amb = cs[0] - (rows[0][5] or 0.0)     # the rise is logged, so this
    d_inf = t_inf - t_amb                   # recovers the ambient exactly
    try:
        iq = float(th_iq.get()); rph = float(th_res.get())
        allow = float(th_rise.get())
    except ValueError:
        iq = rph = allow = 0.0
    p_cu = th_pcu(iq, rph)
    rth = d_inf / p_cu if p_cu > 1e-9 else None
    icont = (math.sqrt(allow / (1.5 * rph * rth))
             if (rth and rth > 1e-9 and rph > 1e-9 and allow > 0) else None)

    # cool-down: same tau, measured with the heat source off, so it depends on
    # neither R_phase nor the current. If the two disagree badly, the bead is
    # reading its own mounting rather than the motor.
    crows = [r for r in th["rows"] if r[1] == "cool" and r[4] is not None]
    cf = expfit([r[0] for r in crows], [r[4] for r in crows]) if len(crows) >= 8 else None
    tau_c = cf[0] if cf else None

    th["fit"] = dict(tau=tau, t_inf=t_inf, d_inf=d_inf, r2=r2, rth=rth,
                     icont=icont, p_cu=p_cu, t_amb=t_amb, tau_cool=tau_c)

    th_out["tau"].config(text=f"{tau/60.0:.1f}")
    th_out["dinf"].config(text=f"{d_inf:.1f}")
    th_out["rth"].config(text="—" if rth is None else f"{rth:.2f}")
    th_out["icont"].config(text="—" if icont is None else f"{icont:.2f}")

    reached = (max(cs) - t_amb) / d_inf if d_inf > 1e-6 else 0.0
    warn = ""
    if r2 < 0.95:
        warn = ("  ⚠ r² is low for a first-order fit: the curve is noisy or is "
                "not a single exponential. Check the bead is actually attached "
                "to the motor and not swinging in the air.")
    elif reached < 0.4:
        warn = (f"  ⚠ the run only reached {reached*100:.0f}% of the fitted "
                f"ΔT∞ — a long extrapolation. Treat ΔT∞ and R_th as indicative "
                f"and re-run for at least 2τ ({2*tau/60.0:.0f} min).")
    elif tau_c is not None and (tau_c > 1.6 * tau or tau_c < 0.6 * tau):
        warn = (f"  ⚠ the cool-down gives τ = {tau_c/60.0:.1f} min against "
                f"{tau/60.0:.1f} min heating. One body does not have two time "
                f"constants — the sensor is probably reading its own mount.")
    cool_txt = "" if tau_c is None else f"  ·  τ from cool-down = {tau_c/60.0:.1f} min"
    th_fit_note.config(
        text=(f"T(t) = {t_amb:.1f} + {d_inf:.1f}·(1 − e^(−t/{tau/60.0:.1f} min)) °C   "
              f"·  r² = {r2:.4f}  ·  P_cu = {p_cu:.1f} W at {iq:.2f} A "
              f"(1.5·Iq²·R){cool_txt}  ·  source: {th['src'] or temp_label()}" + warn),
        fg=AMBER if warn else MUTED)


# ── right: sample table ──
th_rsc_o, th_rsc = scroll_column(th_fr); th_rsc_o.pack(side="left", fill="y")
th_r_o, th_r = card(th_rsc); th_r_o.pack(fill="both", expand=True)
section(th_r, "Log")
th_table = mktable(th_r, [("t", "t min", 62), ("ph", "phase", 58),
                          ("i", "Iq A", 62), ("T", "°C", 62),
                          ("d", "rise K", 66)], height=16)


def th_live_row(r):
    th_table.insert("", "end", values=(
        f"{r[0]/60.0:.1f}", r[1], f"{r[3]:.2f}",
        "--" if r[4] is None else f"{r[4]:.1f}",
        "--" if r[5] is None else f"{r[5]:+.1f}"))
    kids = th_table.get_children()
    if kids:
        th_table.see(kids[-1])


def th_tick():
    now = time.time()
    draw_ts(th_cv, [(t, i) for (t, i) in snap_hist(iq_hist) if t >= now - 60],
            BLUE, "Iq and motor temperature", marks=th["marks"],
            y2=temp_window(now - 60.0, now), unit1="A", unit2="°C",
            label1="|Iq|", label2="temp")
    tc = temp_now(2.0)
    el = (now - th["t0"]) / 60.0 if th["run"] else 0.0
    th_live.config(
        text=(f"{('%.1f' % tc) if tc is not None else '--'} °C   "
              f"Iq {T['iq']:+.2f} A   "
              f"{(th['phase'] + ' ' + ('%.1f' % el) + ' min') if th['run'] else temp_label()}"))


add_tab("7 · Thermal · Rise", th_fr)


# ═════════════ global live loops ═══════════════════════════════
def global_tick():
    m, spread = kv_steady_rpm()
    dut = (m or 0.0) * kv_ratio_v()
    kv_rpm.config(text=f"{dut:.0f}")
    if m is not None and kv["spinning"] and kv["steps"]:
        # 0.5% drift of the MEAN is a realistic bar once the measurement comes
        # from angle rather than from averaged velocity samples.
        tol = max(2.0, 0.005 * abs(kv["steps"][kv["idx"]]))
        dr = (spread or 99) * kv_ratio_v()
        ok = dr < tol
        kv_steady.config(
            text=(f"● STEADY — read the meter   (drift {dr:.1f} rpm)" if ok
                  else f"● settling…   drift {dr:.1f} rpm > {tol:.1f}"),
            fg=GREEN if ok else AMBER)
    else:
        kv_steady.config(text="")
    kvdata = [(t, r * kv_ratio_v()) for (t, r) in snap_hist(rpm_hist)]
    draw_ts(kv_chart, kvdata, BLUE, "DUT speed", unit1="rpm", label1="|speed|")
    m2, _ = iq_avg(1.0)
    w_iq.config(text=f"{abs(m2):.3f}" if m2 is not None else "—")
    w_state.config(text=STATE_NAMES.get(T["state"], "?"),
                   fg=GREEN if T["state"] == 2 else MUTED)
    w_ang.config(text=f"shaft {math.degrees(T['ang']):+.1f}°   cmd {T['iqc']:+.2f} A")


show_tab(0)
for _fn, _ms in ((foot_tick, 200), (dg_tick, 200), (dg_console_tick, 300),
                 (global_tick, 120), (h_tick, 200), (th_tick, 400)):
    safe_tick(_fn, _ms)()
threading.Thread(target=dev_reader, daemon=True).start()
threading.Thread(target=lc_reader, daemon=True).start()


def on_close():
    global running
    running = False
    ht["run"] = False
    th["run"] = False          # [g3-A] a thermal run holds current — end it
    stop_all()
    dev_disconnect(); lc_disconnect()
    root.destroy()


root.protocol("WM_DELETE_WINDOW", on_close)
root.mainloop()