/*
  ExArMo Lab — load cell bridge  (raw)
  ====================================
  Streams RAW HX711 counts to ExarmoLabGui (exarmolab.py) at 115200 baud.

  ---------------------------------------------------------------------------
  WHY THIS SENDS RAW COUNTS AND NOT GRAMS
  ---------------------------------------------------------------------------
  The previous sketch did set_scale(1175) and tare() here, and the GUI then
  applied its own scale on top. Two calibrations in series, neither aware of
  the other — which is exactly the fault the project logbook already recorded
  once, when weightscale/wdisplay.py divided the same stream by a hard-coded
  2.44 and the two tools disagreed about what a gram was.

  A calibration needs ONE owner. It is the GUI, because that is where the
  known masses are entered, where the fit is computed, where the result is
  saved (labdata/loadcell_cal.json) and where it gets stamped into every run
  CSV. This sketch is now a dumb sensor: it reports what the ADC saw.

  NO tare() AT BOOT, either. A boot-time tare silently zeroes whatever happens
  to be resting on the cell at power-up — the arm, a fixture, a preload — and
  the offset it captures is different every power cycle. That makes two runs
  non-comparable with nothing in either log to show why. The GUI's "Tare now"
  captures the offset deliberately and records it.

  ---------------------------------------------------------------------------
  SAMPLE RATE — the reason the old sketch was slower than it looked
  ---------------------------------------------------------------------------
  get_units(3) averages three conversions, and the HX711 runs at 10 SPS with
  its RATE pin low. Three conversions is ~300 ms, so a loop asking for them
  every 100 ms actually produced about 3.3 samples/s, not the 10 intended, and
  it BLOCKED inside get_units for most of that time.

  This version never blocks: it asks is_ready(), and takes one conversion when
  one is there. That gives the HX711's true rate — 10 SPS as wired, or 80 SPS
  if you tie the module's RATE pin to VCC, which is worth doing. The GUI wants
  samples, not pre-averaged ones: it computes trimmed means itself, and its
  settle check needs at least 6 samples in a 2 s window to tell a drifting
  reading from a steady one. At 3.3 Hz that check is marginal.

  Averaging here would also throw away the thing the GUI's robust_mean is for:
  a mean is wrecked by one outlier, a trimmed mean is not, and the outliers
  have to still be present for the trimming to do anything.

  ---------------------------------------------------------------------------
  OUTPUT FORMAT — one numeric line per sample
  ---------------------------------------------------------------------------
      <raw>                e.g.  1046233
      <raw>,<tempC>        if SEND_TEMP is enabled

  Print NOTHING else on this port. The GUI pulls numbers out of each line with
  a regex and takes the first one as the reading, so a friendly banner like
  "HX711 ready v1.0" would be parsed as a sample of 711 with a temperature of
  1.0. (The GUI now also discards any line containing letters, but do not rely
  on that — a board flashed with an older GUI would swallow it.) Diagnostics,
  if you must, go on a second serial port.

  ---------------------------------------------------------------------------
  FIRST-TIME SETUP IN THE GUI
  ---------------------------------------------------------------------------
  Your old calibrationFactor of 1175 carries straight over: HX711 grams were
  (raw - offset)/1175, so the equivalent GUI scale is 1/1175 = 0.00085106
  g per raw count. Diagnostics tab -> Load cell calibration -> Manual, type
  that in, press Apply typed, then "Tare now" with the cell empty.

  Then check it against real masses. Multi-point mode, with the empty cell as
  a 0 g point, is the one to trust: it estimates the offset instead of
  assuming it is zero.
*/

#include <HX711.h>

// ---- Load cell pins (unchanged from the previous sketch) ----
const int LOADCELL_DOUT_PIN = 2;
const int LOADCELL_SCK_PIN  = 3;

// ---- Optional second number: temperature ----
// The driver board now reads a 100k NTC on its own GPIO3, and the GUI prefers
// that source because it shares a clock with Iq. This is the fallback for a
// board with no bead fitted. 0 = send the load cell only.
#define SEND_TEMP      0
#define TEMP_PIN       A0
#define TEMP_VREF      5.0f      // 3.3f on a 3.3 V board
#define TEMP_R_FIXED   10000.0f  // divider resistor to GND
#define TEMP_R25       100000.0f // NTC nominal at 25 C
#define TEMP_BETA      3950.0f
// Wiring matches the driver board: VCC -[NTC]- TEMP_PIN -[R_FIXED]- GND

HX711 scale;

// The HX711 can simply not be there — unplugged, a broken DT wire, an
// unpowered module. read() would then block forever and the sketch would go
// silent with no way to tell that apart from "no force". Bound the wait and
// keep the loop alive.
const unsigned long READY_TIMEOUT_MS = 250;

#if SEND_TEMP
float readTempC() {
  int adc = analogRead(TEMP_PIN);
  float v = adc * (TEMP_VREF / 1023.0f);
  if (v < 0.05f || v > TEMP_VREF - 0.05f) return NAN;   // open or shorted
  float r = TEMP_R_FIXED * (TEMP_VREF / v - 1.0f);
  float inv = 1.0f / 298.15f + log(r / TEMP_R25) / TEMP_BETA;
  float t = 1.0f / inv - 273.15f;
  return (t > -40.0f && t < 200.0f) ? t : NAN;
}
#endif

void setup() {
  Serial.begin(115200);
  scale.begin(LOADCELL_DOUT_PIN, LOADCELL_SCK_PIN);
  // Deliberately: no set_scale(), no tare(). See the header.
  // set_scale(1) and set_offset(0) make get_value()/get_units() identities,
  // so even if something calls them later the numbers stay raw.
  scale.set_scale(1.0f);
  scale.set_offset(0);
}

void loop() {
  // Non-blocking: take a conversion only when the HX711 has one waiting.
  if (!scale.wait_ready_timeout(READY_TIMEOUT_MS)) {
    return;                      // module absent or asleep — say nothing
  }

  long raw = scale.read();       // one conversion, no averaging

  Serial.print(raw);
#if SEND_TEMP
  float t = readTempC();
  if (!isnan(t)) {
    Serial.print(',');
    Serial.print(t, 1);
  }
#endif
  Serial.println();
}
