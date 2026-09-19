/*
  ESP32-S3 + HX711 + WIT Motion serial IMU -- Arduino IDE

  Install: "esp32 by Espressif Systems" board package and
           "HX711 Arduino Library" by Bogdan Necula (bogde).
  Board: your exact ESP32-S3 board, or ESP32S3 Dev Module for a generic board.
  Serial Monitor: 115200 baud. For the UART USB port, disable USB CDC On Boot.
  For the native USB port, enable USB CDC On Boot instead.

  Normal output has four fields: Roll_deg, Pitch_deg, Yaw_deg, and LoadCell.
  LoadCell_raw is ADC counts until taring and calibration are complete.
  LoadCell_g is grams after both are complete. nan means unavailable/invalid,
  including load-cell readings while a tare/calibration job is running.
  Command confirmations are printed only when t/c is sent.

  HX711: VCC -> 3V3, GND -> GND, DT -> GPIO4, SCK -> GPIO5.
  Load cell: excitation +/- -> E+/E-, signal +/- -> A+/A-.
  IMU: TX -> GPIO18 (ESP RX), RX -> GPIO17 (ESP TX), GND -> GND.
  IMPORTANT: IMU VCC voltage and electrical interface must be confirmed
  from its model. Direct GPIO wiring requires 3.3 V-compatible TTL signals.
  RS-232 models require an appropriate converter. Do not apply 5 V to GPIO.

  IMU ASSUMPTION: standard WIT 11-byte streaming binary UART protocol,
  header 0x55, angle packet 0x53, checksum = sum of first 10 bytes mod 256.
  This is NOT a driver for every WIT model. No configuration is sent to IMU.
  IMU_BAUD is 115200, matching the working setup in this conversation.

  Commands (Serial Monitor; any line-ending setting):
    t : remove load, hold still, then send t to zero using 20 samples.
    c : after t, apply KNOWN_MASS_G grams, wait to settle, then send c.
  Calibration is in RAM. Copy the printed factor into COUNTS_PER_GRAM
  below and re-upload to preserve it. Tare again after each restart.
  Mount the load cell correctly before calibration. This sketch reads
  sensors only; it does not control motors.

  References:
  https://github.com/bogde/HX711
  https://github.com/WITMOTION/WitStandardProtocol_JY901
*/

#include <Arduino.h>
#include <HX711.h>
#include <math.h>
#include <string.h>

constexpr int HX_DT = 4;
constexpr int HX_SCK = 5;
constexpr int IMU_RX = 18;  // Connect to IMU TX
constexpr int IMU_TX = 17;  // Connect to IMU RX; this sketch sends no commands
constexpr uint32_t IMU_BAUD = 115200;  // Must match your IMU
constexpr float KNOWN_MASS_G = 500.0f;  // CHANGE to your calibration mass
constexpr float COUNTS_PER_GRAM = 0.0f; // 0 = uncalibrated; retain sign
constexpr uint8_t AVERAGE_SAMPLES = 20;
constexpr uint32_t STALE_MS = 2000;

HX711 scale;
HardwareSerial imuSerial(1);

long rawLoad = 0;
double zeroOffset = 0;
float countsPerGram = COUNTS_PER_GRAM;
bool loadSeen = false, zeroSet = false, overload = false;
uint32_t lastLoadMs = 0;

// job: 0 = idle, 1 = tare, 2 = calibration
uint8_t job = 0, sampleCount = 0;
int64_t sampleSum = 0;
uint32_t jobStartMs = 0;

uint8_t packet[11];
uint8_t packetUsed = 0;
uint32_t imuBytes = 0, angleFrames = 0, lastAngleMs = 0;
float rollDeg = 0, pitchDeg = 0, yawDeg = 0;
bool angleSeen = false;

float decodeAngle(const uint8_t *p) {
  const uint16_t u = uint16_t(p[0]) | (uint16_t(p[1]) << 8);
  const int32_t signedValue = (u & 0x8000) ? int32_t(u) - 65536 : u;
  return signedValue * (180.0f / 32768.0f);
}

void acceptImuByte(uint8_t value) {
  ++imuBytes;
  if (packetUsed == 0 && value != 0x55) return;
  packet[packetUsed++] = value;
  if (packetUsed < sizeof(packet)) return;

  uint8_t checksum = 0;
  for (uint8_t i = 0; i < 10; ++i) checksum += packet[i];
  if (checksum == packet[10]) {
    if (packet[1] == 0x53) {
      rollDeg = decodeAngle(packet + 2);
      pitchDeg = decodeAngle(packet + 4);
      yawDeg = decodeAngle(packet + 6);
      lastAngleMs = millis();
      angleSeen = true;
      ++angleFrames;
    }
    packetUsed = 0;
  } else {
    // Recover after noise/dropped bytes without discarding a later header.
    uint8_t start = 1;
    while (start < sizeof(packet) && packet[start] != 0x55) ++start;
    packetUsed = sizeof(packet) - start;
    memmove(packet, packet + start, packetUsed);
  }
}

void startJob(uint8_t requestedJob) {
  if (job != 0) {
    Serial.println("Busy: wait for current measurement to finish.");
    return;
  }
  if (requestedJob == 2 && (!zeroSet || KNOWN_MASS_G <= 0)) {
    Serial.println("Tare first (t), and set a positive KNOWN_MASS_G.");
    return;
  }
  job = requestedJob;
  sampleSum = 0;
  sampleCount = 0;
  jobStartMs = millis();
  Serial.println(job == 1 ? "Taring: keep unloaded and still..."
                          : "Calibrating: keep known mass still...");
}

void readLoadCell() {
  if (scale.is_ready()) {
    rawLoad = scale.read(); // Read one ready conversion, no averaging wait.
    loadSeen = true;
    lastLoadMs = millis();
    overload = rawLoad == 8388607L || rawLoad == -8388608L;
    if (job != 0 && overload) {
      job = 0;
      Serial.println("Measurement cancelled: HX711 saturated. Check wiring/load.");
    }
    if (job != 0) {
      sampleSum += rawLoad;
      if (++sampleCount >= AVERAGE_SAMPLES) {
        const double average = double(sampleSum) / sampleCount;
        if (job == 1) {
          zeroOffset = average;
          zeroSet = true;
          Serial.println("Tare complete. Apply known mass, then send c to calibrate.");
        } else {
          const double delta = average - zeroOffset;
          if (fabs(delta) < 1.0) {
            Serial.println("Calibration failed: no measurable load change.");
          } else {
            countsPerGram = delta / KNOWN_MASS_G;
            Serial.print("Calibration complete. COUNTS_PER_GRAM = ");
            Serial.println(countsPerGram, 6);
          }
        }
        job = 0;
      }
    }
  }
  if (job != 0 && uint32_t(millis() - jobStartMs) > 5000) {
    job = 0;
    Serial.println("Measurement timed out: check HX711 power and wiring.");
  }
}

void printReadings() {
  const uint32_t now = millis();
  const bool anglesValid = angleSeen && uint32_t(now - lastAngleMs) <= STALE_MS;
  const bool loadValid = loadSeen && uint32_t(now - lastLoadMs) <= STALE_MS
                         && !overload && job == 0;
  const bool calibrated = zeroSet && countsPerGram != 0;

  Serial.print("Roll_deg: ");
  Serial.print(anglesValid ? rollDeg : NAN, 2);
  Serial.print(" | Pitch_deg: ");
  Serial.print(anglesValid ? pitchDeg : NAN, 2);
  Serial.print(" | Yaw_deg: ");
  Serial.print(anglesValid ? yawDeg : NAN, 2);
  Serial.print(calibrated ? " | LoadCell_g: " : " | LoadCell_raw: ");
  if (!loadValid) {
    Serial.println("nan");
  } else if (calibrated) {
    Serial.println((double(rawLoad) - zeroOffset) / countsPerGram, 2);
  } else {
    Serial.println(rawLoad);
  }
}

void setup() {
  Serial.begin(115200);
  // No indefinite while(!Serial): sensor reading also works without a PC.
  scale.begin(HX_DT, HX_SCK);
  imuSerial.setRxBufferSize(1024);
  imuSerial.begin(IMU_BAUD, SERIAL_8N1, IMU_RX, IMU_TX);
}

void loop() {
  // Bound each pass so continuous UART traffic cannot starve HX711/commands.
  for (int i = 0; i < 256 && imuSerial.available(); ++i) {
    acceptImuByte(uint8_t(imuSerial.read()));
  }
  for (int i = 0; i < 32 && Serial.available(); ++i) {
    const char command = char(Serial.read());
    if (command == 't' || command == 'T') startJob(1);
    if (command == 'c' || command == 'C') startJob(2);
  }
  readLoadCell();
  static uint32_t lastPrintMs = 0;
  if (uint32_t(millis() - lastPrintMs) >= 250) {
    lastPrintMs = millis();
    printReadings();
  }
  delay(1);
}
