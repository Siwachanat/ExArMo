/*
  ExArMo Lab - HX711 load cell bridge (kilograms)
  Streams calibrated kilograms at 115200 baud.
  Keep the load cell unloaded during startup tare.
  The receiver must treat readings as kg without applying another calibration.
*/

#include <HX711.h>

const int LOADCELL_DOUT_PIN = 2;
const int LOADCELL_SCK_PIN = 3;

HX711 scale;

// 1175 counts/gram * 1000 grams/kg = 1175000 counts/kg.
// Use a negative factor if added weight produces negative readings.
float CALIBRATION_FACTOR = 1175000.0;
const unsigned long READY_TIMEOUT_MS = 250;

void setup() {
  Serial.begin(115200);
  scale.begin(LOADCELL_DOUT_PIN, LOADCELL_SCK_PIN);
  scale.set_scale(CALIBRATION_FACTOR);

  // Zero the unloaded cell at each power-up or reset.
  scale.tare();
  delay(500);
}

void loop() {
  if (!scale.wait_ready_timeout(READY_TIMEOUT_MS)) {
    return;
  }

  float weight_kg = scale.get_units(1);
  Serial.println(weight_kg, 4);
}
