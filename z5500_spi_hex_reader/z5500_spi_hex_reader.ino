/*
 * Logitech Z-5500 -> HD44780 20x2 bridge
 * Arduino Uno / Pro Mini ATmega328P (5 V or 3.3 V, matched signal levels)
 *
 * Pod -> Arduino: CS D10, MOSI D11, SCK D13, common GND.
 * LCD: RS D2, E D3, DB4..DB7 D4..D7, RW GND.
 *
 * SPI slave mode 3 and CS polarity are preserved from the user's working setup.
 * Do not connect 5 V pod signals directly to a 3.3 V Pro Mini.
 */
#include <Arduino.h>
#include <SPI.h>
#include <LiquidCrystal.h>
#include <util/atomic.h>

// 0 = LCD operation, 1 = raw SPI log (LCD not updated)
#define DEBUG_PRINT_FRAMES 0
// Set to 1 to report overruns periodically alongside LCD operation.
#define SERIAL_DIAGNOSTICS 0

// Exact UART divider on ATmega328P at both 8 MHz and 16 MHz.
#define DEBUG_BAUD 250000UL

static LiquidCrystal lcd(2, 3, 4, 5, 6, 7);

// Each ring entry is TWO bytes instead of three:
// byte 0: first payload byte (high nibble only), bit 0 = 1 for data / 0 for command
// byte 1: second payload byte (high nibble only).
// The original SPI frame on the wire is still exactly F8/FA xx yy (three bytes).
struct SpiEvent {
  uint8_t hi;
  uint8_t lo;
};

// 256 * 2 = 512 B SRAM; uint8_t indices wrap naturally (255 usable entries).
static volatile SpiEvent spiQueue[256];
static volatile uint8_t queueHead = 0;
static volatile uint8_t queueTail = 0;

static volatile uint8_t ssWasHigh = 0;
static volatile uint8_t frameActive = 0;
static volatile uint8_t frameLength = 0;
static volatile uint8_t frameData[3];
static volatile uint16_t droppedEvents = 0;
static volatile uint16_t invalidFrames = 0;

// Only the ISR writes head; only loop() writes tail.
static inline void captureByte(uint8_t value)
{
  if (!frameActive) return;
  if (frameLength < 3) frameData[frameLength] = value;
  if (frameLength != 255) ++frameLength;
}

static inline void finishFrame()
{
  if (frameLength == 3 &&
      (frameData[0] == 0xF8 || frameData[0] == 0xFA) &&
      ((frameData[1] | frameData[2]) & 0x0F) == 0) {
    uint8_t next = (uint8_t)(queueHead + 1);
    if (next != queueTail) {
      spiQueue[queueHead].hi = (frameData[1] & 0xF0) |
                               (frameData[0] == 0xFA ? 1 : 0);
      spiQueue[queueHead].lo = frameData[2] & 0xF0;
      queueHead = next;  // Publish after writing both bytes.
    } else {
      ++droppedEvents;
    }
  } else if (frameLength != 0) {
    ++invalidFrames;
  }
  frameActive = 0;
}

static bool popEvent(SpiEvent &ev)
{
  bool available = false;
  ATOMIC_BLOCK(ATOMIC_RESTORESTATE) {
    if (queueTail != queueHead) {
      ev.hi = spiQueue[queueTail].hi;
      ev.lo = spiQueue[queueTail].lo;
      ++queueTail;  // uint8_t rollover is modulo 256.
      available = true;
    }
  }
  return available;
}

// Reverses only the meaningful four transmitted bits.
static inline uint8_t reverseNibble(uint8_t b)
{
  uint8_t n = b >> 4;
  return ((n & 1) << 3) | ((n & 2) << 1) |
         ((n & 4) >> 1) | ((n & 8) >> 3);
}

static inline uint8_t decodePayload(const SpiEvent &ev)
{
  return reverseNibble(ev.hi & 0xF0) |
         (reverseNibble(ev.lo) << 4);
}

#if DEBUG_PRINT_FRAMES
static void printHex(uint8_t b)
{
  if (b < 16) Serial.write('0');
  Serial.print(b, HEX);
}

static void printRaw(const SpiEvent &ev)
{
  Serial.print((ev.hi & 1) ? F("FA ") : F("F8 "));
  printHex(ev.hi & 0xF0);
  Serial.write(' ');
  printHex(ev.lo);
  Serial.println();
}
#else
// -----------------------------------------------------
// Virtual display: writes from the pod modify this RAM,
// not the comparatively slow physical HD44780.
// -----------------------------------------------------
static uint8_t desiredScreen[40];
static uint8_t displayedScreen[40];
static uint8_t renderStart = 0;
static uint32_t lastTrafficMs = 0;

static bool inCgram = false;
static uint8_t cgramAddress = 0;
static uint8_t ddramAddress = 0;
static bool incrementAddress = true;
static bool displayWanted = true;
static bool displayActive = true;

// Fallback glyphs retained from the latest user's sketch.
// Incoming complete CGRAM definitions will REPLACE them dynamically.
static uint8_t glyphs[8][8] = {
  {0x00,0x00,0x00,0x04,0x00,0x00,0x00,0x00}, // slot 0
  {0x1F,0x1F,0x1F,0x1F,0x1F,0x1F,0x1F,0x1F}, // slot 1
  {0x10,0x10,0x10,0x10,0x10,0x10,0x10,0x10}, // slot 2
  {0x01,0x01,0x01,0x01,0x01,0x00,0x1F,0x00}, // slot 3
  {0x04,0x04,0x04,0x04,0x04,0x0E,0x1F,0x00}, // slot 4
  {0x1F,0x13,0x11,0x11,0x11,0x13,0x1F,0x00}, // slot 5
  {0x1F,0x19,0x11,0x11,0x11,0x19,0x1F,0x00}, // slot 6
  {0x1F,0x0A,0x0A,0x0A,0x0A,0x0A,0x1F,0x00}  // slot 7
};

// Store incoming glyphs separately until all eight rows have arrived.
static uint8_t incomingGlyphs[8][8];
static uint8_t receivedRows[8];
static uint8_t glyphsToUpload = 0;

// The original pod uses contiguous visible coordinates 0..39,
// with the second row starting at DDRAM address 0x14 (command 0x94).
// Standard 0x40..0x53 second-row addresses are accepted too.
static inline int8_t visibleCell(uint8_t address)
{
  // Z-5500 uses contiguous addresses:
    // 0x00 - 0x13 = first LCD row
    // 0x14 - 0x27 = second LCD row

    if (address <= 0x27) {
        return (int8_t)address;
    }

    // Ignore addresses outside the visible 40 cells.
    return -1;
}

static void advanceDdram()
{
  if (incrementAddress) {
    if (ddramAddress == 0x27) ddramAddress = 0x40;
    else if (ddramAddress == 0x67) ddramAddress = 0x00;
    else ++ddramAddress;
  } else {
    if (ddramAddress == 0x40) ddramAddress = 0x27;
    else if (ddramAddress == 0x00) ddramAddress = 0x67;
    else --ddramAddress;
  }
}

static void clearVirtualScreen()
{
  for (uint8_t i = 0; i < 40; ++i) desiredScreen[i] = ' ';
}

static void processCommand(uint8_t cmd)
{
  if (cmd == 0x01) {  // Clear display
    clearVirtualScreen();
    // The pod is starting a new screen: redraw all 40 cells even
    // if the virtual content matches the previous snapshot.
    for (uint8_t i = 0; i < 40; ++i) displayedScreen[i] = 0xFF;
    ddramAddress = 0;
    inCgram = false;
    incrementAddress = true;
    return;
  }
  if (cmd == 0x02) {  // Return home
    ddramAddress = 0;
    inCgram = false;
    return;
  }
  if ((cmd & 0xFC) == 0x04) {  // Entry mode
    incrementAddress = (cmd & 0x02) != 0;
    return;
  }
  if ((cmd & 0xF8) == 0x08) {  // Display control
    displayWanted = (cmd & 0x04) != 0;
    return;
  }
  if ((cmd & 0xC0) == 0x40) {  // Set CGRAM address
    inCgram = true;
    cgramAddress = cmd & 0x3F;
    // Start a fresh definition; never combine fragments across blocks.
    for (uint8_t i = 0; i < 8; ++i) receivedRows[i] = 0;
    return;
  }
  if (cmd & 0x80) {  // Set DDRAM address
    inCgram = false;
    ddramAddress = cmd & 0x7F;
    return;
  }
  // Cursor/display shift commands (0x10..0x1F) are not yet emulated.
}

static void processData(uint8_t value)
{
  if (inCgram) {
    uint8_t slot = (cgramAddress >> 3) & 7;
    uint8_t row = cgramAddress & 7;
    incomingGlyphs[slot][row] = value & 0x1F;
    receivedRows[slot] |= (uint8_t)(1 << row);

    if (receivedRows[slot] == 0xFF) {
      bool changed = false;
      for (uint8_t i = 0; i < 8; ++i) {
        uint8_t pix = incomingGlyphs[slot][i];
        if (glyphs[slot][i] != pix) changed = true;
        glyphs[slot][i] = pix;
      }
      if (changed) glyphsToUpload |= (uint8_t)(1 << slot);
      receivedRows[slot] = 0;
    }
    cgramAddress = (uint8_t)((cgramAddress + (incrementAddress ? 1 : 63)) & 0x3F);
    return;
  }

  int8_t cell = visibleCell(ddramAddress);
  if (cell >= 0) {
    // All custom codes 0..7 are sent as codes, without remapping.
    // Space 0x20 is retained; don't trim leading blanks or center text.
    if (value == 0x81) value = '1';
    if (value == 0x82) value = '2';
    if (value == 0x83) value = '3';

    desiredScreen[(uint8_t)cell] = (value <= 7 || (value >= 0x20 && value <= 0x7E)) ? value : '?';
  }
  advanceDdram();
}

static inline void handleEvent(const SpiEvent &ev)
{
  uint8_t value = decodePayload(ev);
  if (ev.hi & 1) processData(value);
  else processCommand(value);
}

// One small update per loop, only when the SPI burst has gone quiet.
// Even after this function returns, SPI capture keeps running in interrupts.
static void updateLcdStep()
{
  if (glyphsToUpload) {
    for (uint8_t i = 0; i < 8; ++i) {
      uint8_t mask = (uint8_t)(1 << i);
      if (glyphsToUpload & mask) {
        glyphsToUpload &= (uint8_t)~mask;
        lcd.createChar(i, glyphs[i]);
        return;
      }
    }
  }

  if (displayActive != displayWanted) {
    if (displayWanted) lcd.display();
    else lcd.noDisplay();
    displayActive = displayWanted;
    return;
  }

  for (uint8_t scanned = 0; scanned < 40; ++scanned) {
    uint8_t index = (uint8_t)((renderStart + scanned) % 40);
    if (desiredScreen[index] == displayedScreen[index]) continue;

    uint8_t row = index / 20;
    lcd.setCursor(index % 20, row);

    // Write up to 4 adjacent changed characters, then return to SPI handling.
    for (uint8_t n = 0; n < 4 && index < (uint8_t)((row + 1) * 20); ++n) {
      if (desiredScreen[index] == displayedScreen[index]) break;
      uint8_t value = desiredScreen[index];
      lcd.write(value);
      displayedScreen[index] = value;
      ++index;
    }
    renderStart = index % 40;
    return;
  }
}
#endif  // !DEBUG_PRINT_FRAMES

void setup()
{
  pinMode(MOSI, INPUT); // D11
  pinMode(SCK, INPUT);  // D13
  pinMode(SS, INPUT);   // D10
  pinMode(MISO, INPUT); // D12 is NOT used

#if DEBUG_PRINT_FRAMES || SERIAL_DIAGNOSTICS
  Serial.begin(DEBUG_BAUD);
#endif

  // Start receiving as early as possible, before slow LCD initialization.
  ATOMIC_BLOCK(ATOMIC_RESTORESTATE) {
    queueHead = queueTail = 0;
    frameLength = 0;
    frameActive = 0;
    droppedEvents = invalidFrames = 0;
    ssWasHigh = (PINB & _BV(PB2)) != 0;
    PCMSK0 |= _BV(PCINT2);
    PCIFR |= _BV(PCIF0);
    PCICR |= _BV(PCIE0);
    SPCR = _BV(SPE) | _BV(CPOL) | _BV(CPHA); // Slave, mode 3
    SPI.attachInterrupt();
  }

#if !DEBUG_PRINT_FRAMES
  for (uint8_t i = 0; i < 40; ++i) {
    desiredScreen[i] = ' ';
    displayedScreen[i] = ' ';
  }
  for (uint8_t i = 0; i < 8; ++i) {
    receivedRows[i] = 0;
    for (uint8_t j = 0; j < 8; ++j)
      incomingGlyphs[i][j] = glyphs[i][j];
  }

  lcd.begin(20, 2);
  for (uint8_t i = 0; i < 8; ++i) lcd.createChar(i, glyphs[i]);
  lcd.clear();
  lastTrafficMs = millis();
#endif
}

ISR(SPI_STC_vect)
{
  captureByte(SPDR);
}

ISR(PCINT0_vect)
{
  uint8_t currentHigh = (PINB & _BV(PB2)) != 0;
  if (currentHigh == ssWasHigh) return;
  ssWasHigh = currentHigh;

  if (currentHigh) {
    // Finish the last byte if SS rises before SPI_STC ISR executes.
    if (SPSR & _BV(SPIF)) captureByte(SPDR);
    if (frameActive) finishFrame();
  } else {
    frameLength = 0;
    frameActive = 1;
  }
}

void loop()
{
  SpiEvent ev;
#if !DEBUG_PRINT_FRAMES
  bool received = false;
#endif

  while (popEvent(ev)) {
#if DEBUG_PRINT_FRAMES
    printRaw(ev);
#else
    received = true;
    handleEvent(ev);
#endif
  }

#if !DEBUG_PRINT_FRAMES
  if (received) lastTrafficMs = millis();
  if ((uint32_t)(millis() - lastTrafficMs) >= 8)
    updateLcdStep();
#endif

#if DEBUG_PRINT_FRAMES || SERIAL_DIAGNOSTICS
  static uint32_t previousReport = 0;
  if ((uint32_t)(millis() - previousReport) >= 1000) {
    previousReport = millis();
    uint16_t drops, invalid;
    ATOMIC_BLOCK(ATOMIC_RESTORESTATE) {
      drops = droppedEvents;
      invalid = invalidFrames;
    }
    Serial.print(F("! dropped=")); Serial.print(drops);
    Serial.print(F(" invalid=")); Serial.println(invalid);
#if SERIAL_DIAGNOSTICS && !DEBUG_PRINT_FRAMES
    // Show what the virtual 20x2 image contains.
    // Character slots 0..7 are printed as {0}..{7} on Serial.
    for (uint8_t row = 0; row < 2; ++row) {
      Serial.print(row == 0 ? F("R0: ") : F("R1: "));
      for (uint8_t col = 0; col < 20; ++col) {
        uint8_t c = desiredScreen[row * 20 + col];
        if (c <= 7) {
          Serial.write('{'); Serial.write('0' + c); Serial.write('}');
        } else {
          Serial.write(c);
        }
      }
      Serial.println();
    }
#endif
  }
#endif
}
