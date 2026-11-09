# BMS protection requirements

## Purpose and scope

The demo is the protection layer of a battery management system (BMS) for a pack of four lithium iron phosphate cells in series.  The Cortex-M7 back end compiles it to a flash image for the NUCLEO-F767ZI, and theorems cover the protection machine, the WebAssembly module of the verified compiler from which the back end works, and the image's run from reset.  The board sees only the bytes of USART3.  A bridge at the far end of the UART samples the pack's sensors and digital inputs, sends one record per scan, and drives three relays from the board's answers: the negative contactor (NEG), the precharge relay (PRE), and the positive contactor (POS).  In the demo a host program acts as the bridge and simulates the pack.

The first iteration covers cell overvoltage and undervoltage, overtemperature and undertemperature, charging outside its temperature range, and pack overcurrent in both directions, each against a limit taken from the cell's datasheet.  It also covers the range of every sensor, a check of the sum of the cell voltages against an independently measured pack voltage, control of the three relays with a precharge sequence, monitoring of the relays' auxiliary contacts, a stop input, a restart interlock with a reset edge, the supervisor's run request, and the communication checks of a black channel.  It leaves out state of charge and state of health, cell balancing, a real analog front end, CAN, thermal management, charger control, safety-rated hardware, and every theorem about real time.

## The channel

The UART, the ST-LINK's virtual COM port, USB, the host, and the bridge's transport form a black channel in the sense of IEC 61784-3: the safety measures run end to end, in the verified program and in the bridge's lease logic, and no property of the channel enters a safety claim.  The table lists the communication errors of IEC 61784-3 as OPC 10000-15 section 5.3 tabulates them, with this design's measures.  The board has no clock, so the bridge's lease, which expires a fixed time after the sampling of the record that an answer answers, bounds the age of the data on which a relay acts in either direction.

| Error | Measures |
|---|---|
| Corruption | CRC-32 over the link identifier and the record, the COBS and length checks |
| Unintended repetition | Sequence number, the bridge's rule that only the first answer to its latest record acts |
| Incorrect sequence | Sequence number |
| Loss | Sequence number, the bridge's lease and timeout |
| Unacceptable delay | The bridge's lease |
| Insertion | Sequence number, the overflow and length checks |
| Masquerade | Link identifier in the CRC, tag, sequence number |
| Addressing | Link identifier in the CRC |

The checks detect errors of the channel, and the leases bound how long a relay acts on data that the channel delivered late or not at all.  They cannot detect a bridge that sends a wrong value with a correct CRC, except through the check of the cell sum against the pack voltage when the two measurements take independent paths, as [what lies outside the theorems](#what-lies-outside-the-theorems) states.  A record that arrives intact from a bridge or a board whose link identifier has another CRC-32 value fails the CRC check, so it acts on no relay of this system except through the CRC's residual error.

## Wire format

### Framing

The framing of `LeanExe/Requests/Delimited.lean` carries both directions.  Each record is encoded with Consistent Overhead Byte Stuffing (COBS; Cheshire and Baker 1999) and followed by one `0x00`.  A segment is the sequence of bytes between two delimiters.  The framing ignores an empty segment and gives it no answer, and it treats a non-empty segment longer than 36 bytes, the encoded length of a scan record, as an overflow: it discards the segment's bytes up to the next delimiter.  It calls the machine once for each non-empty segment, with the decoded bytes, a decode error, or the overflow error, and it writes the machine's answer COBS-encoded and followed by `0x00`.  A record of fewer than 254 bytes encodes to its length plus one, so a scan record takes 37 bytes on the wire and an answer 19.

### USART3 and the initialization

The window that receives a delimiter decodes the segment, computes the CRCs, runs the machine, and encodes the answer, and the polling windows only store bytes.  Under the bridge's lockstep rule (BR3) no byte arrives while that long window runs or while the answer is sent.  A byte that arrives then, through a channel error, finds USART3's single receive register full.

The image's initialization performs the accesses of the board's list `init` of `LeanExe/M7/Board.lean` with one more write: `0x00001000`, `OVRDIS`, to `USART_CR3` at `0x40004808`, after the write of `USART_BRR` and before the write of `USART_CR1` that sets `UE`, since `USART_CR3` takes the bit only while `UE` is 0 (RM0410 section 34.8.3).  With `OVRDIS` clear, a byte that arrives while `RXNE` is set sets `ORE`, and USART3 then delivers no byte until a write of `ORECF` to `USART_ICR`, which a program confined to `USART_ISR`, `USART_RDR`, and `USART_TDR` cannot make, so one overrun would stop reception until a reset.  With `OVRDIS` set, `ORE` stays 0, a byte that arrives while `RXNE` is set replaces the byte in `USART_RDR`, and reception continues, as tests on the board confirmed.  An overrun then loses the byte that `USART_RDR` held and every byte that arrives while `RXNE` is set except the last.  The record checks report the loss as a communication fault, except the loss of a delimiter alone, which BR4 repairs.

### Scan record

The bridge sends one scan record for each scan.  Multi-byte integers are big-endian, and signed integers are two's complement.  The raw record has 35 bytes:

| Offset | Size | Field | Type and unit |
|---|---|---|---|
| 0 | 1 | Tag, `0x10` | `u8` |
| 1 | 4 | Sequence number | `u32` |
| 5 | 8 | Cells 0 to 3 | `u16` each, mV |
| 13 | 4 | Temperature sensors 0 and 1 | `i16` each, tenths of a degree Celsius |
| 17 | 4 | Pack current, positive while charging | `i32`, mA |
| 21 | 4 | Pack voltage, measured independently of the cells | `u32`, mV |
| 25 | 4 | Bus voltage, on the load side of the contactors | `u32`, mV |
| 29 | 2 | Digital-input word | `u16` |
| 31 | 4 | CRC of bytes 0 to 30 | `u32` |

| Bit of the digital word | Name | Meaning |
|---|---|---|
| 0 | `AUX_NEG` | 1 when the negative contactor's auxiliary contact reports closed |
| 1 | `AUX_PRE` | 1 when the precharge relay's auxiliary contact reports closed |
| 2 | `AUX_POS` | 1 when the positive contactor's auxiliary contact reports closed |
| 3 | `STOP_OK` | 1 when the stop circuit is closed; the button is a normally closed contact, so 0 means a stop demand or a broken circuit |
| 4 | `RESET` | 1 while the reset button is pressed |
| 5 | `RUN` | 1 while the supervisor requests operation, 0 for standby |
| 6 to 15 | | Reserved, 0 |

Bits 0 to 2 form the auxiliary word, whose bit `r` belongs to the relay of bit `r` of the permit.  The stop circuit is a single channel, read through `STOP_OK` alone.  A reserved bit set to 1 fails check 7.

### Answer

The board answers each non-empty segment with one answer of 17 raw bytes.  Its integers are big-endian, as in the scan record, and its CRC covers the link identifier and bytes 0 to 12.  The bridge reads the permit from byte 9.

| Offset | Size | Field | Type |
|---|---|---|---|
| 0 | 1 | Tag, `0x80` | `u8` |
| 1 | 4 | Board sequence number | `u32` |
| 5 | 4 | Sequence number of the record answered, or `0xFFFFFFFF` | `u32` |
| 9 | 1 | Permit | `u8` |
| 10 | 1 | State | `u8` |
| 11 | 2 | Diagnostic code | `u16` |
| 13 | 4 | CRC of bytes 0 to 12 | `u32` |

The board sequence number is 0 in the first answer after a board reset and grows by one with each answer, modulo 2^32.  The answered field holds the record's sequence number when the segment decodes to 35 bytes whose CRC matches, and `0xFFFFFFFF` otherwise.  Bit 0 of the permit permits NEG, bit 1 PRE, and bit 2 POS, and bits 3 to 7 are 0.  The state codes are 0 `RESET_REQUIRED`, 1 `STANDBY`, 2 `PRECHARGE`, 3 `NORMAL`, and 4 `FAULT`.

### CRC and link identifier

The CRC field of either record holds the CRC-32 of ITU-T V.42, the value that `zlib.crc32` reports, of the link identifier followed by the record's bytes before the field: `zlib.crc32(raw[:-4], zlib.crc32(LINK))`, which equals `zlib.crc32(LINK + raw[:-4])`.  The link identifier `LINK` is a byte string that the board's profile and the bridge share and that no record carries, the 16 ASCII bytes `LeanExe-BMS-0001` in the demo, whose CRC-32 is `0xfe3f9f15`.  The identifier enters the CRC only through the register value that its CRC-32 gives, so two identifiers with equal CRC-32 act as one link, and the identifiers of one installation must have distinct CRC-32 values.  The specification computes the CRC with `crc32Eval` of `Library/Hashing/Crc/Division.lean` over the identifier's bytes followed by the record's, and `crc32_eq` equates it with the transcription `Spec.crc32` of `Library/Hashing/Crc/Spec.lean`, which is not computable.

### Test vectors

`uv run tests/baremetal/bms_proto.py vectors` computes the two vectors below.  The scan record has sequence number 7, cells of 3,300, 3,301, 3,299, and 3,302 mV, temperatures of 25.0 and 24.5 °C, a discharge current of 10,000 mA, a pack voltage of 13,202 mV, a bus voltage of 13,150 mV, and the digital word `0x002D`: NEG and POS closed, the stop circuit closed, and `RUN`.  The answer has board sequence number 8 and answers record 7 with permit `0x05` (NEG and POS), state 3 (`NORMAL`), and diagnostic code 0.  Without the link identifier the two CRCs would be `0xdf2e3f66` and `0x937e53f6`.

```
scan raw:    10 00 00 00 07 0c e4 0c e5 0c e3 0c e6 00 fa 00 f5 ff ff d8 f0 00 00 33 92
             00 00 33 5e 00 2d 56 f3 9e 0d                         (35 bytes, CRC 0x56f39e0d)
scan wire:   02 10 01 01 0a 07 0c e4 0c e5 0c e3 0c e6 02 fa 06 f5 ff ff d8 f0 01 03 33
             92 01 03 33 5e 06 2d 56 f3 9e 0d 00                                (37 bytes)
answer raw:  80 00 00 00 08 00 00 00 07 05 03 00 00 91 0a 58 a2   (17 bytes, CRC 0x910a58a2)
answer wire: 02 80 01 01 02 08 01 01 04 07 05 03 01 05 91 0a 58 a2 00             (19 bytes)
```

### Line time

At 4,800 baud with 8 data bits, no parity, and one stop bit, a byte takes 10 bit times, 2.083 ms.  A scan record takes 77.083 ms on the wire and an answer 39.583 ms, so one exchange takes 116.667 ms plus the board's long window, the bridge's sampling, and the latency of the host and the virtual COM port, which no run has measured.  Each byte takes two polling windows, a status read and the read of `USART_RDR`, so each polling window must end within half a byte time, 16,667 cycles at the 16 MHz of the internal oscillator.

## Profile

The profile is compiled into the module as constants.  The cell limits come from EVE Energy's LF280K product specification, file LF280K-72174, version A of 16 January 2021, section 4, for a cell of 280 Ah and 3.2 V, and the pack has the four cells in series, so the pack current is the cell current.  The specification gives its temperature ranges as ambient temperatures and calls the 1C discharge current and the 2.5 V cut-off preference values, and applying them to the readings of the cell sensors as the board's only limits is a design choice.  The values marked as design choices have the reasons that [the review](review.md) records.

| Parameter | Meaning | Value | Source |
|---|---|---|---|
| `V_max` | Cell overvoltage limit | 3,650 mV | Section 4, item 5: charge cut-off voltage 3.65 V |
| `V_min` | Cell undervoltage limit | 2,500 mV | Section 4, item 6: discharge cut-off voltage 2.5 V |
| `T_max` | Overtemperature limit | 55.0 °C | Section 4, items 9 and 10: charging 0 to 55 °C, discharging −20 to 55 °C |
| `T_min` | Undertemperature limit | −20.0 °C | Section 4, item 10 |
| `T_chg_min` | Lowest temperature for charging | 0.0 °C | Section 4, item 9 |
| `T_chg_max` | Highest temperature for charging | 45.0 °C | Design choice: item 5 allows 1C between 0 and 45 °C and states no current from 45 to 55 °C |
| `I_chg_max` | Charge current limit | 280,000 mA | Section 4, item 5: maximum charge current 1C |
| `I_dis_max` | Discharge current limit | 280,000 mA | Section 4, item 6: maximum discharge current 1C |
| `I_chg_detect` | Current above which the pack counts as charging | 2,800 mA | Design choice |
| `V_sens_lo`, `V_sens_hi` | Valid range of a cell reading | 1,000 to 4,500 mV | Design choice |
| `T_sens_lo`, `T_sens_hi` | Valid range of a temperature reading | −40.0 to 125.0 °C | Design choice |
| `P_sens_hi` | Upper end of the valid range of the pack and bus readings | 20,000 mV | Design choice |
| `tol_sum` | Allowed difference between the sum of the cells and the pack voltage | 300 mV | Design choice |
| `tol_pc` | Allowed difference between the bus and pack voltages that completes precharge | 500 mV | Design choice |
| `N_pc` | Records allowed in `PRECHARGE` | 10 | Design choice |
| `D_edm` | Records in which a relay's auxiliary contact may disagree after its permit bit changes | 2 | Design choice |
| `LINK` | Link identifier | `LeanExe-BMS-0001` | Design choice |

Temperatures enter the machine in tenths of a degree, so `T_max` is 550 and `T_min` is −200.  A reading equal to a limit passes, and a reading beyond it fails.  Signed fields compare as two's-complement integers, so a discharge beyond the limit is a current below −280,000 mA.

## The machine

The machine is a function `M → Except Err (List UInt8) → M × List UInt8`, which the framing calls once for each non-empty segment.  Its answer is the 17 raw bytes of an answer record, which the framing encodes.  The machine has no clock, so every rule about time belongs to the bridge.

### State

| Field | Meaning | After a board reset |
|---|---|---|
| `state` | Protection state | `RESET_REQUIRED` |
| `diag` | Diagnostic code | `0x0001` |
| `synced` | Whether the segment before was a record that passed the length, CRC, and tag checks | false |
| `expected` | That record's sequence number plus one, modulo 2^32 | 0 |
| `answers` | Board sequence number of the next answer | 0 |
| `prevReset` | `RESET` bit of the last record that passed the communication checks | 1 |
| `age` | Each relay's age, up to `D_edm` | 0 for each relay |
| `pcCount` | Records in `PRECHARGE` without the precharge condition | 0 |
| `first` | Whether no segment has been answered since the board reset | true |

The permit is the function of the state that the table below gives.  The permit in force for a segment is the permit of the state before it, which the previous answer carried.  A relay's age at segment `t` is 0 for `t` = 0, and otherwise the number of records that passed the communication checks among segments `c + 1` to `t − 1`, where `c` is the last segment before `t` whose answer's bit for the relay differs from the bit of the answer before it, segment 0 counting as such a segment for every relay.  The age therefore depends only on the segments and answers before `t`, and the auxiliary contacts of relays that the bridge held closed before a board reset may open during the first records after it.

| State | Permit |
|---|---|
| `RESET_REQUIRED`, `STANDBY`, `FAULT` | `0x00` |
| `PRECHARGE` | `0x03`: NEG and PRE |
| `NORMAL` | `0x05`: NEG and POS |

### Checks

The checks run in the order of the table, and the first that fails gives the diagnostic code.  A record is good when it passes the length, CRC, and tag checks, and it passes the communication checks, checks 1 to 6, when it is good and, if `synced` holds, its sequence number equals `expected`.  A good record with `synced` false synchronizes: its sequence number is not checked.  The content checks, 7 to 17, apply only to records that pass the communication checks.

| Order | Check: the segment fails when | Code |
|---|---|---|
| 1 | The framing reports a decode error | `0x1001` |
| 2 | The framing reports an overflow | `0x1002` |
| 3 | The decoded record does not have 35 bytes | `0x1003` |
| 4 | Bytes 31 to 34 differ from the CRC of `LINK` followed by bytes 0 to 30 | `0x1004` |
| 5 | Byte 0 is not `0x10` | `0x1005` |
| 6 | `synced` holds and the sequence number differs from `expected` | `0x1006` |
| 7 | A reserved bit of the digital word is 1 | `0x1007` |
| 8 | A cell lies outside `V_sens_lo` to `V_sens_hi`, a temperature outside `T_sens_lo` to `T_sens_hi`, or the pack or bus voltage above `P_sens_hi` | `0x2001` |
| 9 | A cell exceeds `V_max` | `0x2002` |
| 10 | A cell lies below `V_min` | `0x2003` |
| 11 | A temperature exceeds `T_max` | `0x2004` |
| 12 | A temperature lies below `T_min` | `0x2005` |
| 13 | The current exceeds `I_chg_max` | `0x2006` |
| 14 | The current lies below `−I_dis_max` | `0x2007` |
| 15 | The current exceeds `I_chg_detect` and a temperature lies outside `T_chg_min` to `T_chg_max` | `0x2008` |
| 16 | The sum of the four cells differs from the pack voltage by more than `tol_sum` | `0x2009` |
| 17 | An auxiliary bit differs from the relay's bit in the permit in force, and the relay's age is at least `D_edm` | `0x3001` |

Check 17 is the auxiliary-contact check.  It lets a relay whose permit bit changed disagree for the `D_edm` records that follow the change, the time its contacts need to move, and it requires the relay to agree at every later record.  In `NORMAL`, NEG's permit bit has not changed since the start of precharge, so a record that reports NEG open fails at once unless the start lies within `D_edm` records.

### Transitions

The machine processes a segment by the rules below, in order.  A rule's outcome sets the next state and code, and the fields that no rule names keep their values.  When the next state is `FAULT` and the state before was not, the code becomes the failing check's code, or `0x3002` for the precharge timeout, and in `FAULT` the code never changes.

1. A segment that fails a check from 1 to 5 leads to `FAULT` and sets `synced` false.
2. A good record sets `expected` to its sequence number plus one and `synced` true.  If it fails check 6, it leads to `FAULT`, and rules 3 to 5 do not apply.
3. A record that passes the communication checks sets `prevReset` to its `RESET` bit, after the rules below have read the old value.  If it fails a check from 7 to 17, it leads to `FAULT`.
4. A record that passes every check with `STOP_OK` 0 leads from `STANDBY`, `PRECHARGE`, or `NORMAL` to `RESET_REQUIRED` with code `0x5001`, and it keeps the state and the code in `RESET_REQUIRED` or `FAULT`.
5. A record that passes every check with `STOP_OK` 1 follows the table.

| State | Condition, the first that holds | Next state and code |
|---|---|---|
| `RESET_REQUIRED`, `FAULT` | `synced` held before the record, `prevReset` is 0, `RESET` is 1, `RUN` is 0, and the auxiliary word is 0: a reset acceptance | `STANDBY`, `0x0000` |
| `RESET_REQUIRED`, `FAULT` | Otherwise | Unchanged |
| `STANDBY` | `RUN` is 1 and the auxiliary word is 0: a start | `PRECHARGE`, with `pcCount` 0 |
| `STANDBY` | Otherwise | Unchanged |
| `PRECHARGE` | `RUN` is 0 | `STANDBY` |
| `PRECHARGE` | The bus and pack voltages differ by at most `tol_pc`, and `AUX_NEG` and `AUX_PRE` are 1: the precharge condition | `NORMAL` |
| `PRECHARGE` | `pcCount + 1 ≥ N_pc` | `FAULT`, `0x3002` |
| `PRECHARGE` | Otherwise | Unchanged, with `pcCount + 1` |
| `NORMAL` | `RUN` is 0 | `STANDBY` |
| `NORMAL` | Otherwise | Unchanged |

After these rules, a relay gets age 0 when the next state's permit differs in its bit from the permit in force, and every relay gets age 0 at segment 0.  Otherwise a record that passed the communication checks raises the relay's age by one, up to `D_edm`.  The answer carries `answers`, the answered sequence number, the permit and code of the next state, and its CRC, and `answers` then grows by one.

The code is 0 in `STANDBY`, `PRECHARGE`, and `NORMAL`, `0x0001` or `0x5001` in `RESET_REQUIRED`, and a fault code in `FAULT`.  A synchronizing record never accepts a reset, so the expected sequence number of every reset acceptance comes from the record before it.  A reset acceptance needs `RUN` 0, so a reset never starts precharge by itself, and a start needs a record with `RUN` 1 after it.  The transition from `NORMAL` to `STANDBY` opens the contactors at once, whatever the current.

### Diagnostic codes

| Code | Meaning |
|---|---|
| `0x0000` | No fault |
| `0x0001` | Board reset; no reset accepted since |
| `0x1001` | COBS decode error |
| `0x1002` | Segment overflow |
| `0x1003` | Length other than 35 bytes |
| `0x1004` | CRC mismatch |
| `0x1005` | Tag other than `0x10` |
| `0x1006` | Sequence number other than the expected one |
| `0x1007` | Nonzero reserved bit |
| `0x2001` | Reading outside its sensor range |
| `0x2002`, `0x2003` | Cell overvoltage, cell undervoltage |
| `0x2004`, `0x2005` | Overtemperature, undertemperature |
| `0x2006`, `0x2007` | Charge overcurrent, discharge overcurrent |
| `0x2008` | Charging outside `T_chg_min` to `T_chg_max` |
| `0x2009` | Sum of the cells disagrees with the pack voltage |
| `0x3001` | Auxiliary contact disagrees with the permit: a welded or failed relay, or relays that the bridge released |
| `0x3002` | Precharge timeout |
| `0x5001` | Stop demanded, which is not a fault |

Codes `0x1001` to `0x1006` are communication faults.  They latch like every other fault, so the answer to the faulty segment and every later answer carry permit 0 until a reset acceptance.  The resynchronization of rules 1 and 2 keeps them from failing later records: after a segment that fails a check from 1 to 5, the next good record synchronizes, and after a sequence fault the next record is checked against the faulty record's number plus one.

### Lost, inserted, and changed bytes

A single lost, inserted, or changed byte damages only the segments that contain it, since the next delimiter ends the segment.  COBS decoding of a segment of `k` bytes gives at most `k − 1` bytes, so a scan record that loses a byte other than its delimiter decodes to at most 34 bytes or fails to decode, and a record that gains a nonzero byte becomes a segment of 37 bytes, an overflow.  `uv run tests/baremetal/bms_proto.py faults` applies every single-byte fault to the wire bytes of the test vector's scan record and follows it with the bytes that BR3 and BR4 make the bridge send next, and it gives these outcomes:

| Fault | Outcomes |
|---|---|
| Lost byte inside the record | `0x1001` (24 positions) or `0x1003` (12) |
| Lost delimiter | No answer within `T_ans`; after the bridge's `0x00` of BR4 the record is answered normally |
| Inserted nonzero byte inside the record or before its delimiter | `0x1002` |
| Inserted nonzero byte after the delimiter | The record is answered normally, and the byte joins the next record's segment, which gives `0x1002` |
| Inserted `0x00` inside the record | Two segments, each `0x1001` or `0x1003` |
| Inserted `0x00` next to a delimiter | An empty segment, which gets no answer |
| Changed data byte | `0x1004` |
| Changed COBS code byte | `0x1001` (2,735 of 2,794) or `0x1004` (59) |
| Changed delimiter | `0x1002` |
| Byte changed to `0x00` | Two segments, each `0x1001` or `0x1003`, or one `0x1001` when the first or last byte changes |

In every case the record after the damaged segments passes the communication checks, by synchronizing or by its sequence number.  The CRC detects every change confined to one byte of the decoded record, since the generator has degree 32 and a nonzero constant term, while a changed code byte moves zeros and can change several bytes, which the CRC then detects with probability 1 − 2^−32, a figure that no theorem states.  The script's model has no timing: a `0x00` inside a record ends a segment early, the board answers it while the rest of the record arrives, and if the framing reads no byte while it answers, USART3 keeps only the last byte that arrives meanwhile, so the rest of the record gives `0x1001`, `0x1003`, or no segment.

## The bridge's requirements

No theorem covers the bridge.  These requirements are premises of every statement about the relays and the cells, and the demo's host program implements them.  The bridge measures every time on its own clock.

| Requirement | Statement |
|---|---|
| BR1 Leases | An answer is authentic when it decodes to 17 bytes with tag `0x80` and the CRC of `LINK` and its bytes.  It is current when it is authentic, its answered sequence number is that of the latest record sent, and no earlier answer was current for that record.  A current answer with a relay's bit set gives that relay a lease that ends `T_lease` after the sampling of the record it answers, and an authentic answer with the bit clear ends the relay's lease at once.  The bridge energizes a relay only while it holds the relay's lease, and it de-energizes the relay within `T_act` of the lease's end.  The board sequence number serves the bridge's log alone |
| BR2 Power-up | All relays are de-energized at power-up.  The bridge then sends one `0x00` and sends its first record once `T_ans` has passed with no byte received since the end of the `0x00` |
| BR3 Lockstep | The bridge sends records one at a time, with consecutive sequence numbers modulo 2^32.  It sends the next record only after a current answer to the latest record, or after BR4 |
| BR4 Timeout | When no current answer arrives within `T_ans` of the end of the latest record's delimiter, the bridge discards any partial answer and sends one `0x00`.  It then waits until a current answer arrives, or until `T_ans` has passed with no byte received since the later of the end of the `0x00` and the last byte received, applying BR1 to every answer that arrives.  It then sends the next record |
| BR5 Sampling | The bridge samples a record's values after the previous exchange has ended, by a current answer or by BR4, after it has applied the answers that arrived, and within `T_sample` of that end, and it sends the record's first byte within `T_sample` of sampling |
| BR6 Re-energization | At power-up, and after a relay's lease ends other than through a current answer with the relay's bit clear, the bridge energizes no relay until it receives a current answer with permit 0 |
| BR7 Fidelity | Each field reports the quantity it names within the measurement's stated error, and each digital bit reports the level of its input at the sampling |

The demo's bridge uses `T_ans` 100 ms, `T_lease` 500 ms, `T_sample` 20 ms, and `T_act` 20 ms, which the runs must confirm.  The estimates below take 20 ms for the long window and the latency of the host and the virtual COM port in each exchange, which no run has measured, so an exchange from sampling to the answer's end takes at most 156.7 ms and samples lie at most 176.7 ms apart in normal operation.  The table gives each case's times after the sampling of record `k`, the record that the case names.

| Case | Answers, in ms after the sampling of record `k` | Leases |
|---|---|---|
| Normal operation | Answer `k` by 156.7, answer `k + 1` by 333.4 | The lease of answer `k` outlasts answer `k + 1` by at least 166.6 ms |
| The delimiter of record `k` lost | Answer `k` at about 258.8, answer `k + 1` by about 435.4 | The lease of answer `k − 1`, which ends at 323.3 or later, outlasts answer `k`, and the lease of answer `k` outlasts answer `k + 1` by about 64.6 ms |
| Answer `k` lost | Answer `k + 1` at 395.8 to 475.8 | The lease of answer `k − 1` ends at 323.3 to 383.3, before answer `k + 1`, and the relays open |

After a lost answer the lease expires and the relays open, and BR6 keeps them open.  A record sampled once NEG's contact has opened reports it open, which check 17 turns into a fault in `NORMAL`, and a record sampled before that still gets `0x05 NORMAL`, on which BR6 does not act.  The relay's tolerance of `D_edm` records assumes that a relay operates and its auxiliary contact settles between the application of the answer that changes its bit and the sampling of the third record after that answer, which BR3 and BR5 place at least two exchanges on the wire, 233.3 ms, later.  A slower relay causes a spurious `0x3001`, which opens the relays.

BR6 keeps POS from closing onto a bus that lost its precharge after the bridge released the relays.  After a release that no current answer commanded, the bridge energizes nothing until a current answer with permit 0, and by M1 a later nonzero permit needs a start and, for POS, the precharge condition, in records that the bridge sends after that answer and so samples after the release.  Check 17 makes that answer come: in `NORMAL` a record that reports NEG open fails at once unless the start lies within `D_edm` records, and in `PRECHARGE` the open relays fail check 17 within `D_edm` records or the precharge times out.

The operator presses the reset button for at least 500 ms, after the button has been released for at least 500 ms.  Samples lie at most 176.7 ms apart in normal operation, so such a press appears in a record whose predecessor shows the button released, and a shorter press may be missed, which leaves the system in its state.  A press counts only in a record that passes every check and whose predecessor segment is a good record, and the previous `RESET` bit is that of the last record that passed the communication checks.  After a board reset or a communication fault the first good record synchronizes, so a button held through it must be released and pressed again, and the initial `prevReset` of 1 also keeps a button held at boot from forming an edge.

## Theorems

The framing's theorems, which another module proves, carry the bytes, the machine's theorems hold over every sequence of segments, and the board's theorems hold of the image from reset.  In the codes of the repository's index, the machine's theorems are SPEC, the compiled step's theorems WASM, and the board's theorems M7, a code that names the Cortex-M7 image and not theorem M7.  Every theorem may depend on no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`.

### Framing

The framing module proves F1 (decoding inverts encoding, and the encoding has no zero byte), F2 (a segment's result depends only on its bytes), and F3 (for every sequence of values that the reads return, the bytes written begin the encoded answers, each followed by `0x00`, to the non-empty segments read).  The BMS uses F3 with its machine, a maximum segment of 36 bytes, and the registers of USART3 and of UART0 of QEMU's `mps2-an500`.  Lemma L1, that COBS decoding of `k` bytes gives at most `k − 1` bytes, supports M12.

### Machine

The theorems hold for every sequence of segment results, each the decoded bytes of a segment or an error, from the state after a board reset.  Segment `t` is the `t`-th call of the machine, counted from 0, `a_t` its answer, and record `t` the segment when it decodes.  The terms good, passing the communication checks, synchronizing, age, start, and reset acceptance are those of [the machine's sections](#the-machine), and each depends only on the segments and answers up to the one it describes.  A good record passes the communication checks when it is the first segment, when the segment before it is not a good record, or when its number is that record's number plus one.

M1 is the main theorem.  If `a_n` has a nonzero permit, let `i` be the last reset acceptance at or before `n` and `j` the last start at or before `n`.  Both exist, `1 ≤ i < j ≤ n`, and:

1. segments `i − 1` to `n` are good records, and each record from `i` to `n` has the sequence number of the record before it plus one, modulo 2^32;
2. records `i` to `n` pass checks 7 to 17 and have `STOP_OK` 1;
3. the last record before `i` that passed the communication checks has `RESET` 0, and record `i` has `RESET` 1, `RUN` 0, and the auxiliary word 0;
4. record `j` has `RUN` 1 and the auxiliary word 0, and records `j` to `n` have `RUN` 1;
5. `a_{i−1}` has state `RESET_REQUIRED` or `FAULT`, `a_i` and `a_{j−1}` have state `STANDBY`, and no answer from `a_i` to `a_n` has state `RESET_REQUIRED` or `FAULT`;
6. if `a_n` has permit `0x03`, then `a_j` to `a_n` have state `PRECHARGE` and `n − j < N_pc`;
7. if `a_n` has permit `0x05`, then there is a segment `k` with `j < k ≤ n` and `k − j ≤ N_pc` such that record `k` has bus and pack voltages within `tol_pc` of each other and `AUX_NEG` and `AUX_PRE` 1, `a_j` to `a_{k−1}` have state `PRECHARGE`, and `a_k` to `a_n` have state `NORMAL`.

Items 1 and 2 state that every record from the reset acceptance to `n` passed every check, including check 17, through which the auxiliary contacts followed the permits.  Items 3 to 7 state that the states followed the transitions from `RESET_REQUIRED` or `FAULT` through `STANDBY` and `PRECHARGE`, and reached `NORMAL` only through the precharge condition.  A reset acceptance needs a good record before it, so `i ≥ 1`, and the first two answers after a board reset have permit 0.

| Theorem | Statement |
|---|---|
| M2 | The permit of every answer is the permit of its state.  No answer permits PRE and POS together, or POS without NEG |
| M3 | The answer to a segment that fails a check has permit 0 and state `FAULT`, and its code is the code of the first failing check when the state before was not `FAULT` and the code before otherwise |
| M4 | A state of `FAULT` changes only through a reset acceptance, to `STANDBY`, and the code stays the same until then |
| M5 | The answer to a record that passes the communication checks and has `STOP_OK` 0 has permit 0 and state `RESET_REQUIRED` or `FAULT` |
| M6 | The answer to a record that passes every check with `STOP_OK` 1 and `RUN` 0, in `PRECHARGE` or `NORMAL`, has permit 0 and state `STANDBY` |
| M7 | At most `N_pc` consecutive answers have state `PRECHARGE`, and the answer that ends `PRECHARGE` has state `NORMAL` only for a record that meets the precharge condition |
| M8 | The answer to a record that passes the communication checks and fails check 17 has permit 0 and state `FAULT` |
| M9 | If segments `t` to `t + k` are good records with consecutive sequence numbers, then records `t + 1` to `t + k` pass the communication checks, whatever the state before `t` |
| M10 | The answers to the first two segments after a board reset have permit 0, the first has board sequence number 0, and every reset acceptance comes after a record that passed the communication checks after the board reset with `RESET` 0 |
| M11 | Every answer has 17 bytes, tag `0x80`, board sequence number `t` modulo 2^32 for segment `t`, the answered sequence number of [the answer's format](#answer), and the CRC of `LINK` and its first 13 bytes |
| M12 | The result of a segment equal to the encoding of a 35-byte record with one byte removed is, by L1, a decode error or a record of fewer than 35 bytes, so its answer has code `0x1001` or `0x1003` when the state before was not `FAULT` |

### Board

The board theorems follow the energy gateway's files.  The statements name the step `bmsTickUsart3` from its initial state and the image's initialization list, and B4 names the step `bmsTick` for UART0 with QEMU's initialization.  They rest on boot and board theorems that hold for any initialization list whose operations the existing checks admit.

| Theorem | Statement |
|---|---|
| B1 `bms_board`, `bms_board_runs`, `bms_board_prefix` | From every state that reset gives while the flash holds the image's bytes, for every sequence `σ` of the values that reads return and every number `N` of windows, the image performs the accesses of its initialization and then the requested access of every window, the run never stops, and the bytes written to `USART_TDR` begin the encoded answers that F3 gives for the bytes read from `USART_RDR` |
| B2 `bms_confined` | Every access of the initialization lies in the register blocks of RCC, GPIOD, or USART3, and every access of the windows is to `USART_ISR`, `USART_RDR`, or `USART_TDR` |
| B3 `bms_board_steps` | Every window takes at most 16 instructions plus the step's `staticCost` |
| B3a `bms_board_poll` | Every window other than one that receives a delimiter takes at most 16 instructions plus the dispatch and the `staticCost` of the function that a polling window calls |
| B4 `bms_qemu`, `bms_qemu_prefix` | B1's statements for the image on QEMU's `mps2-an500`, with UART0 |
| B5 `bms_board_safe` | For every `σ` and `N`, every complete answer among the bytes written to `USART_TDR` with a nonzero permit is the answer `a_n` of the machine's run over the non-empty segments of the bytes read, and M1 holds of it |

B3 bounds the long window, whose CRCs over the record's 31 bytes and the answer's 13, COBS decoding of 36 bytes, machine, and encoding of 17 bytes dominate the bound, so B3 bounds the board's share of `T_ans`.  B3a bounds the polling windows, which determine the usable baud rate against half a byte time, 16,667 cycles at 4,800 baud.  `staticCost` fails on a loop, so both need a step without loops, and B3a needs the step written as a dispatch on its phase to a polling function and a delimiter function, with a lemma that bounds a window's `costRun` by the dispatch and the `staticCost` of the function its phase selects, which `LeanExe/M7/Proof/Bound.lean` does not yet provide.  The cycles an instruction come from measurement.

## Trusted base

The board's theorems rest on the trusted items of the Cortex-M7 back end that `docs/m7-bare-metal.md` lists: Lean's kernel, the definitions in the statements, the model's fidelity with the reading of the two pseudocodes and the Isla check, reset, the run conditions, and the file reader and the flash.  For the BMS, the definitions in the statements are those of the board's run, the image's initialization list, the CRC's transcription `Spec.crc32`, the framing, and the machine with its profile.  The evidence that the back end's document gives for these items applies to the BMS image unchanged.

Of the device, the trusted item is that the accesses of the initialization and the windows, which B2 confines to RCC, GPIOD, and USART3, change nothing that the model represents other than the trace.  The safety claims hold for every sequence of values that the reads return, so they need nothing about the bytes that reach USART3, and the ST-LINK's virtual COM port, USB, the host, and the bridge's transport belong to the black channel.  Whether the system runs depends on further behavior: the initialization's effect, which includes overrun detection disabled and which a read of `USART_CR3` over SWD after each run checks, since a read during the run would be a debugger access, and USART3's reception with `OVRDIS` set as RM0410 section 34.8.3 states it and tests on the board confirmed.  A failure of any of them gives communication faults or silence, after which the leases release the relays.

## What lies outside the theorems

| Item | Status |
|---|---|
| The bridge and the simulator | BR1 to BR7 are premises of every statement about relays and cells |
| Common cause | Every reading passes through one bridge and one wire.  A bridge that reports a wrong value with a correct CRC goes undetected, except by the check of the cell sum against the pack voltage when the two measurements take independent paths |
| Residual errors of the CRC | M1 states that a permitted record passed the CRC check, and no theorem bounds the probability that a corrupted record passes it |
| Replayed records | After a segment that clears synchronization, the board cannot tell a replayed run of the bridge's own good records from new ones.  BR1 acts only on the first answer to the latest record sent, and BR6 and check 17 tie a renewed permit to records sampled after a release, but no theorem covers the board and the bridge together |
| Physical quantities | No theorem relates a reading to a cell's voltage, temperature, or current, or bounds how far a cell can pass a limit before the relays open |
| Hardware faults | The NUCLEO board is not safety-rated hardware, and the hardware-fault analysis of IEC 62619 is not covered |
| Real time | `T_ans`, `T_lease`, `T_sample`, `T_act`, the window cycles, and the line rate are measured or chosen, and no theorem speaks of time |
| Lost bytes | `OVRDIS` forces `ORE` to 0, so USART3 records no overrun, and the checks report the lost bytes as a communication fault.  Lockstep keeps overruns out of normal operation |
| Profile values | The theorems hold for whatever profile is compiled in, and whether its values suit the cell is a matter of review |

## Fault-injection schedule

Each scenario starts in `NORMAL` unless it states otherwise.  An expected answer gives the permit, the state, and the code, and every answer after a fault has permit 0 until a reset acceptance.  The bridge's expected actions follow BR1 to BR6.

| Scenario | Injection | Expected answers | Theorems |
|---|---|---|---|
| Normal start | Board reset, a record with `RESET` 0, a record with `RESET` 1 and `RUN` 0, then `RUN` 1 | `0x00 RESET_REQUIRED 0x0001`, `0x00 STANDBY 0x0000`, `0x03 PRECHARGE`, then `0x05 NORMAL` once the bus is within `tol_pc` of the pack and `AUX_NEG` and `AUX_PRE` report closed | M1, M10 |
| Reset held at boot | `RESET` 1 from the first record, then released and pressed | No acceptance until the press after the release | M1, M10 |
| Reset with `RUN` 1 | Reset pressed in `FAULT` while `RUN` is 1 | No acceptance | M1, M4 |
| Restart after standby | `RUN` 0 in `NORMAL`, then `RUN` 1 | `0x00 STANDBY`, then `0x03 PRECHARGE` and `0x05 NORMAL` through the precharge condition | M1, M6 |
| Cell overvoltage | One cell at 3,651 mV | `0x00 FAULT 0x2002` in the answer to that record | M1, M3 |
| Cell undervoltage | One cell at 2,499 mV | `0x00 FAULT 0x2003` | M3 |
| Overtemperature | One sensor at 55.1 °C | `0x00 FAULT 0x2004` | M3 |
| Undertemperature | One sensor at −20.1 °C | `0x00 FAULT 0x2005` | M3 |
| Charge overcurrent | 280,001 mA | `0x00 FAULT 0x2006` | M3 |
| Discharge overcurrent | −280,001 mA | `0x00 FAULT 0x2007` | M3 |
| Cold charge | Charge at 2,801 mA with one sensor at −0.1 °C | `0x00 FAULT 0x2008` | M3 |
| Hot charge | Charge at 2,801 mA with one sensor at 45.1 °C | `0x00 FAULT 0x2008` | M3 |
| Thermistor open | One sensor at −50.0 °C | `0x00 FAULT 0x2001` | M3 |
| Sum mismatch | Pack voltage 301 mV above the cell sum | `0x00 FAULT 0x2009` | M3 |
| Reserved bit | Bit 6 of the digital word set | `0x00 FAULT 0x1007` | M3 |
| Lost byte | One byte of a record's encoding dropped | `0x00 FAULT 0x1001` or `0x1003`, answered `0xFFFFFFFF`; after BR4 the next record synchronizes, answered with its number, `0x00 FAULT` | M3, M9, M12 |
| Lost delimiter | A record's `0x00` dropped | No answer within `T_ans`; after the bridge's `0x00` the record's answer, `0x05 NORMAL 0x0000` | F2, BR4 |
| Inserted byte | A nonzero byte inserted into a record | `0x00 FAULT 0x1002` | M3 |
| Inserted byte between records | A nonzero byte inserted after a record's delimiter | The record's answer, then `0x00 FAULT 0x1002` for the next record | M3 |
| Changed byte | A data byte of a record changed to another nonzero value | `0x00 FAULT 0x1004` | M3 |
| Byte changed to `0x00` | A data byte of a record changed to `0x00` | One or two answers, each `0x00 FAULT` with `0x1001` or `0x1003` | M3 |
| Wrong link | A record with a CRC over another link identifier | `0x00 FAULT 0x1004` | M3 |
| Wrong tag | Tag `0x11` with a correct CRC | `0x00 FAULT 0x1005` | M3 |
| Repeated record | A record sent again with its sequence number | `0x00 FAULT 0x1006`; the next record passes the sequence check against the repeated one | M3, M9 |
| Skipped number | A record whose sequence number skips one | `0x00 FAULT 0x1006` | M3 |
| Lost answers | The board's answers dropped until the lease expires | The bridge releases the relays; answers `0x05 NORMAL` to records sampled before NEG's contact opened do not energize them (BR6); the first record that reports NEG open gets `0x00 FAULT 0x3001` | BR1, BR6, M8 |
| Bridge silent | The bridge stops sending | The bridge releases the relays at the lease's end; no answer | BR1 |
| Welded contactor | `AUX_POS` stays 1 after a standby request | `0x00 STANDBY` for the request and the `D_edm` records after it, then `0x00 FAULT 0x3001`; no reset acceptance while `AUX_POS` is 1 | M8, M1 |
| Contactor fails to close | `AUX_POS` stays 0 after the transition to `NORMAL` | `0x05 NORMAL` for the transition and the `D_edm` records after it, then `0x00 FAULT 0x3001` | M8 |
| Precharge failure | The bus stays low | `0x03 PRECHARGE` for `N_pc` records, then `0x00 FAULT 0x3002` | M7 |
| Stop | `STOP_OK` 0 | `0x00 RESET_REQUIRED 0x5001`; a restart needs a reset acceptance and a start | M5, M1 |
| Standby request | `RUN` 0 | `0x00 STANDBY 0x0000` at once | M6 |
| Board reset in `NORMAL` | NRST during operation | Board sequence 0 and `0x00 RESET_REQUIRED 0x0001`, or `0x00 FAULT` with `0x1001` or `0x1003` when the reset cuts a record; the bridge releases the relays on that authentic answer, and check 17 lets their contacts open | M10, BR1 |

## Open items

The items below bound what a later phase can claim.  Each belongs to a phase of the plan or to another task that a phase depends on.  None of them changes a statement of the machine's theorems.

| Item | State |
|---|---|
| Boot over the image's initialization list | Boot and the board theorems are being generalized over the initialization list, which B1 to B5 need for the list with the write of `OVRDIS` |
| The framing's code | B3 and B3a need the framing's segment decoding and answer encoding to be loop-free, and the fault table assumes the decoder of Cheshire and Baker that `tests/baremetal/bms_proto.py` implements |
| The lemma of B3a | A bound on a window's `costRun` by the dispatch and the `staticCost` of the function that its phase selects, which `LeanExe/M7/Proof/Bound.lean` does not provide |
| Timing values | `T_ans`, `T_lease`, `T_sample`, and `T_act` are design choices until the runs measure the exchange and the latency of the virtual COM port |

## Plan

Each phase ends with its stated criterion.  The delimited framing with F1 to F3 and L1 precedes the program, and the generalized boot precedes the board theorems.  QEMU runs come before board runs.

| Phase | Deliverables | Done when |
|---|---|---|
| Machine specification and theorems | `Demos/Bms/Spec.lean`: the profile, the record layouts, the CRC over `LINK` with `crc32Eval`, the checks, and the machine over plain structures.  `Demos/Bms/Theorems.lean`: M1 to M12.  The machine in `tests/baremetal/bms_proto.py` | M1 to M12 hold with no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`, and the Lean machine and the Python machine reproduce the test vectors and agree on random segments and on the schedule's records |
| Program and compilation | `Demos/Bms/Program.lean`: the step over structures with `Flat` instances, written as a dispatch to a polling function and a delimiter function, with a bitwise CRC from the register value of `LINK` and no loop, an `_abs` theorem relating it to the framing's step of the specification's machine, `bmsTick` for UART0 and `bmsTickUsart3` for USART3, and `verified_compile` | The module compiles, its call theorems and the `_abs` theorem hold, and native Lean agrees with the specification on recorded segments |
| Board theorems | The image's initialization list; `BmsStep.lean`, `BmsLoop.lean`, `BmsImages.lean`, `BmsBoardFile.lean`, and `BmsQemuFile.lean` in `tests/TestSupport/M7/`; the lemma of B3a | The kernel checks every image and B1 to B5 |
| Bridge and simulator | `tests/baremetal/uart_bms.py`: four cells with an open-circuit voltage table, a series resistance, and a capacity; one lumped temperature per sensor; a load and charger profile; relays with operate and release times, auxiliary contacts, and injectable welds and failures to close; a precharge resistor charging the bus capacitance; the supervisor's `RUN`, the stop and reset inputs; BR1 to BR7; the fault-injection schedule; a log of both directions; and a replay of the segments through native Lean | A QEMU run of the schedule gives answers byte-identical to native Lean's and to every expected answer of the schedule |
| Runs and timing | Runs under QEMU, in Renode, and on the board after the reset of `stlink_nrst.py`; a read of `USART_CR3` over SWD after each run; the cycles of every kind of window from `m7_dwt.py` and `m7_timing.py`; the measured exchange and latency; and a count of damaged segments, from the answers whose answered field is `0xFFFFFFFF`, and of the bridge's timeouts, since `ORE` stays 0 | The board's run of the schedule matches native Lean byte for byte with no communication fault that the schedule did not inject, and the measurements confirm or replace the timing values |
| Report and README | `tests/baremetal/bms_report.py`, after `gateway_report.py`, with cell voltages against their limits, temperatures, current, bus and pack voltage, permits and relay states, states, codes, and a table of events; `Demos/Bms/README.md` with the theorems, the premises, the run data, and the limits; entries in `Demos/README.md` and `index.md` | The README's claims match the theorems and the run data |

## References

- [IEC 61784-3:2021, Industrial communication networks, Profiles, Part 3: Functional safety fieldbuses](https://webstore.iec.ch/publication/62095)
- [OPC 10000-15, OPC UA Safety, section 5.3](https://reference.opcfoundation.org/specs/OPC-10000-15/5.3)
- [IEC 62619:2022, Safety requirements for secondary lithium cells and batteries for use in industrial applications](https://webstore.iec.ch/publication/64073)
- [EVE Energy, LF280K Product Specification, LF280K-72174, version A, 2021](https://akkudoktor.net/uploads/short-url/maYfKTLNOcRNqlYZNRluaz43RTL.pdf)
- [S. Cheshire and M. Baker, Consistent Overhead Byte Stuffing, IEEE/ACM Transactions on Networking 7(2), 1999](https://doi.org/10.1109/90.769765)
- [ITU-T Recommendation V.42](https://www.itu.int/rec/T-REC-V.42-200203-I/en)
- [RM0410, STM32F76xxx and STM32F77xxx reference manual](https://www.st.com/resource/en/reference_manual/rm0410-stm32f76xxx-and-stm32f77xxx-advanced-armbased-32bit-mcus-stmicroelectronics.pdf)
- [foxBMS 2 software overview](https://iisb-foxbms.iisb.fraunhofer.de/foxbms/docs/html/latest/software/overview/sw-overview.html)
- [The Cortex-M7 back end](../../docs/m7-bare-metal.md)
- [Energy: authorization of battery power limits](../Energy/README.md)
- [CRC-32 and CRC-32C](../../Library/Hashing/Crc/README.md)
