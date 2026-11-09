# BMS host: the bridge and the pack simulator

`tests/baremetal/uart_bms.py` plays the far end of the board's UART for [the BMS protection requirements](requirements.md).  It implements the bridge's requirements BR1 to BR6, simulates the pack, the relays, the bus, and the operator's and supervisor's inputs behind the bridge, and runs the requirements' fault-injection schedule as scenarios that check each answer.  It runs against QEMU's UART0, against the board's virtual COM port, or against the Python machine of `tests/baremetal/bms_proto.py` behind a simulated channel.  That machine transcribes [the machine's specification](Spec.lean), which is the reference: the Python machine is a test aid that checks every answer byte for byte and lets the schedule and the bridge run before the board image exists.  No theorem depends on the bridge or the simulator, and BR1 to BR7 remain premises of the requirements' statements about relays and cells.

## The bridge

The bridge uses the requirements' timing values, `T_ans` 100 ms, `T_lease` 500 ms, `T_sample` 20 ms, and `T_act` 20 ms, and measures every time on its own clock: the host's monotonic clock, or the simulated clock of a mirror run.  The table states each requirement as the script implements it.

| Requirement | Implementation |
|---|---|
| BR1 Leases | An answer is authentic when its segment decodes to 17 bytes with the tag `0x80` and the CRC of `LINK` and bytes 0 to 12, whatever its state code.  It is current when it is authentic, answers the sequence number of the latest record sent, and is the first current answer to that record.  A current answer with a relay's bit set sets the relay's lease to end `T_lease` after the sampling of the record it answers, and an authentic answer with the bit clear, current or not, ends the lease.  The bridge energizes a relay while the relay holds a lease and BR6 does not block.  Every wait of the bridge ends no later than the earliest lease end, where the bridge de-energizes the relay, and the run fails when a release comes more than `T_act` after a lease's end |
| BR2 Power-up | The relays start de-energized.  The bridge sends one `0x00` and sends its first record once `T_ans` has passed with no byte received since the later of the end of the `0x00` and the last byte received |
| BR3 Lockstep | The bridge sends one record at a time, numbered consecutively modulo 2^32 from 2^32 − 2, so that the number wraps during the first scenario.  It sends the next record after a current answer to the latest record or after BR4 |
| BR4 Timeout | When no current answer arrives within `T_ans` of the end of the latest record's delimiter, the bridge discards the partial answer it holds, sends one `0x00`, and waits until a current answer arrives or `T_ans` passes with no byte received since the later of the end of the `0x00` and the last byte received, applying BR1 to each answer.  The host cannot observe a byte leave the UART, so the end of a write is the time of the write plus the line time of its bytes, 2.083 ms a byte at 4,800 baud |
| BR5 Sampling | The bridge samples a record after it has applied the answers that ended the previous exchange, and sends the first byte after sampling.  On the host's clock both follow at once, and in a mirror run each follows after `STEP`, 1 ms unless set.  The run records the larger of the two delays and fails above `T_sample`.  After a board reset, and after the silence of the bridge-silent scenario, the bound counts from the end of the reset or the silence |
| BR6 Re-energization | The bridge blocks every relay at power-up, when a lease expires, and when a non-current authentic answer ends a lease, and it clears the block on a current answer with permit 0.  A current answer with a nonzero permit while the block holds grants leases but energizes nothing |
| BR7 Fidelity | The simulator's readings carry the measurement noise of [the pack simulator](#the-pack-simulator), and each digital bit reports the contact or input at the sampling |

Before BR1 applies to an answer, the bridge compares it with the answer of a second Python machine fed every byte the bridge writes, in order, from a board reset, and a difference stops the run.  On QEMU and on the board this comparison checks the image against the mirror, and in a mirror run it detects bytes that the simulated USART3 lost, which lockstep must prevent.

## The channel in a mirror run

The simulated channel carries each byte to the board 2.083 ms after the previous one, the time of 10 bits at 4,800 baud, and adds 5 ms of latency in each direction.  The board reads a byte as it arrives, except from a delimiter that ends a non-empty segment until it has sent the answer: the window that receives the delimiter takes 10 ms, and the answer's bytes then leave at the line rate.  A byte that arrives meanwhile waits in `USART_RDR`, and a later byte replaces it, as RM0410 section 34.8.3 states for `OVRDIS` set, and the run fails when USART3 loses a byte that way.  With these values an exchange takes 136.7 ms from the first byte of the record to the end of the answer, the requirements' estimate of 116.7 ms on the line and 20 ms for the long window and the latency.  A board reset takes no time, and the board then starts from the state after a reset with no partial segment.

## The pack simulator

The simulator integrates the pack in steps of 2 ms up to each sampling and each change of a relay's coil.  Its parameters are illustrative values for a pack of four EVE LF280K cells in series, and no theorem depends on them.  A scenario changes a reading by editing the record's values after sampling: a cell reading changes the pack reading by the same amount, as a real cell would, and the other edits change only their field.

| Model | Parameters |
|---|---|
| Open-circuit voltage | Linear between the points 2.500 V at 0% state of charge, 3.000 V at 5%, 3.200 V at 10%, 3.250 V at 20%, 3.285 V at 40%, 3.305 V at 60%, 3.330 V at 80%, 3.340 V at 90%, 3.360 V at 95%, and 3.450 V at 100%.  The points follow the flat plateau of lithium iron phosphate cells and are not fitted to the LF280K |
| Capacities and state of charge | 280.0, 275.8, 282.8, and 278.6 Ah, 280 Ah times 1.000, 0.985, 1.010, and 0.995, starting at 50%, 49%, 51%, and 50% |
| Series resistance | 0.25 mΩ for each cell, the AC impedance bound of the LF280K's section 4, item 4 |
| RC pair | 0.30 mΩ with a time constant of 30 s for each cell |
| Terminal voltages | A cell reads its open-circuit voltage plus the current times the series resistance plus the RC pair's voltage, with the current positive while charging.  The pack reads the sum of the cells plus the current times 0.30 mΩ of busbars |
| Temperatures | Sensor 0 for cells 0 and 1 and sensor 1 for cells 2 and 3, each a lumped node of 10,440 J/K, two cells of 5.22 kg (section 4, item 13) at an assumed 1,000 J/(kg·K), heated by the current squared times the series and RC resistances of its cells and cooled through 0.5 K/W toward ambient temperatures of 25.0 and 24.5 °C |
| Bus | A capacitance of 10 mF on the load side of the contactors, with a 1 kΩ bleed resistor.  With NEG and POS closed the bus takes the pack voltage.  With NEG and PRE closed and POS open, a 10 Ω precharge resistor charges it with a time constant of about 0.1 s, and the current through the resistor is the pack current.  The precharge failure adds a 1 Ω short across the bus, which holds it near 1.2 V |
| Load and charger | With NEG and POS closed, a cycle of 20 s: 100 A of discharge for 8 s, 2 s at rest, 50 A of charge for 8 s, and 2 s at rest |
| Relays | NEG and POS operate in 30 ms and release in 15 ms, and PRE operates in 10 ms and releases in 5 ms.  Each auxiliary contact follows its main contact.  A weld keeps closed contacts closed, a failure to close keeps open contacts open, and one scenario slows the release of NEG and POS to 200 ms |
| Inputs | `STOP_OK`, `RESET`, and `RUN`, set by the scenarios |
| Measurement noise | Uniform integers from a generator seeded by `SEED`, 1 unless set: ±2 mV on each cell, ±0.1 °C on each temperature, ±50 mA on the current, and ±10 mV on the pack and bus voltages |

## Scenarios

The scenarios follow the rows of the requirements' fault-injection schedule, with the board reset in `NORMAL` split into a reset between records and a reset during a record, and with scenarios at the end of the table that test rules the schedule does not reach.  A scenario that starts in `NORMAL` brings the system there first: after a fault or a stop, a record with the reset button released and `RUN` 0, a press, which must give `0x00 STANDBY 0x0000`, a record with `RUN` 1, which must give `0x03 PRECHARGE`, and records that must give `PRECHARGE` until the first record that meets the precharge condition, which must give `0x05 NORMAL`.  Each scenario checks the permit, state, and code of every answer after that point, and where the schedule states them, the answered sequence number, whether the answer is current, the board sequence number, the relays that the bridge energizes, and the bridge's timeouts.  The expected values come from the requirements, apart from the Python machine: the scenarios state `N_pc`, `D_edm`, `tol_pc`, the limits, and the precharge condition themselves.

The bridge injects faults on the wire in its write path.  A fault that leaves the record in one piece goes out in one write.  A fault that makes the board answer before the rest of the record arrives, a byte changed to `0x00`, a repeated record, or a board reset during a record, goes out in pieces, and the channel holds each piece until the board's answer to the one before has arrived or `T_ans` has passed with no byte.  The pieces keep lockstep, so the board reads exactly the bytes that the bridge wrote, which the replay requires.  The lost-answer scenario drops answers on the receiving side: the bridge logs the bytes it receives and then discards them, from the start of an exchange until a lease expires.

| Scenario | Injection | Expected answers | Answers in the mirror run |
|---|---|---|---|
| `normal-start` | A board reset, a record with `RESET` 0, a record with `RESET` 1 and `RUN` 0, then `RUN` 1 | `0x00 RESET_REQUIRED 0x0001` with board sequence number 0, `0x00 STANDBY 0x0000`, `0x03 PRECHARGE` until the precharge condition, then `0x05 NORMAL` | `PRECHARGE` four times |
| `reset-held-at-boot` | A board reset, `RESET` 1 for three records, 0 for two, then 1 | `RESET_REQUIRED 0x0001` until the press after the release, then `STANDBY` and a start | As expected |
| `reset-with-run` | A cell at 3,651 mV, then a temperature of 55.1 °C, then the reset pressed and released with `RUN` 1 | `0x00 FAULT 0x2002` for every record: the code stays, and no acceptance | As expected |
| `restart-after-standby` | `RUN` 0 for one record, then `RUN` 1 | `0x00 STANDBY`, `STANDBY` while a record reports a contact closed, then a start and the precharge | One `STANDBY` while the contacts opened |
| `cell-overvoltage` | A cell at 3,650 mV, then at 3,651 mV | `0x05 NORMAL`, then `0x00 FAULT 0x2002` | As expected |
| `cell-undervoltage` | A cell at 2,500 mV, then at 2,499 mV | `NORMAL`, then `0x00 FAULT 0x2003` | As expected |
| `overtemperature` | A sensor at 55.0 °C, then at 55.1 °C | `NORMAL`, then `0x00 FAULT 0x2004` | As expected |
| `undertemperature` | A sensor at −20.0 °C, then at −20.1 °C | `NORMAL`, then `0x00 FAULT 0x2005` | As expected |
| `charge-overcurrent` | 280,000 mA, then 280,001 mA | `NORMAL`, then `0x00 FAULT 0x2006` | As expected |
| `discharge-overcurrent` | −280,000 mA, then −280,001 mA | `NORMAL`, then `0x00 FAULT 0x2007` | As expected |
| `cold-charge` | 2,801 mA with a sensor at 0.0 °C, then at −0.1 °C | `NORMAL`, then `0x00 FAULT 0x2008` | As expected |
| `hot-charge` | 2,801 mA with a sensor at 45.0 °C, then at 45.1 °C | `NORMAL`, then `0x00 FAULT 0x2008` | As expected |
| `thermistor-open` | A sensor at −50.0 °C | `0x00 FAULT 0x2001` | As expected |
| `sum-mismatch` | The pack voltage 300 mV above the cell sum, then 301 mV | `NORMAL`, then `0x00 FAULT 0x2009` | As expected |
| `reserved-bit` | Bit 6 of the digital word | `0x00 FAULT 0x1007` | As expected |
| `lost-byte` | A data byte near the middle of the record's encoding dropped | `0x00 FAULT` with `0x1001` or `0x1003`, answered `0xFFFFFFFF` and not current, a timeout, then the next record answered with its number, `0x00 FAULT` with the same code | `0x1003` |
| `lost-delimiter` | The record's `0x00` dropped | No answer within `T_ans` of the record's end, a timeout, then `0x05 NORMAL 0x0000`, current, with no relay released | Answer 237.7 ms after the sampling |
| `inserted-byte` | `0x55` inserted near the middle of the record | `0x00 FAULT 0x1002`, answered `0xFFFFFFFF`, then `FAULT 0x1002` for the next record | As expected |
| `inserted-byte-between-records` | `0x55` after the record's delimiter | `0x05 NORMAL`, then `0x00 FAULT 0x1002` answered `0xFFFFFFFF` for the next record, then `FAULT 0x1002` | As expected |
| `changed-byte` | A data byte near the middle changed to another nonzero value | `0x00 FAULT 0x1004`, answered `0xFFFFFFFF`, then `FAULT 0x1004` | As expected |
| `byte-changed-to-zero` | A data byte near the middle changed to `0x00` | Two answers, each `0x00 FAULT` with `0x1001` or `0x1003` and answered `0xFFFFFFFF`, then the next record with the same code | `0x1001` |
| `wrong-link` | The CRC over the identifier `LeanExe-BMS-0002` | `0x00 FAULT 0x1004`, answered `0xFFFFFFFF` | As expected |
| `wrong-tag` | Tag `0x11` with a correct CRC | `0x00 FAULT 0x1005`, answered with the record's number and current | As expected |
| `repeated-record` | The record delivered twice | `0x05 NORMAL`, then `0x00 FAULT 0x1006` answering the same number and not current, which releases the relays and sets BR6's block, then `FAULT 0x1006` for the next record, which clears the block | As expected |
| `skipped-number` | A sequence number skipped | `0x00 FAULT 0x1006`, then `FAULT 0x1006` for the next record | As expected |
| `lost-answers` | Received bytes dropped from the next exchange until a lease expires | No answer while dropping, the relays released within `T_act` of `T_lease` after the sampling of the record of the last nonzero permit, `0x05 NORMAL` that energizes nothing for each record that reports NEG closed, then `0x00 FAULT 0x3001` for the first record that reports NEG open | One `NORMAL`, then `0x3001` |
| `bridge-silent` | No record for 1 s | No answer, the relays released as for the lost answers, then `0x00 FAULT 0x3001` | As expected |
| `welded-contactor` | POS welded in `NORMAL`, then `RUN` 0, then the reset pressed | `0x00 STANDBY` for the request and the `D_edm` records after it, then `0x00 FAULT 0x3001`, and no acceptance of the press | As expected |
| `contactor-fails-to-close` | POS fails to close, then a start from `STANDBY` | `0x05 NORMAL` for the transition and the `D_edm` records after it, then `0x00 FAULT 0x3001` | As expected |
| `precharge-failure` | The bus shorted, then a start from `STANDBY` | `0x03 PRECHARGE` for `N_pc` answers, then `0x00 FAULT 0x3002` | As expected |
| `stop` | `STOP_OK` 0 for two records, then 1 with `RUN` 1 | `0x00 RESET_REQUIRED 0x5001` for each, and a restart through a reset acceptance and a start | As expected |
| `standby-request` | `RUN` 0 | `0x00 STANDBY 0x0000`, with every relay de-energized | As expected |
| `board-reset-in-normal` | A board reset between two records | `0x00 RESET_REQUIRED 0x0001` with board sequence numbers 0, 1, and 2, the first current, which releases the relays and leaves no block | As expected |
| `board-reset-during-record` | A board reset after 18 bytes of a record | `0x00 FAULT` with `0x1001` or `0x1003`, board sequence number 0, not current, then the next record with board sequence number 1 and the same code | `0x1001` |
| `reset-at-synchronization` | A lost byte, then the reset pressed with `RUN` 0 in the record that synchronizes, held for a second record, released, and pressed | `FAULT` with the lost byte's code until the press after the release, then `0x00 STANDBY`: a synchronizing record accepts no reset | `0x1003`, then `STANDBY` |
| `precharge-limit` | A start, then records that report the bus 501 mV below the pack until NEG and PRE report closed, then 500 mV below | `0x03 PRECHARGE` for each record at 501 mV, then `0x05 NORMAL` | As expected |
| `board-reset-slow-contacts` | NEG and POS releasing in 200 ms, then a board reset between two records | `RESET_REQUIRED 0x0001` for segments 0 to 2 whatever the contacts report, and for segment 3 unless it reports a contact closed, which gives `0x00 FAULT 0x3001` | `RESET_REQUIRED` for all four: the contacts opened before segment 3 |

## Files

A run with the prefix `PREFIX` writes three files.  `PREFIX.in` holds one line for each write of the bridge, its bytes in lowercase hexadecimal: a record's encoding with its delimiter or a piece of it, a lone `00` of BR2 or BR4, or bytes that a fault changed.  `PREFIX.out` holds one line for each answer that the board sent, its encoding and the delimiter that ends it in hexadecimal, as received before any injected drop.  Both files hold the line `reset` at each board reset, which the bridge makes only between two writes.

The replay of a run starts the framing and the machine from the state after a board reset for each part of `PREFIX.in` between `reset` lines, feeds the part's bytes in order, and writes each answer's encoding and its delimiter as one line, with `reset` between the parts.  The result must equal `PREFIX.out` line for line.  `uart_bms.py replay` performs the replay with the Python machine, and every run performs it on its own files before it reports.  The replay needs only the framing and the machine, so `bms-replay` of `tests/TestSupport/Bms/Replay.lean` applies it in native Lean with the specification's machine and the framing of `LeanExe/Requests/Delimited.lean`, `delimAnswers machine maxSegment init` of each part, and compares the result with `PREFIX.out` line for line.

`PREFIX.log` holds one event a line: the time in milliseconds since the start of the run on the bridge's clock, the event, and its fields.

| Event | Fields |
|---|---|
| `power-up` | None: BR2 begins |
| `scenario`, `result` | The scenario's name, and for `result` its outcome, `pass`, `fail`, or `skip` |
| `sample` | The record's sequence number and its 35 raw bytes in hexadecimal, after any change a scenario makes to the record |
| `tx` | The bytes written, as in `PREFIX.in` |
| `rx` | An answer received, as in `PREFIX.out` |
| `drop` | An answer that the injection discarded |
| `answer` | The board sequence number, the answered sequence number, the permit, the state, the code, and `current` or `other` |
| `inauthentic` | A frame that is not an authentic answer, without its delimiter |
| `revoke` | A relay whose lease an answer ended, and `current` or `other` |
| `expire` | A relay whose lease expired, and the lease's end in milliseconds |
| `coils` | The energized relays after a change, bit 0 NEG, bit 1 PRE, and bit 2 POS |
| `timeout` | BR4's `0x00` follows |
| `board-reset` | A board reset |
| `inject` | A fault that no record carries: a skipped number, dropped answers, the bridge's silence, a weld, a failure to close, or a short |

## Results against the mirror

Every scenario passes against the Python machine with `STEP` 1 ms and with `STEP` 20 ms, the limit that BR5 allows for both the sampling and the first byte, and with the noise seeds 1 to 5.  With `STEP` 20 ms an exchange takes at most 156.7 ms from the sampling to the end of the current answer, and after a lost delimiter the lease of the record before outlasts the delayed answer by 66.7 ms, against the requirements' estimates of 156.7 ms and about 64.6 ms.  In the lost-answer scenario with `STEP` 1 ms, the lease of the last answered record ends 361.3 ms after the sampling of the first record whose answer is dropped, and the answer to the record after it arrives at 418.8 ms, as the requirements' timing table bounds them.  The bridge releases the relays at the end of each expired lease on the simulated clock, and every answer of each run equals the replay of its `PREFIX.in`.

## Limits

QEMU's UART model and the pseudo-terminal of Renode's USART3 move bytes without line time, so the bridge paces its bytes at 2.083 ms on QEMU and, with `--pace`, in Renode, which keeps the exchanges at the pace that the relays' times, `D_edm`, and `N_pc` assume, while the answers return at once.  Without pacing, Renode's exchanges ran faster than the relays operate, and check 17 failed in `PRECHARGE`.  QEMU connects its UART's socket about 1 s before the guest runs, so on QEMU the bridge waits `--start-delay`, 3 s unless set, before its power-up.  The script has no way to reset QEMU's or Renode's board, so the scenarios that need a board reset are skipped there, and on the board they need `--reset-command`, whose duration delays the next record.  A reset that takes longer than `T_lease` lets the leases expire during it, so the board-reset scenarios then release the relays by expiry, and the slow contacts open before the record of segment 0.  `m7-board.sh nrst` resets the board through `stlink_nrst.py` and a USB reset of the ST-LINK, which removes the virtual COM port and adds it again, so the script, with `--reopen`, releases the port before the command and opens it again after it.  The runs on QEMU, in Renode, and on the board and their results appear in [the BMS guide](README.md#runs).

No scenario delivers an answer that straddles BR4's deadline, so BR4's discard of a partial answer goes untested.  The checks of the lease's timing use the bridge's own `T_lease`, so a wrong value of that constant passes them.  The pack models are simple, the open-circuit voltage curve is not fitted to the LF280K, and the readings carry uniform noise in place of the errors of real sensors.

## Commands

```sh
uv run tests/baremetal/uart_bms.py mirror build/bms/mirror
uv run tests/baremetal/uart_bms.py mirror --step 20 build/bms/mirror-step20
uv run tests/baremetal/uart_bms.py mirror --scenario lost-answers build/bms/lost-answers
uv run tests/baremetal/uart_bms.py replay build/bms/mirror
uv run tests/baremetal/uart_bms.py list
uv run tests/baremetal/uart_bms.py qemu build/bms/qemu build/bms/qemu.trace \
  qemu-system-arm -M mps2-an500 -display none -monitor none -kernel IMAGE
uv run tests/baremetal/uart_bms.py device --reset-command CMD --reopen /dev/ttyACM0 build/bms/board
```

The QEMU and board commands need an image of [the BMS step](README.md#images-and-board-theorems), running from reset with no byte received, which `m7-qemu.sh bms` and `m7-board.sh nrst bms` and `emulate bms` arrange.  `--seed` sets the noise generator's seed, and `--scenario`, repeated, selects scenarios in the order given.  Each run prints one line for each scenario and a summary with the number of records, the answers that equal the replay, the timeouts, the longest exchange without a channel fault, the smallest margin by which a lease outlasted its renewal, the longest delay from a lease's end to a release, and the longest delay of a sampling or a first byte.

## References

- [BMS protection requirements](requirements.md)
- [BMS protection requirements: decisions and review](review.md)
- [EVE Energy, LF280K Product Specification, LF280K-72174, version A, 2021](https://akkudoktor.net/uploads/short-url/maYfKTLNOcRNqlYZNRluaz43RTL.pdf)
- [RM0410, STM32F76xxx and STM32F77xxx reference manual](https://www.st.com/resource/en/reference_manual/rm0410-stm32f76xxx-and-stm32f77xxx-advanced-armbased-32bit-mcus-stmicroelectronics.pdf)
- [Energy: replay study](../Energy/Replay.md)
