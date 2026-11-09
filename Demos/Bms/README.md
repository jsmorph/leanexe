# BMS protection

[The requirements](requirements.md) specify the protection layer of a battery management system for a pack of four lithium iron phosphate cells, a machine that answers each record of a bridge with the permits of three relays, and [the review](review.md) records their decisions.  The machine's specification and its theorems carry the code SPEC of [the index](../../index.md).

## Specification and theorems

[`Spec.lean`](Spec.lean) states the machine over natural numbers, integers, lists, and structures, independent of any program.  It holds the profile's values and the diagnostic codes as named constants, the layouts of the 35-byte scan record and the 17-byte answer with their decoding and encoding, the CRC-32 of V.42 over the link identifier and a record's bytes as `crc32Eval` of [the CRC division](../../Library/Hashing/Crc/Division.lean) computes it, the state, the 17 checks in order, and the transition rules.  `step` gives the next state and the answer for the result of one non-empty segment, a framing error or the decoded bytes, and `machine` writes the answer's raw bytes.  The specification is computable, so native Lean replays recorded records against it.

The theorems hold for every sequence `x` of segment results from the state after a board reset, `answerAt x t` is the answer to segment `t`, and the terms of their statements are defined over the earlier segments and answers alone, as the requirements define them: the permit in force, a relay's age, the previous `RESET` bit, passing the communication checks, the first failing check, a reset acceptance, and a start.  Every theorem depends on no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`.

| Theorem | Statement | File |
|---|---|---|
| M1 `m1` | An answer `a_n` with a nonzero permit has a last reset acceptance `i` and a last start `j` with `1 ≤ i < j ≤ n`, and `Permitted x n i j`: segments `i − 1` to `n` are good records in sequence, records `i` to `n` pass checks 7 to 17 with `STOP_OK` 1, the reset edge precedes `i`, `RUN` holds from `j` to `n`, the answers' states run from `RESET_REQUIRED` or `FAULT` through `STANDBY` and `PRECHARGE`, at most `N_pc` records lie in `PRECHARGE`, and `NORMAL` follows a record with the precharge condition | [`Theorems.lean`](Theorems.lean) |
| M2 `m2` | Every answer's permit is its state's, `0x00`, `0x03`, or `0x05`, never PRE with POS or POS without NEG | [`Theorems.lean`](Theorems.lean) |
| M3 `m3`, `step_failure` | A segment that fails a check gets permit 0 and `FAULT`, with the first failing check's code unless the state before was `FAULT` | [`Theorems.lean`](Theorems.lean) |
| M4 `m4` | `FAULT` keeps its code until a reset acceptance leads to `STANDBY` | [`Theorems.lean`](Theorems.lean) |
| M5 `m5` | A segment whose record has `STOP_OK` 0 gets permit 0 and `RESET_REQUIRED` or `FAULT` | [`Theorems.lean`](Theorems.lean) |
| M6 `m6` | A record that passes every check with `STOP_OK` 1 and `RUN` 0 in `PRECHARGE` or `NORMAL` gets permit 0 and `STANDBY` | [`Theorems.lean`](Theorems.lean) |
| M7 `m7_count`, `m7_normal` | No `N_pc + 1` consecutive answers have `PRECHARGE`, and `NORMAL` after `PRECHARGE` answers a record with the precharge condition | [`Theorems.lean`](Theorems.lean) |
| M8 `m8` | A record whose auxiliary contacts fail check 17 gets permit 0 and `FAULT` | [`Theorems.lean`](Theorems.lean) |
| M9 `m9` | From every state, good records with consecutive sequence numbers pass the communication checks after the first | [`Theorems.lean`](Theorems.lean) |
| M10 `m10` | The first two answers have permit 0, the first has board sequence number 0, and every reset acceptance follows a record with `RESET` 0 that passed the communication checks | [`Theorems.lean`](Theorems.lean) |
| M11 `m11` | Every answer has 17 bytes, the tag `0x80`, and the CRC of `LINK` and its first 13 bytes, which `decodeAnswer` checks, the board sequence number `t` modulo 2^32, and the answered sequence number of the requirements | [`Theorems.lean`](Theorems.lean) |
| M12 `m12` | A decode error or a record shorter than 35 bytes gets `0x1001` or `0x1003` when the state before was not `FAULT` | [`Theorems.lean`](Theorems.lean) |
| `codes` | The code is 0 in `STANDBY`, `PRECHARGE`, and `NORMAL`, `0x0001` or `0x5001` in `RESET_REQUIRED`, and a fault code in `FAULT` | [`Theorems.lean`](Theorems.lean) |
| `resetAcceptance_iff`, `start_iff` | A reset acceptance is a transition from `RESET_REQUIRED` or `FAULT` to `STANDBY`, and a start one from `STANDBY` to `PRECHARGE` | [`Theorems.lean`](Theorems.lean) |
| `failure_eq` | The machine's checks of a segment are the checks that the history defines | [`Theorems.lean`](Theorems.lean) |
| `delimAnswers_eq`, `answer_stream` | The answers to bytes `bs` are the encoded answers of the run over `inputs bs`, the results of the non-empty segments, and the `n`-th segment of the bytes written decodes to the raw answer `a_n` | [`Stream.lean`](Stream.lean) |
| M1 `m1_stream` | An answer among the bytes written with a nonzero permit byte is `a_n` of the run over the non-empty segments of the bytes read, and `Permitted` holds of it | [`Stream.lean`](Stream.lean) |
| M2 `m2_stream`, M11 `m11_stream` | The permit byte of every answer written is `0x00`, `0x03`, or `0x05`, and every answer written is 17 bytes that `decodeAnswer` accepts, with the board sequence number `n` modulo 2^32 | [`Stream.lean`](Stream.lean) |
| M12 `m12_stream` | A segment that is the encoding of a 35-byte record with one byte removed gets `0x1001` or `0x1003` when the state before was not `FAULT`, since COBS decoding of `k` bytes gives fewer than `k` (`length_cobsDecode`) | [`Stream.lean`](Stream.lean) |

[`Stream.lean`](Stream.lean) carries the theorems to every byte stream: `machine` has the type of the machine of [the delimited framing](../../LeanExe/Requests/Delimited.lean), so `delimAnswers machine maxSegment init bs` is the specification of the answers to the bytes `bs`, and every theorem above holds for `inputs bs`.  M5 and M8 drop the requirements' hypothesis that the record passes the communication checks, since a record that fails them gets `FAULT` by M3.  M9 holds from every state before the first record.  [`Cases.lean`](Cases.lean) evaluates the specification when it builds: the two test vectors, the machine's answer to the scan vector, the schedule's scenarios that the machine decides, limits at and beyond their values, and the agreement of the history terms with the machine's state on a run through every state.

```sh
tools/leanrun --timeout 30m lake build Demos.Bms.Theorems Demos.Bms.Stream Demos.Bms.Cases
```
