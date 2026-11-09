import Demos.Bms.Spec

/-!
Executable cases of the BMS specification: the requirements' test vectors and the entries of the
fault-injection schedule that the machine decides.  Each `#guard` evaluates the specification when
the module builds.  A scenario lists the scan records that the bridge sends, or the framing's
errors in their place, from the state after a board reset, and compares each answer's permit,
state, and code with the schedule's expected answers.  The entries that concern bytes on the wire,
the lease, or the bridge alone (a lost delimiter, a byte inserted between records, a byte changed
to `0x00`, the bridge's silence, and the lost answers' release of the relays) need the framing or
the bridge and have no case here.
-/

namespace Demos.Bms.Cases

open Demos.Bms.Spec
open Library.Hashing.Crc.Division (crc32Eval)

/-! ## Test vectors -/

def vectorScan : Scan :=
  { tag := 0x10, seq := 7, cells := [3300, 3301, 3299, 3302], temps := [250, 245],
    current := -10000, pack := 13202, bus := 13150, digital := 0x002D }

def vectorScanRaw : List UInt8 :=
  [0x10, 0x00, 0x00, 0x00, 0x07, 0x0c, 0xe4, 0x0c, 0xe5, 0x0c, 0xe3, 0x0c, 0xe6, 0x00, 0xfa, 0x00,
    0xf5, 0xff, 0xff, 0xd8, 0xf0, 0x00, 0x00, 0x33, 0x92, 0x00, 0x00, 0x33, 0x5e, 0x00, 0x2d, 0x56,
    0xf3, 0x9e, 0x0d]

def vectorAnswer : Answer :=
  { board := 8, answered := 7, permit := 0x05, state := .normal, code := codeNone }

def vectorAnswerRaw : List UInt8 :=
  [0x80, 0x00, 0x00, 0x00, 0x08, 0x00, 0x00, 0x00, 0x07, 0x05, 0x03, 0x00, 0x00, 0x91, 0x0a, 0x58,
    0xa2]

#guard crc32Eval link == 0xfe3f9f15
#guard encodeScan vectorScan == vectorScanRaw
#guard decodeScan vectorScanRaw == vectorScan
#guard crc32Eval (vectorScanRaw.take 31) == 0xdf2e3f66
#guard encodeAnswer vectorAnswer == vectorAnswerRaw
#guard decodeAnswer vectorAnswerRaw == some vectorAnswer
#guard crc32Eval (vectorAnswerRaw.take 13) == 0x937e53f6

/-- A state in `NORMAL` that expects record 7 and numbers its next answer 8. -/
def vectorState : State :=
  { mode := .normal, diag := codeNone, synced := true, expected := 7, answers := 8,
    prevReset := false, age := [2, 2, 2], pcCount := 0, first := false }

#guard (machine vectorState (.ok vectorScanRaw)).2 == vectorAnswerRaw

/-! ## Scenarios -/

/-- Bits of the digital word. -/
def auxNeg : Nat := 0x01
def auxPre : Nat := 0x02
def auxPos : Nat := 0x04
def stopOk : Nat := 0x08
def reset : Nat := 0x10
def run : Nat := 0x20

/-- A record within every limit, with the sequence number `seq`, the digital word `d`, and the
bus voltage `bus`. -/
def scan (seq d : Nat) (bus : Nat := 13200) : Scan :=
  { tag := 0x10, seq, cells := [3300, 3300, 3300, 3300], temps := [250, 245], current := -10000,
    pack := 13200, bus, digital := d }

def rec (sc : Scan) : Input := .ok (encodeScan sc)

/-- The answers to the segment results `xs` from the state `s`. -/
def answers (s : State) : List Input → List Answer
  | [] => []
  | x :: xs => (step s x).2 :: answers (step s x).1 xs

/-- The permit, state, and code of each answer after a board reset. -/
def outcomes (xs : List Input) : List (Nat × Mode × Nat) :=
  (answers init xs).map fun a => (a.permit, a.state, a.code)

/-- The state after the segment results `xs` from a board reset. -/
def after (xs : List Input) : State := xs.foldl (fun s x => (step s x).1) init

/-- Normal start: a record with `RESET` 0, a record with `RESET` 1 and `RUN` 0, a start with the
bus low, a record with NEG and PRE closed and the bus rising, and the precharge condition. -/
def startup : List Input :=
  [rec (scan 0 stopOk), rec (scan 1 (stopOk + reset)), rec (scan 2 (stopOk + run) 0),
    rec (scan 3 (stopOk + run + auxNeg + auxPre) 6000),
    rec (scan 4 (stopOk + run + auxNeg + auxPre))]

/-- The digital word in `NORMAL` with NEG and POS closed. -/
def normalWord : Nat := stopOk + run + auxNeg + auxPos

/-- `startup` followed by a record in `NORMAL` with NEG and POS closed. -/
def inNormal : List Input := startup ++ [rec (scan 5 normalWord)]

#guard outcomes inNormal ==
  [(0, .resetRequired, codeBoot), (0, .standby, codeNone), (3, .precharge, codeNone),
    (3, .precharge, codeNone), (5, .normal, codeNone), (5, .normal, codeNone)]
#guard (answers init inNormal).map (·.board) == [0, 1, 2, 3, 4, 5]
#guard (answers init inNormal).map (·.answered) == [0, 1, 2, 3, 4, 5]

/-- The last answer's permit, state, and code after `inNormal` and the records `xs`. -/
def fromNormal (xs : List Input) : Option (Nat × Mode × Nat) := (outcomes (inNormal ++ xs)).getLast?

/-- A record in `NORMAL` numbered 6 with the fields that `f` changes. -/
def faulty (f : Scan → Scan) : List Input := [rec (f (scan 6 normalWord))]

/-! Reset held at boot: no acceptance until a press after a release. -/
#guard outcomes [rec (scan 0 (stopOk + reset)), rec (scan 1 (stopOk + reset)),
    rec (scan 2 stopOk), rec (scan 3 (stopOk + reset))] ==
  [(0, .resetRequired, codeBoot), (0, .resetRequired, codeBoot), (0, .resetRequired, codeBoot),
    (0, .standby, codeNone)]

/-! Reset with `RUN` 1 in `FAULT`: no acceptance, and the code stays. -/
#guard (outcomes (inNormal ++ faulty (fun sc => { sc with cells := [3651, 3300, 3300, 3300] }) ++
    [rec (scan 7 (stopOk + run)), rec (scan 8 (stopOk + run + reset)), rec (scan 9 (stopOk + run)),
      rec (scan 10 (stopOk + run + reset))])).drop 6 ==
  [(0, .fault, codeOverVoltage), (0, .fault, codeOverVoltage), (0, .fault, codeOverVoltage),
    (0, .fault, codeOverVoltage), (0, .fault, codeOverVoltage)]

/-! Restart after standby: `RUN` 0 in `NORMAL`, then a start and the precharge condition. -/
#guard (outcomes (inNormal ++ [rec (scan 6 (stopOk + auxNeg + auxPos)), rec (scan 7 stopOk),
    rec (scan 8 (stopOk + run) 0), rec (scan 9 (stopOk + run + auxNeg + auxPre))])).drop 6 ==
  [(0, .standby, codeNone), (0, .standby, codeNone), (3, .precharge, codeNone),
    (5, .normal, codeNone)]

/-! Limits and sensor ranges, each in the answer to the record. -/
#guard fromNormal (faulty fun sc => { sc with cells := [3651, 3300, 3300, 3300] }) ==
  some (0, .fault, codeOverVoltage)
#guard fromNormal (faulty fun sc => { sc with cells := [2499, 3300, 3300, 3300] }) ==
  some (0, .fault, codeUnderVoltage)
#guard fromNormal (faulty fun sc => { sc with temps := [551, 245] }) ==
  some (0, .fault, codeOverTemp)
#guard fromNormal (faulty fun sc => { sc with temps := [-201, 245] }) ==
  some (0, .fault, codeUnderTemp)
#guard fromNormal (faulty fun sc => { sc with current := 280001 }) ==
  some (0, .fault, codeChargeCurrent)
#guard fromNormal (faulty fun sc => { sc with current := -280001 }) ==
  some (0, .fault, codeDischargeCurrent)
#guard fromNormal (faulty fun sc => { sc with current := 2801, temps := [-1, 245] }) ==
  some (0, .fault, codeChargeTemp)
#guard fromNormal (faulty fun sc => { sc with current := 2801, temps := [451, 245] }) ==
  some (0, .fault, codeChargeTemp)
#guard fromNormal (faulty fun sc => { sc with temps := [-500, 245] }) ==
  some (0, .fault, codeSensor)
#guard fromNormal (faulty fun sc => { sc with pack := 13501 }) == some (0, .fault, codeSum)
#guard fromNormal (faulty fun sc => { sc with digital := normalWord + 0x40 }) ==
  some (0, .fault, codeReserved)

/-! The limits pass at their values. -/
#guard fromNormal (faulty fun sc =>
    { sc with cells := [3650, 2500, 3300, 3300], pack := 12750, temps := [550, -200] }) ==
  some (5, .normal, codeNone)
#guard fromNormal (faulty fun sc => { sc with current := 2800, temps := [-1, 451] }) ==
  some (5, .normal, codeNone)
#guard fromNormal (faulty fun sc => { sc with pack := 13500 }) == some (5, .normal, codeNone)

/-! Lost byte: a decode error or a short record, answered `0xFFFFFFFF`; the next record
synchronizes and is answered with its number. -/
#guard ((answers init (inNormal ++ [.error .decode, rec (scan 7 normalWord)])).drop 6).map
    (fun a => (a.answered, a.permit, a.state, a.code)) ==
  [(unanswered, 0, .fault, codeDecode), (7, 0, .fault, codeDecode)]
#guard fromNormal [.ok ((encodeScan (scan 6 normalWord)).eraseIdx 9)] ==
  some (0, .fault, codeLength)
#guard (after (inNormal ++ [.error .decode])).synced == false
#guard failure (after (inNormal ++ [.error .decode])) (rec (scan 20 normalWord)) |>.isNone

/-! Inserted byte: an overflow. -/
#guard fromNormal [.error .overflow] == some (0, .fault, codeOverflow)

/-! Changed byte, and a record over another link identifier: a CRC mismatch. -/
#guard fromNormal [.ok ((encodeScan (scan 6 normalWord)).set 14 0x55)] == some (0, .fault, codeCrc)
#guard fromNormal [.ok (encodeScanWith ("LeanExe-BMS-0002".toList.map fun c => c.toNat.toUInt8)
    (scan 6 normalWord))] == some (0, .fault, codeCrc)

/-! Wrong tag with a correct CRC, answered with its number. -/
#guard ((answers init (inNormal ++ faulty fun sc => { sc with tag := 0x11 })).getLast?.map
    fun a => (a.answered, a.permit, a.state, a.code)) == some (6, 0, .fault, codeTag)

/-! Repeated record: a sequence fault, after which the next record passes the sequence check
against the repeated one. -/
#guard fromNormal [rec (scan 5 normalWord)] == some (0, .fault, codeSeq)
#guard failure (after (inNormal ++ [rec (scan 5 normalWord)])) (rec (scan 6 normalWord)) |>.isNone

/-! Skipped number. -/
#guard fromNormal [rec (scan 7 normalWord)] == some (0, .fault, codeSeq)

/-! NEG reported open in `NORMAL`, as after lost answers: check 17. -/
#guard fromNormal [rec (scan 6 (stopOk + run + auxPos))] == some (0, .fault, codeAux)

/-! Welded contactor: `AUX_POS` stays 1 after a standby request; `STANDBY` for the request and
`D_edm` records after it, then `0x3001`, and no reset acceptance while `AUX_POS` is 1. -/
#guard (outcomes (inNormal ++ [rec (scan 6 (stopOk + auxNeg + auxPos)), rec (scan 7 (stopOk + auxPos)),
    rec (scan 8 (stopOk + auxPos)), rec (scan 9 (stopOk + auxPos)),
    rec (scan 10 (stopOk + reset + auxPos))])).drop 6 ==
  [(0, .standby, codeNone), (0, .standby, codeNone), (0, .standby, codeNone), (0, .fault, codeAux),
    (0, .fault, codeAux)]

/-! Contactor fails to close: `AUX_POS` stays 0 after the transition to `NORMAL`. -/
#guard (outcomes (startup ++ [rec (scan 5 (stopOk + run + auxNeg)), rec (scan 6 (stopOk + run + auxNeg)),
    rec (scan 7 (stopOk + run + auxNeg))])).drop 4 ==
  [(5, .normal, codeNone), (5, .normal, codeNone), (5, .normal, codeNone), (0, .fault, codeAux)]

/-! Precharge failure: the bus stays low; `PRECHARGE` for `N_pc` records, then `0x3002`. -/
#guard (outcomes (startup.take 3 ++ (List.range 10).map fun k =>
    rec (scan (3 + k) (stopOk + run + auxNeg + auxPre) 0))).drop 2 ==
  List.replicate 10 (3, .precharge, codeNone) ++ [(0, .fault, codePrecharge)]

/-! Precharge completing at the last record that `N_pc` allows. -/
#guard (outcomes (startup.take 3 ++ (List.range 9).map (fun k =>
    rec (scan (3 + k) (stopOk + run + auxNeg + auxPre) 0)) ++
    [rec (scan 12 (stopOk + run + auxNeg + auxPre))])).getLast? == some (5, .normal, codeNone)

/-! Stop: `STOP_OK` 0 in `NORMAL`; a restart needs a reset acceptance and a start. -/
#guard (outcomes (inNormal ++ [rec (scan 6 (run + auxNeg + auxPos)), rec (scan 7 run),
    rec (scan 8 (stopOk + run)), rec (scan 9 stopOk), rec (scan 10 (stopOk + reset)),
    rec (scan 11 (stopOk + run) 0)])).drop 6 ==
  [(0, .resetRequired, codeStop), (0, .resetRequired, codeStop), (0, .resetRequired, codeStop),
    (0, .resetRequired, codeStop), (0, .standby, codeNone), (3, .precharge, codeNone)]

/-! Standby request: `RUN` 0 in `NORMAL` opens at once. -/
#guard fromNormal [rec (scan 6 (stopOk + auxNeg + auxPos))] == some (0, .standby, codeNone)

/-! Board reset in `NORMAL`: board sequence 0, `RESET_REQUIRED` with `0x0001`, and the contacts
may stay closed for the first records. -/
#guard (answers init [rec (scan 40 normalWord), rec (scan 41 normalWord), rec (scan 42 normalWord),
    rec (scan 43 (stopOk + run))]).map (fun a => (a.board, a.permit, a.state, a.code)) ==
  [(0, 0, .resetRequired, codeBoot), (1, 0, .resetRequired, codeBoot),
    (2, 0, .resetRequired, codeBoot), (3, 0, .resetRequired, codeBoot)]
#guard (outcomes [rec (scan 40 normalWord), rec (scan 41 normalWord), rec (scan 42 normalWord),
    rec (scan 43 normalWord)]).getLast? == some (0, .fault, codeAux)
#guard outcomes [.error .decode] == [(0, .fault, codeDecode)]
#guard outcomes [.ok ((encodeScan (scan 40 normalWord)).drop 3)] == [(0, .fault, codeLength)]

/-! Rule 4 from `STANDBY` and `PRECHARGE`, and in `FAULT`. -/
#guard (outcomes (inNormal ++ [rec (scan 6 (stopOk + auxNeg + auxPos)), rec (scan 7 0)])).getLast? ==
  some (0, .resetRequired, codeStop)
#guard (outcomes (startup.take 3 ++ [rec (scan 3 (run + auxNeg + auxPre) 0)])).getLast? ==
  some (0, .resetRequired, codeStop)
#guard (outcomes (inNormal ++ faulty (fun sc => { sc with cells := [3651, 3300, 3300, 3300] }) ++
    [rec (scan 7 run)])).getLast? == some (0, .fault, codeOverVoltage)

/-! `RUN` 0 in `PRECHARGE`, and a start refused while an auxiliary contact reports closed. -/
#guard (outcomes (startup.take 3 ++ [rec (scan 3 (stopOk + auxNeg + auxPre) 0)])).getLast? ==
  some (0, .standby, codeNone)
#guard (outcomes (startup.take 2 ++ [rec (scan 2 (stopOk + run + auxPos))])).getLast? ==
  some (0, .standby, codeNone)

/-! A reset acceptance needs the auxiliary word 0, a good record before it, and a previous `RESET`
bit of 0 that a sequence fault does not change. -/
#guard outcomes [rec (scan 0 (stopOk + auxPos)), rec (scan 1 (stopOk + reset + auxPos))] ==
  [(0, .resetRequired, codeBoot), (0, .resetRequired, codeBoot)]
#guard (outcomes (inNormal ++ [.error .decode, rec (scan 7 (stopOk + reset))])).drop 6 ==
  [(0, .fault, codeDecode), (0, .fault, codeDecode)]
#guard outcomes [rec (scan 0 (stopOk + reset)), rec (scan 5 stopOk), rec (scan 6 (stopOk + reset))] ==
  [(0, .resetRequired, codeBoot), (0, .fault, codeSeq), (0, .fault, codeSeq)]

/-! In `FAULT` the code stays when another check fails. -/
#guard (outcomes (inNormal ++ faulty (fun sc => { sc with cells := [3651, 3300, 3300, 3300] }) ++
    [rec { scan 7 normalWord with cells := [2499, 3300, 3300, 3300] }, .error .overflow])).drop 6 ==
  [(0, .fault, codeOverVoltage), (0, .fault, codeOverVoltage), (0, .fault, codeOverVoltage)]

/-! Sequence numbers and board sequence numbers wrap modulo `2 ^ 32`. -/
#guard outcomes [rec (scan 0xFFFFFFFF stopOk), rec (scan 0 (stopOk + reset))] ==
  [(0, .resetRequired, codeBoot), (0, .standby, codeNone)]
#guard (answers { init with answers := 0xFFFFFFFF } [rec (scan 0 stopOk), rec (scan 1 stopOk)]).map
    (·.board) == [0xFFFFFFFF, 0]

/-! The answered field of a segment that does not decode to 35 bytes with a matching CRC. -/
#guard ((answers init (inNormal ++ [.error .overflow,
    .ok ((encodeScan (scan 6 normalWord)).eraseIdx 9),
    .ok (encodeScanWith ("LeanExe-BMS-0002".toList.map fun c => c.toNat.toUInt8)
      (scan 6 normalWord))])).drop 6).map (·.answered) == [unanswered, unanswered, unanswered]

/-! A short record, and the record after it synchronizes. -/
#guard ((answers init (inNormal ++ [.ok ((encodeScan (scan 6 normalWord)).eraseIdx 9),
    rec (scan 7 normalWord)])).drop 6).map (fun a => (a.answered, a.permit, a.state, a.code)) ==
  [(unanswered, 0, .fault, codeLength), (7, 0, .fault, codeLength)]

/-! Readings at and beyond their limits. -/
#guard fromNormal (faulty fun sc => { sc with current := 280000 }) == some (5, .normal, codeNone)
#guard fromNormal (faulty fun sc => { sc with current := -280000 }) == some (5, .normal, codeNone)
#guard fromNormal (faulty fun sc => { sc with current := 2801, temps := [0, 450] }) ==
  some (5, .normal, codeNone)
#guard fromNormal (faulty fun sc => { sc with pack := 12900 }) == some (5, .normal, codeNone)
#guard fromNormal (faulty fun sc => { sc with pack := 12899 }) == some (0, .fault, codeSum)
#guard fromNormal (faulty fun sc => { sc with cells := [4501, 3300, 3300, 3300] }) ==
  some (0, .fault, codeSensor)
#guard fromNormal (faulty fun sc => { sc with cells := [999, 3300, 3300, 3300] }) ==
  some (0, .fault, codeSensor)
#guard fromNormal (faulty fun sc => { sc with pack := 20001 }) == some (0, .fault, codeSensor)
#guard fromNormal (faulty fun sc => { sc with bus := 20001 }) == some (0, .fault, codeSensor)
#guard fromNormal (faulty fun sc => { sc with bus := 20000 }) == some (5, .normal, codeNone)
#guard (outcomes (startup.take 3 ++ [rec (scan 3 (stopOk + run + auxNeg + auxPre) 12700)])).getLast? ==
  some (5, .normal, codeNone)
#guard (outcomes (startup.take 3 ++ [rec (scan 3 (stopOk + run + auxNeg + auxPre) 12699)])).getLast? ==
  some (3, .precharge, codeNone)

/-! The history terms agree with the machine's state on a run that covers every state. -/

/-- The segment results of a run through every state: `inNormal`, a sequence fault, a reset
acceptance, a start, a precharge, a stop, a decode error, and a resynchronization. -/
def mixed : Nat → Input := fun t =>
  (inNormal ++ [rec (scan 7 normalWord), rec (scan 8 (stopOk + auxNeg + auxPos)), rec (scan 9 stopOk),
    rec (scan 10 (stopOk + reset)), rec (scan 11 (stopOk + run) 0),
    rec (scan 12 (stopOk + run + auxNeg + auxPre)), rec (scan 13 (run + auxNeg + auxPre)),
    .error .decode, rec (scan 30 stopOk), rec (scan 31 (stopOk + reset)),
    rec (scan 32 (stopOk + run)), rec (scan 33 (stopOk + run + auxNeg + auxPre))]).getD t
    (.error .overflow)

#guard (List.range 22).all fun t => failure (stateAt mixed t) (mixed t) == failureAt mixed t
#guard (List.range 22).all fun t => (stateAt mixed t).prevReset == prevResetAt mixed t
#guard (List.range 22).all fun t =>
  (stateAt mixed t).age == (agesAt mixed t).map fun a => min a dEdm
#guard (List.range 22).filter (resetAcceptance mixed) == [1, 9, 15]
#guard (List.range 22).filter (start mixed) == [2, 10, 16]

end Demos.Bms.Cases
