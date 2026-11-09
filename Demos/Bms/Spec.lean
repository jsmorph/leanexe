import Library.Hashing.Crc.Division

/-!
The protection machine of the BMS demo, as `Demos/Bms/requirements.md` states it, over natural
numbers, integers, lists, and structures.  The profile values and the diagnostic codes are named
constants.  A scan record and an answer are lists of bytes with big-endian fields, signed fields
in two's complement, and a CRC field that holds the CRC-32 of V.42, as `crc32Eval` of
`Library/Hashing/Crc/Division.lean` computes it, of the link identifier followed by the record's
bytes before the field.

`step` processes the result of one non-empty segment from a state and gives the next state and
the answer, applying the checks in the order of the requirements' table and the transition rules
in their order.  `machine` writes the answer's 17 bytes, so that it has the type of the machine
that the delimited framing calls once for each non-empty segment: an error of the segment or its
decoded bytes, to the next state and the raw answer.  `stateAt x t` and `answerAt x t` give the
state before segment `t` and the answer to it for every sequence `x` of segment results, from the
state after a board reset.

The terms of the theorems follow the requirements' definitions over the segments and the answers
before the one they describe, with no reference to the machine's state: the permit in force, a
relay's age, the previous `RESET` bit, passing the communication checks, the checks that fail, a
reset acceptance, and a start.  `Permitted` collects the conclusions of theorem M1.
-/

namespace Demos.Bms.Spec

open Library.Hashing.Crc.Division (crc32Eval)

/-! ## Profile -/

/-- `V_max`, the cell overvoltage limit, mV. -/
def vMax : Nat := 3650

/-- `V_min`, the cell undervoltage limit, mV. -/
def vMin : Nat := 2500

/-- `T_max`, the overtemperature limit, tenths of a degree Celsius. -/
def tMax : Int := 550

/-- `T_min`, the undertemperature limit, tenths of a degree Celsius. -/
def tMin : Int := -200

/-- `T_chg_min`, the lowest temperature for charging, tenths of a degree Celsius. -/
def tChgMin : Int := 0

/-- `T_chg_max`, the highest temperature for charging, tenths of a degree Celsius. -/
def tChgMax : Int := 450

/-- `I_chg_max`, the charge current limit, mA. -/
def iChgMax : Int := 280000

/-- `I_dis_max`, the discharge current limit, mA. -/
def iDisMax : Int := 280000

/-- `I_chg_detect`, the current above which the pack counts as charging, mA. -/
def iChgDetect : Int := 2800

/-- `V_sens_lo`, the lower end of the valid range of a cell reading, mV. -/
def vSensLo : Nat := 1000

/-- `V_sens_hi`, the upper end of the valid range of a cell reading, mV. -/
def vSensHi : Nat := 4500

/-- `T_sens_lo`, the lower end of the valid range of a temperature reading, tenths of a degree
Celsius. -/
def tSensLo : Int := -400

/-- `T_sens_hi`, the upper end of the valid range of a temperature reading, tenths of a degree
Celsius. -/
def tSensHi : Int := 1250

/-- `P_sens_hi`, the upper end of the valid range of the pack and bus readings, mV. -/
def pSensHi : Nat := 20000

/-- `tol_sum`, the allowed difference between the sum of the cells and the pack voltage, mV. -/
def tolSum : Nat := 300

/-- `tol_pc`, the allowed difference between the bus and pack voltages that completes precharge,
mV. -/
def tolPc : Nat := 500

/-- `N_pc`, the records allowed in `PRECHARGE`. -/
def nPc : Nat := 10

/-- `D_edm`, the records in which a relay's auxiliary contact may disagree after its permit bit
changes. -/
def dEdm : Nat := 2

/-- `LINK`, the link identifier: the 16 ASCII bytes of `LeanExe-BMS-0001`. -/
def link : List UInt8 := "LeanExe-BMS-0001".toList.map fun c => c.toNat.toUInt8

/-! ## Diagnostic codes -/

/-- No fault. -/
def codeNone : Nat := 0x0000

/-- Board reset, and no reset accepted since. -/
def codeBoot : Nat := 0x0001

/-- Check 1: COBS decode error. -/
def codeDecode : Nat := 0x1001

/-- Check 2: segment overflow. -/
def codeOverflow : Nat := 0x1002

/-- Check 3: length other than 35 bytes. -/
def codeLength : Nat := 0x1003

/-- Check 4: CRC mismatch. -/
def codeCrc : Nat := 0x1004

/-- Check 5: tag other than `0x10`. -/
def codeTag : Nat := 0x1005

/-- Check 6: sequence number other than the expected one. -/
def codeSeq : Nat := 0x1006

/-- Check 7: nonzero reserved bit. -/
def codeReserved : Nat := 0x1007

/-- Check 8: reading outside its sensor range. -/
def codeSensor : Nat := 0x2001

/-- Check 9: cell overvoltage. -/
def codeOverVoltage : Nat := 0x2002

/-- Check 10: cell undervoltage. -/
def codeUnderVoltage : Nat := 0x2003

/-- Check 11: overtemperature. -/
def codeOverTemp : Nat := 0x2004

/-- Check 12: undertemperature. -/
def codeUnderTemp : Nat := 0x2005

/-- Check 13: charge overcurrent. -/
def codeChargeCurrent : Nat := 0x2006

/-- Check 14: discharge overcurrent. -/
def codeDischargeCurrent : Nat := 0x2007

/-- Check 15: charging outside `T_chg_min` to `T_chg_max`. -/
def codeChargeTemp : Nat := 0x2008

/-- Check 16: the sum of the cells disagrees with the pack voltage. -/
def codeSum : Nat := 0x2009

/-- Check 17: an auxiliary contact disagrees with the permit. -/
def codeAux : Nat := 0x3001

/-- Precharge timeout. -/
def codePrecharge : Nat := 0x3002

/-- Stop demanded. -/
def codeStop : Nat := 0x5001

/-! ## Bytes and the CRC -/

/-- The tag of a scan record. -/
def scanTag : Nat := 0x10

/-- The tag of an answer. -/
def answerTag : Nat := 0x80

/-- The raw length of a scan record. -/
def scanLength : Nat := 35

/-- The raw length of an answer. -/
def answerLength : Nat := 17

/-- The answered sequence number of an answer to a segment that does not decode to 35 bytes with
a matching CRC. -/
def unanswered : Nat := 0xFFFFFFFF

/-- The number whose big-endian bytes are `bs`. -/
def beValue (bs : List UInt8) : Nat := bs.foldl (fun v b => 256 * v + b.toNat) 0

/-- The `k` big-endian bytes of `n` modulo `256 ^ k`. -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n / 256 ^ k) :: beBytes k n

/-- The big-endian field of `len` bytes at offset `off` of `raw`. -/
def field (raw : List UInt8) (off len : Nat) : Nat := beValue ((raw.drop off).take len)

/-- The integer that the two's complement `n` of `bits` bits represents. -/
def signed (bits n : Nat) : Int := if n < 2 ^ (bits - 1) then n else (n : Int) - 2 ^ bits

/-- The two's complement of `i` in `bits` bits. -/
def twos (bits : Nat) (i : Int) : Nat := (i % 2 ^ bits).toNat

/-- The CRC-32 of the link identifier `lnk` followed by the bytes `bs`. -/
def crcWith (lnk bs : List UInt8) : Nat := crc32Eval (lnk ++ bs)

/-- The CRC of the bytes `bs` of a record before its CRC field: the CRC-32 of `LINK` followed by
`bs`. -/
def crc (bs : List UInt8) : Nat := crcWith link bs

/-! ## Scan record -/

/-- The fields of a scan record: the tag, the sequence number, the cells in mV, the temperatures
in tenths of a degree Celsius, the pack current in mA, positive while charging, the pack and bus
voltages in mV, and the digital-input word. -/
structure Scan where
  tag : Nat
  seq : Nat
  cells : List Nat
  temps : List Int
  current : Int
  pack : Nat
  bus : Nat
  digital : Nat
  deriving DecidableEq, Repr

/-- The fields of the raw scan record `raw` at the requirements' offsets.  Bytes beyond the end of
`raw` read as missing, which makes a field shorter. -/
def decodeScan (raw : List UInt8) : Scan where
  tag := field raw 0 1
  seq := field raw 1 4
  cells := (List.range 4).map fun i => field raw (5 + 2 * i) 2
  temps := (List.range 2).map fun i => signed 16 (field raw (13 + 2 * i) 2)
  current := signed 32 (field raw 17 4)
  pack := field raw 21 4
  bus := field raw 25 4
  digital := field raw 29 2

/-- Bytes 0 to 30 of the scan record with the fields `sc`. -/
def scanBody (sc : Scan) : List UInt8 :=
  beBytes 1 sc.tag ++ beBytes 4 sc.seq ++ sc.cells.flatMap (beBytes 2) ++
    sc.temps.flatMap (fun t => beBytes 2 (twos 16 t)) ++ beBytes 4 (twos 32 sc.current) ++
    beBytes 4 sc.pack ++ beBytes 4 sc.bus ++ beBytes 2 sc.digital

/-- The raw scan record with the fields `sc` and the CRC over the link identifier `lnk`. -/
def encodeScanWith (lnk : List UInt8) (sc : Scan) : List UInt8 :=
  scanBody sc ++ beBytes 4 (crcWith lnk (scanBody sc))

/-- The raw scan record with the fields `sc`. -/
def encodeScan (sc : Scan) : List UInt8 := encodeScanWith link sc

/-- Bit `r` of the auxiliary word: whether the auxiliary contact of the relay of bit `r` of the
permit reports closed. -/
def Scan.aux (sc : Scan) (r : Nat) : Bool := sc.digital.testBit r

/-- The auxiliary word, bits 0 to 2 of the digital word. -/
def Scan.auxWord (sc : Scan) : Nat := sc.digital % 8

/-- `STOP_OK`, bit 3: the stop circuit is closed. -/
def Scan.stopOk (sc : Scan) : Bool := sc.digital.testBit 3

/-- `RESET`, bit 4: the reset button is pressed. -/
def Scan.reset (sc : Scan) : Bool := sc.digital.testBit 4

/-- `RUN`, bit 5: the supervisor requests operation. -/
def Scan.run (sc : Scan) : Bool := sc.digital.testBit 5

/-- Whether one of the reserved bits, 6 to 15, of the digital word is 1. -/
def Scan.reserved (sc : Scan) : Bool := (List.range 10).any fun k => sc.digital.testBit (k + 6)

/-! ## States and answers -/

/-- The protection states. -/
inductive Mode where
  | resetRequired
  | standby
  | precharge
  | normal
  | fault
  deriving DecidableEq, Repr

/-- The state code of an answer. -/
def Mode.code : Mode → Nat
  | .resetRequired => 0
  | .standby => 1
  | .precharge => 2
  | .normal => 3
  | .fault => 4

/-- The state with the code `n`. -/
def Mode.ofCode? : Nat → Option Mode
  | 0 => some .resetRequired
  | 1 => some .standby
  | 2 => some .precharge
  | 3 => some .normal
  | 4 => some .fault
  | _ => none

/-- The permit of a state.  Bit 0 permits NEG, bit 1 PRE, and bit 2 POS. -/
def Mode.permit : Mode → Nat
  | .precharge => 0x03
  | .normal => 0x05
  | _ => 0x00

/-- The fields of an answer. -/
structure Answer where
  /-- The board sequence number. -/
  board : Nat
  /-- The sequence number of the record answered, or `0xFFFFFFFF`. -/
  answered : Nat
  permit : Nat
  state : Mode
  /-- The diagnostic code. -/
  code : Nat
  deriving DecidableEq, Repr

/-- Bytes 0 to 12 of the answer `a`. -/
def answerBody (a : Answer) : List UInt8 :=
  beBytes 1 answerTag ++ beBytes 4 a.board ++ beBytes 4 a.answered ++ beBytes 1 a.permit ++
    beBytes 1 a.state.code ++ beBytes 2 a.code

/-- The 17 raw bytes of the answer `a`. -/
def encodeAnswer (a : Answer) : List UInt8 := answerBody a ++ beBytes 4 (crc (answerBody a))

/-- The answer that the raw bytes `raw` hold, when they have 17 bytes, the tag `0x80`, the CRC of
`LINK` and bytes 0 to 12, and a state code from 0 to 4.  The last condition goes beyond the
bridge's test of authenticity in BR1, which accepts every state byte. -/
def decodeAnswer (raw : List UInt8) : Option Answer :=
  if raw.length = answerLength ∧ field raw 0 1 = answerTag ∧ field raw 13 4 = crc (raw.take 13) then
    (Mode.ofCode? (field raw 10 1)).map fun m =>
      { board := field raw 1 4, answered := field raw 5 4, permit := field raw 9 1, state := m,
        code := field raw 11 2 }
  else none

/-- The machine's state.  `mode` is the field `state` of the requirements, the protection state,
and `diag` its diagnostic code.  `synced` holds when the segment before was a good record, and
`expected` is that record's sequence number plus one, modulo `2 ^ 32`.  `answers` is the board
sequence number of the next answer.  `prevReset` is the `RESET` bit of the last record that passed
the communication checks.  `age` lists the ages of the relays of bits 0, 1, and 2 of the permit, up
to `D_edm`.  `pcCount` counts the records in `PRECHARGE` without the precharge condition.  `first`
holds until the first answer after a board reset. -/
structure State where
  mode : Mode
  diag : Nat
  synced : Bool
  expected : Nat
  answers : Nat
  prevReset : Bool
  age : List Nat
  pcCount : Nat
  first : Bool
  deriving DecidableEq, Repr

/-- The state after a board reset. -/
def init : State where
  mode := .resetRequired
  diag := codeBoot
  synced := false
  expected := 0
  answers := 0
  prevReset := true
  age := [0, 0, 0]
  pcCount := 0
  first := true

/-! ## Checks -/

/-- The errors that the framing reports for a segment. -/
inductive Err where
  | decode
  | overflow
  deriving DecidableEq, Repr

/-- The result of a non-empty segment: an error, or the segment's decoded bytes. -/
abbrev Input := Except Err (List UInt8)

/-- The decoded bytes of a segment, or no bytes for an error. -/
def bytesOf : Input → List UInt8
  | .ok bs => bs
  | .error _ => []

/-- The scan record fields of a segment's decoded bytes. -/
def scanOf (x : Input) : Scan := decodeScan (bytesOf x)

/-- Whether the framing reports the error `e`. -/
def isError (e : Err) : Input → Bool
  | .error e' => e' == e
  | .ok _ => false

/-- Whether the segment decodes to 35 bytes. -/
def lengthOk (x : Input) : Bool := (bytesOf x).length == scanLength

/-- Whether bytes 31 to 34 of the decoded record hold the CRC of `LINK` followed by bytes 0 to
30. -/
def crcOk (x : Input) : Bool := field (bytesOf x) 31 4 == crc ((bytesOf x).take 31)

/-- Whether byte 0 of the decoded record is the tag `0x10`. -/
def tagOk (x : Input) : Bool := (scanOf x).tag == scanTag

/-- Checks 1 to 5, each as whether the segment fails it and its code. -/
def recordChecks (x : Input) : List (Bool × Nat) :=
  [(isError .decode x, codeDecode), (isError .overflow x, codeOverflow), (!lengthOk x, codeLength),
    (!crcOk x, codeCrc), (!tagOk x, codeTag)]

/-- Whether a segment is a good record: it passes the length, CRC, and tag checks, and with them
checks 1 and 2. -/
def good (x : Input) : Bool := (recordChecks x).all fun c => !c.1

/-- Check 6: `synced` holds and the sequence number differs from `expected`. -/
def seqFault (synced : Bool) (expected : Nat) (sc : Scan) : Bool := synced && sc.seq != expected

/-- Whether a segment passes the communication checks, checks 1 to 6, given `synced` and
`expected`. -/
def passesCommWith (synced : Bool) (expected : Nat) (x : Input) : Bool :=
  good x && !seqFault synced expected (scanOf x)

/-- Check 8: a cell lies outside `V_sens_lo` to `V_sens_hi`, a temperature outside `T_sens_lo` to
`T_sens_hi`, or the pack or bus voltage above `P_sens_hi`. -/
def sensorFault (sc : Scan) : Bool :=
  sc.cells.any (fun c => c < vSensLo || vSensHi < c) ||
    sc.temps.any (fun t => t < tSensLo || tSensHi < t) || pSensHi < sc.pack || pSensHi < sc.bus

/-- Check 15: the current exceeds `I_chg_detect` and a temperature lies outside `T_chg_min` to
`T_chg_max`. -/
def chargeTempFault (sc : Scan) : Bool :=
  iChgDetect < sc.current && sc.temps.any fun t => t < tChgMin || tChgMax < t

/-- Check 16: the sum of the four cells differs from the pack voltage by more than `tol_sum`. -/
def sumFault (sc : Scan) : Bool := tolSum < ((sc.cells.sum : Int) - sc.pack).natAbs

/-- Check 17: for some relay, the auxiliary bit differs from the relay's bit in the permit in force
`permit`, and the relay's age in `age` is at least `D_edm`. -/
def auxFault (permit : Nat) (age : List Nat) (sc : Scan) : Bool :=
  (List.range 3).any fun r => sc.aux r != permit.testBit r && dEdm ≤ age.getD r 0

/-- Checks 7 to 17, each as whether the record fails it and its code, given the permit in force
and the relays' ages. -/
def contentChecks (permit : Nat) (age : List Nat) (sc : Scan) : List (Bool × Nat) :=
  [(sc.reserved, codeReserved),
    (sensorFault sc, codeSensor),
    (sc.cells.any fun c => vMax < c, codeOverVoltage),
    (sc.cells.any fun c => c < vMin, codeUnderVoltage),
    (sc.temps.any fun t => tMax < t, codeOverTemp),
    (sc.temps.any fun t => t < tMin, codeUnderTemp),
    (iChgMax < sc.current, codeChargeCurrent),
    (sc.current < -iDisMax, codeDischargeCurrent),
    (chargeTempFault sc, codeChargeTemp),
    (sumFault sc, codeSum),
    (auxFault permit age sc, codeAux)]

/-- Checks 1 to 17 in the order of the requirements' table. -/
def checks (synced : Bool) (expected permit : Nat) (age : List Nat) (x : Input) :
    List (Bool × Nat) :=
  recordChecks x ++ (seqFault synced expected (scanOf x), codeSeq) ::
    contentChecks permit age (scanOf x)

/-- The code of the first check that fails, or `none` when every check passes. -/
def firstFailure (cs : List (Bool × Nat)) : Option Nat := (cs.find? (·.1)).map (·.2)

/-! ## Transitions -/

/-- The precharge condition: the bus and pack voltages differ by at most `tol_pc`, and `AUX_NEG`
and `AUX_PRE` are 1. -/
def prechargeCondition (sc : Scan) : Bool :=
  ((sc.bus : Int) - sc.pack).natAbs ≤ tolPc && sc.aux 0 && sc.aux 1

/-- The conditions of a reset acceptance on a record that passes every check with `STOP_OK` 1 in
`RESET_REQUIRED` or `FAULT`: `synced` held before the record, `prevReset` is 0, `RESET` is 1,
`RUN` is 0, and the auxiliary word is 0. -/
def acceptanceWith (synced prevReset : Bool) (sc : Scan) : Bool :=
  synced && !prevReset && sc.reset && !sc.run && sc.auxWord == 0

/-- The condition of a start on a record that passes every check with `STOP_OK` 1 in `STANDBY`:
`RUN` is 1 and the auxiliary word is 0. -/
def startCondition (sc : Scan) : Bool := sc.run && sc.auxWord == 0

/-- The next state, code, and precharge count. -/
structure Next where
  mode : Mode
  diag : Nat
  pcCount : Nat
  deriving DecidableEq, Repr

/-- Rule 4: a record that passes every check with `STOP_OK` 0 leads from `STANDBY`, `PRECHARGE`, or
`NORMAL` to `RESET_REQUIRED` with code `0x5001`, and keeps the state and the code in
`RESET_REQUIRED` or `FAULT`. -/
def rule4 (s : State) : Next :=
  match s.mode with
  | .resetRequired | .fault => ⟨s.mode, s.diag, s.pcCount⟩
  | .standby | .precharge | .normal => ⟨.resetRequired, codeStop, s.pcCount⟩

/-- Rule 5: the table for a record `sc` that passes every check with `STOP_OK` 1, the first
condition that holds in the state's rows.  A row that names no code keeps it, and `codes` of
`Demos/Bms/Theorems.lean` proves that the code is then 0, as the requirements state for
`STANDBY`, `PRECHARGE`, and `NORMAL`. -/
def rule5 (s : State) (sc : Scan) : Next :=
  match s.mode with
  | .resetRequired | .fault =>
      if acceptanceWith s.synced s.prevReset sc then ⟨.standby, codeNone, s.pcCount⟩
      else ⟨s.mode, s.diag, s.pcCount⟩
  | .standby =>
      if startCondition sc then ⟨.precharge, s.diag, 0⟩ else ⟨.standby, s.diag, s.pcCount⟩
  | .precharge =>
      if !sc.run then ⟨.standby, s.diag, s.pcCount⟩
      else if prechargeCondition sc then ⟨.normal, s.diag, s.pcCount⟩
      else if nPc ≤ s.pcCount + 1 then ⟨.fault, codePrecharge, s.pcCount⟩
      else ⟨.precharge, s.diag, s.pcCount + 1⟩
  | .normal => if !sc.run then ⟨.standby, s.diag, s.pcCount⟩ else ⟨.normal, s.diag, s.pcCount⟩

/-- The code of the first check from 1 to 17 that the segment `x` fails in the state `s`. -/
def failure (s : State) (x : Input) : Option Nat :=
  firstFailure (checks s.synced s.expected s.mode.permit s.age x)

/-- The next state, code, and precharge count after the segment `x` in the state `s`.  A segment
that fails a check leads to `FAULT`, with the failing check's code unless the state was already
`FAULT`, as rules 1 to 3 state.  A record that passes every check follows rule 4 or rule 5. -/
def next (s : State) (x : Input) : Next :=
  match failure s x with
  | some c => ⟨.fault, if s.mode = .fault then s.diag else c, s.pcCount⟩
  | none => if (scanOf x).stopOk then rule5 s (scanOf x) else rule4 s

/-- The step of the machine: the state after the segment `x` and the answer to it.  `synced`
becomes whether `x` is a good record, as rules 1 and 2 state, and a good record sets `expected` to
its sequence number plus one.  A record that passes the communication checks sets `prevReset` to
its `RESET` bit.  A relay gets age 0 at segment 0 and when the next state's permit differs in its
bit from the permit in force, and otherwise a record that passed the communication checks raises
its age by one, up to `D_edm`. -/
def step (s : State) (x : Input) : State × Answer :=
  let n := next s x
  let comm := passesCommWith s.synced s.expected x
  ({ mode := n.mode
     diag := n.diag
     synced := good x
     expected := if good x then ((scanOf x).seq + 1) % 2 ^ 32 else s.expected
     answers := (s.answers + 1) % 2 ^ 32
     prevReset := if comm then (scanOf x).reset else s.prevReset
     age := (List.range 3).map fun r =>
       if s.first || n.mode.permit.testBit r != s.mode.permit.testBit r then 0
       else if comm then min (s.age.getD r 0 + 1) dEdm
       else s.age.getD r 0
     pcCount := n.pcCount
     first := false },
   { board := s.answers
     answered := if lengthOk x && crcOk x then (scanOf x).seq else unanswered
     permit := n.mode.permit
     state := n.mode
     code := n.diag })

/-- The machine that the framing calls for each non-empty segment: the next state and the 17 raw
bytes of the answer. -/
def machine (s : State) (x : Input) : State × List UInt8 :=
  ((step s x).1, encodeAnswer (step s x).2)

/-- The longest segment that the framing passes to the machine, the encoded length of a scan
record. -/
def maxSegment : Nat := 36

/-! ## Runs -/

/-- The state before segment `t` of the segment results `x`, from the state `s0`. -/
def stateFrom (s0 : State) (x : Nat → Input) : Nat → State
  | 0 => s0
  | t + 1 => (step (stateFrom s0 x t) (x t)).1

/-- The state before segment `t` after a board reset. -/
def stateAt (x : Nat → Input) (t : Nat) : State := stateFrom init x t

/-- The answer `a_t` to segment `t` after a board reset. -/
def answerAt (x : Nat → Input) (t : Nat) : Answer := (step (stateAt x t) (x t)).2

/-! ## Terms of the theorems -/

/-- The last segment `u < t` at which `p` holds. -/
def lastBefore (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | t + 1 => if p t then some t else lastBefore p t

/-- The state before segment `t`: the state of answer `t - 1`, or `RESET_REQUIRED` at segment 0. -/
def stateBefore (x : Nat → Input) (t : Nat) : Mode :=
  if t = 0 then .resetRequired else (answerAt x (t - 1)).state

/-- The permit in force for segment `t`: the permit of the state before it, which the previous
answer carried, and at segment 0 the permit of `RESET_REQUIRED`, 0. -/
def permitInForce (x : Nat → Input) (t : Nat) : Nat :=
  if t = 0 then 0 else (answerAt x (t - 1)).permit

/-- Whether `synced` held before segment `t`: segment `t - 1` is a good record. -/
def syncedAt (x : Nat → Input) (t : Nat) : Bool := t != 0 && good (x (t - 1))

/-- The expected sequence number at segment `t`: that of segment `t - 1` plus one.  The checks read
it only when `syncedAt x t` holds. -/
def expectedAt (x : Nat → Input) (t : Nat) : Nat := ((scanOf (x (t - 1))).seq + 1) % 2 ^ 32

/-- Whether record `t` passes the communication checks: it is a good record, and it is the first
segment, the segment before it is not a good record, or its number is that record's number plus
one, modulo `2 ^ 32`. -/
def passesComm (x : Nat → Input) (t : Nat) : Bool :=
  good (x t) &&
    (t == 0 || !good (x (t - 1)) ||
      (scanOf (x t)).seq == ((scanOf (x (t - 1))).seq + 1) % 2 ^ 32)

/-- Whether answer `c`'s bit for relay `r` differs from the bit of the answer before it, segment 0
counting as such a segment for every relay. -/
def changedAt (x : Nat → Input) (r c : Nat) : Bool :=
  c == 0 || (answerAt x c).permit.testBit r != (answerAt x (c - 1)).permit.testBit r

/-- The age of relay `r` at segment `t`: 0 for `t = 0`, and otherwise the number of records that
passed the communication checks among segments `c + 1` to `t - 1`, where `c` is the last segment
before `t` at which the relay's bit changed.  The machine's state holds the smaller of this age and
`D_edm`, and check 17 reads only whether the age reaches `D_edm`. -/
def ageAt (x : Nat → Input) (r t : Nat) : Nat :=
  if t = 0 then 0
  else
    let c := (lastBefore (changedAt x r) t).getD 0
    ((List.range t).filter fun u => c < u && passesComm x u).length

/-- The ages of the relays of bits 0, 1, and 2 at segment `t`. -/
def agesAt (x : Nat → Input) (t : Nat) : List Nat := (List.range 3).map fun r => ageAt x r t

/-- The previous `RESET` bit at segment `t`: the `RESET` bit of the last record before `t` that
passed the communication checks, or 1 when there is none. -/
def prevResetAt (x : Nat → Input) (t : Nat) : Bool :=
  match lastBefore (passesComm x) t with
  | some u => (scanOf (x u)).reset
  | none => true

/-- The code of the first check from 1 to 17 that segment `t` fails. -/
def failureAt (x : Nat → Input) (t : Nat) : Option Nat :=
  firstFailure (checks (syncedAt x t) (expectedAt x t) (permitInForce x t) (agesAt x t) (x t))

/-- The code of the first check from 7 to 17 that record `t` fails. -/
def contentFailureAt (x : Nat → Input) (t : Nat) : Option Nat :=
  firstFailure (contentChecks (permitInForce x t) (agesAt x t) (scanOf (x t)))

/-- Whether segment `t` is a reset acceptance: a record that passes every check with `STOP_OK` 1
in `RESET_REQUIRED` or `FAULT`, after a good record, with the previous `RESET` bit 0, `RESET` 1,
`RUN` 0, and the auxiliary word 0. -/
def resetAcceptance (x : Nat → Input) (t : Nat) : Bool :=
  (failureAt x t).isNone && (scanOf (x t)).stopOk &&
    (stateBefore x t == .resetRequired || stateBefore x t == .fault) &&
    acceptanceWith (syncedAt x t) (prevResetAt x t) (scanOf (x t))

/-- Whether segment `t` is a start: a record that passes every check with `STOP_OK` 1 in
`STANDBY`, with `RUN` 1 and the auxiliary word 0. -/
def start (x : Nat → Input) (t : Nat) : Bool :=
  (failureAt x t).isNone && (scanOf (x t)).stopOk && stateBefore x t == .standby &&
    startCondition (scanOf (x t))

/-- `i` is the last segment up to `n` at which `p` holds. -/
def LastUpTo (p : Nat → Bool) (i n : Nat) : Prop :=
  i ≤ n ∧ p i = true ∧ ∀ t, i < t → t ≤ n → p t = false

/-- The conclusions of theorem M1 for an answer `a_n` with a nonzero permit, the last reset
acceptance `i` at or before `n`, and the last start `j` at or before `n`. -/
structure Permitted (x : Nat → Input) (n i j : Nat) : Prop where
  order : 1 ≤ i ∧ i < j ∧ j ≤ n
  lastAcceptance : LastUpTo (resetAcceptance x) i n
  lastStart : LastUpTo (start x) j n
  /-- Item 1: segments `i - 1` to `n` are good records. -/
  good : ∀ t, i - 1 ≤ t → t ≤ n → good (x t) = true
  /-- Item 1: each record from `i` to `n` has the sequence number of the record before it plus
  one, modulo `2 ^ 32`. -/
  sequence : ∀ t, i ≤ t → t ≤ n →
    (scanOf (x t)).seq = ((scanOf (x (t - 1))).seq + 1) % 2 ^ 32
  /-- Item 2: records `i` to `n` pass checks 7 to 17. -/
  content : ∀ t, i ≤ t → t ≤ n → contentFailureAt x t = none
  /-- Item 2: records `i` to `n` have `STOP_OK` 1. -/
  stopOk : ∀ t, i ≤ t → t ≤ n → (scanOf (x t)).stopOk = true
  /-- Item 3: a record before `i` passed the communication checks, and the last such record has
  `RESET` 0. -/
  resetReleased : ∃ u < i, passesComm x u = true ∧ (∀ v, u < v → v < i → passesComm x v = false) ∧
    (scanOf (x u)).reset = false
  /-- Item 3: record `i` has `RESET` 1, `RUN` 0, and the auxiliary word 0. -/
  resetPressed : (scanOf (x i)).reset = true ∧ (scanOf (x i)).run = false ∧
    (scanOf (x i)).auxWord = 0
  /-- Item 4: record `j` has `RUN` 1 and the auxiliary word 0. -/
  started : (scanOf (x j)).run = true ∧ (scanOf (x j)).auxWord = 0
  /-- Item 4: records `j` to `n` have `RUN` 1. -/
  run : ∀ t, j ≤ t → t ≤ n → (scanOf (x t)).run = true
  /-- Item 5: `a_(i - 1)` has state `RESET_REQUIRED` or `FAULT`. -/
  beforeAcceptance : (answerAt x (i - 1)).state = .resetRequired ∨
    (answerAt x (i - 1)).state = .fault
  /-- Item 5: `a_i` and `a_(j - 1)` have state `STANDBY`. -/
  standby : (answerAt x i).state = .standby ∧ (answerAt x (j - 1)).state = .standby
  /-- Item 5: no answer from `a_i` to `a_n` has state `RESET_REQUIRED` or `FAULT`. -/
  active : ∀ t, i ≤ t → t ≤ n →
    (answerAt x t).state ≠ .resetRequired ∧ (answerAt x t).state ≠ .fault
  /-- Item 6: with permit `0x03`, `a_j` to `a_n` have state `PRECHARGE`, and `n - j < N_pc`. -/
  precharge : (answerAt x n).permit = 0x03 →
    (∀ t, j ≤ t → t ≤ n → (answerAt x t).state = .precharge) ∧ n - j < nPc
  /-- Item 7: with permit `0x05`, a record `k` after `j` and at most `N_pc` segments after it
  meets the precharge condition, `a_j` to `a_(k - 1)` have state `PRECHARGE`, and `a_k` to `a_n`
  have state `NORMAL`. -/
  normal : (answerAt x n).permit = 0x05 →
    ∃ k, j < k ∧ k ≤ n ∧ k - j ≤ nPc ∧ prechargeCondition (scanOf (x k)) = true ∧
      (∀ t, j ≤ t → t < k → (answerAt x t).state = .precharge) ∧
      ∀ t, k ≤ t → t ≤ n → (answerAt x t).state = .normal

end Demos.Bms.Spec
