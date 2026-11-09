import Demos.Bms.Program
import Demos.Bms.Stream
import Library.Hashing.Crc.Bitwise.Proof
import LeanExe.Requests.DelimitedSteps

/-!
The BMS step of `Demos/Bms/Program.lean` against the machine of `Demos/Bms/Spec.lean` and the
delimited framing of `LeanExe/Requests/Delimited.lean`.

`absS` maps the machine's words to the specification's state: the protection state through
`modeOf`, the flags as `== 1`, and the counters through `toNat`.  `StInv` bounds the words as the
specification's values stay bounded, and the step keeps it.  `scanAbs` maps the program's record
fields to the specification's `Scan`, with the signed fields through `signed`, and
`decodeRec_spec` states that the fields that `decodeRec` reads from the last 35 bytes of a buffer
are those that `decodeScan` reads from those bytes.  `recCrc_spec` states that `recCrc` computes the
requirements' CRC of `LINK` and bytes 0 to 30, through `crc32Word_spec` from `linkCrc_spec`, and
`answerSrc_spec` that the last 17 bytes of `answerSrc` are an answer's 13 bytes and its CRC.

Each check of the program equals the specification's check as a `Bool` (`sensor_eq` to `aux_eq`),
`contentW_spec` and `failW_spec` state that the program's code of the first failing check is the
specification's, through the view `ViewOf` of a segment's result, and `rule4W_spec`,
`rule5W_spec`, `nextW_spec`, and `updW_spec` state the transitions and the next state.
`view_decode` states the view of the decoder's result, and `bmsDelim_spec` the window of a `0x00`
after a non-empty segment: the machine's next state and its answer, encoded and followed by
`0x00`.

`bmsPhases_abs` states that `bmsPhases` computes `delimTick` of `machine` with segments of at most
`maxSegment` bytes under `bmsAbs`, which takes the last `min len 36` bytes of the segment's buffer
and the first `k` bytes of the answer's, on the states of `BmsInv`, for every register map.
`bms_usart3_prefix`, `bms_usart3_answered`, `bms_cmsdk_prefix`, and `bms_cmsdk_answered` carry F3
to `bmsTickUsart3` and `bmsTick` through `reqTrace_mapOn`: for every bus and every sequence of the
values read, the bytes that the windows write begin `delimAnswers machine maxSegment init` of the
bytes read, and they are all of it whenever a window reads a byte.  `m1_prefix` states M1 for every
complete answer in a prefix of those bytes.
-/

namespace Demos.Bms.Program

open LeanExe.Requests
open LeanExe.Native (readReq writeReq)
open Demos.Bms.Spec
open Library.Hashing.Crc.Bitwise (crc32Word crc32Word_spec)

set_option linter.unusedSimpArgs false

/-! ## Bytes -/

theorem and_1 (x : Nat) : x &&& 1 = x % 2 := Nat.and_two_pow_sub_one_eq_mod x 1
theorem and_7 (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3
theorem and_255 (x : Nat) : x &&& 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8
theorem and_65535 (x : Nat) : x &&& 65535 = x % 65536 := Nat.and_two_pow_sub_one_eq_mod x 16
theorem and_4294967295 (x : Nat) : x &&& 4294967295 = x % 4294967296 :=
  Nat.and_two_pow_sub_one_eq_mod x 32

/-- A byte of a word, as a natural number. -/
macro "byte_eq" : tactic => `(tactic| (
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt8.toNat_ofNat', UInt64.toNat_shiftRight,
    UInt64.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, UInt64.toNat_and,
    UInt64.toNat_add, UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow, Nat.reduceMul,
    and_1, and_7, and_255, and_65535, and_4294967295] at *
  all_goals omega))

/-- Each conjunct of a conjunction of equations of bytes. -/
macro "bytes_eq" : tactic => `(tactic| (
  repeat' apply And.intro
  all_goals first | exact True.intro | byte_eq))

theorem wordBytes8_eq (w : UInt64) : wordBytes8 w = beBytes 8 w.toNat := by
  have := UInt64.toNat_lt w
  simp only [wordBytes8, beBytes, List.cons.injEq, and_true]
  bytes_eq

theorem sel_bytes (b : Bytes40) : b.bytes.drop 5 =
    [(b.w0 >>> 16).toUInt8, (b.w0 >>> 8).toUInt8, b.w0.toUInt8] ++ wordBytes8 b.w1 ++
      wordBytes8 b.w2 ++ wordBytes8 b.w3 ++ wordBytes8 b.w4 := by
  simp [Bytes40.bytes, wordBytes8]


/-- A field of the record as a natural number. -/
macro "field_eq" : tactic => `(tactic| (
  simp only [field, wordBytes8, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, List.take_succ_cons, List.take_zero, beValue, List.foldl_cons, List.foldl_nil]
  simp only [UInt64.toNat_toUInt8, UInt8.toNat_ofNat', UInt64.toNat_shiftRight,
    UInt64.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, UInt64.toNat_and,
    UInt64.toNat_add, UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow, Nat.reduceMul,
    Nat.mul_zero, Nat.zero_add, and_1, and_7, and_255, and_65535, and_4294967295] at *
  all_goals omega))

/-- The fields of the program's scan record as the specification's. -/
def scanAbs (sc : ScanW) : Scan where
  tag := sc.tag.toNat
  seq := sc.seq.toNat
  cells := [sc.c0.toNat, sc.c1.toNat, sc.c2.toNat, sc.c3.toNat]
  temps := [signed 16 sc.t0.toNat, signed 16 sc.t1.toNat]
  current := signed 32 sc.cur.toNat
  pack := sc.pack.toNat
  bus := sc.bus.toNat
  digital := sc.dig.toNat

/-- The widths of a scan record's fields. -/
structure ScanBounds (sc : ScanW) : Prop where
  tag : sc.tag.toNat < 2 ^ 8
  seq : sc.seq.toNat < 2 ^ 32
  c0 : sc.c0.toNat < 2 ^ 16
  c1 : sc.c1.toNat < 2 ^ 16
  c2 : sc.c2.toNat < 2 ^ 16
  c3 : sc.c3.toNat < 2 ^ 16
  t0 : sc.t0.toNat < 2 ^ 16
  t1 : sc.t1.toNat < 2 ^ 16
  cur : sc.cur.toNat < 2 ^ 32
  pack : sc.pack.toNat < 2 ^ 32
  bus : sc.bus.toNat < 2 ^ 32
  dig : sc.dig.toNat < 2 ^ 16

theorem decodeRec_bounds (b : Bytes40) : ScanBounds (decodeRec b) := by
  have h0 := UInt64.toNat_lt b.w0
  have h1 := UInt64.toNat_lt b.w1
  have h2 := UInt64.toNat_lt b.w2
  have h3 := UInt64.toNat_lt b.w3
  have h4 := UInt64.toNat_lt b.w4
  constructor <;>
  simp only [decodeRec, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, UInt64.toNat_and, UInt64.toNat_add, UInt64.reduceToNat, Nat.reduceMod,
    Nat.reducePow, Nat.reduceMul, and_1, and_7, and_255, and_65535, and_4294967295] at * <;> omega

/-- The program's fields of the record in the last 35 bytes of a buffer are the specification's
fields of those bytes. -/
theorem decodeRec_spec (b : Bytes40) : decodeScan (b.bytes.drop 5) = scanAbs (decodeRec b) := by
  have h0 := UInt64.toNat_lt b.w0
  have h1 := UInt64.toNat_lt b.w1
  have h2 := UInt64.toNat_lt b.w2
  have h3 := UInt64.toNat_lt b.w3
  have h4 := UInt64.toNat_lt b.w4
  rw [sel_bytes]
  show Scan.mk _ _ [_, _, _, _] [signed 16 _, signed 16 _] _ _ _ _ = _
  simp only [scanAbs, decodeRec, Scan.mk.injEq, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> (try congr 1) <;> field_eq


/-! ## The CRC -/

/-- The bytes of `LINK` in two words, eight to a word in little-endian order, as the table
program of `Library.Hashing.Crc` reads them. -/
def linkWords : Array UInt64 := #[0x2d6578456e61654c, 0x313030302d534d42]

theorem linkWords_bytes : Library.Hashing.Crc.Proof.messageBytes linkWords 16 = link := by
  decide +kernel

theorem crc32_linkWords : Library.Hashing.Crc.crc32 linkWords 16 = linkCrc := by decide +kernel

/-- `linkCrc` is the CRC-32 of `LINK`. -/
theorem linkCrc_spec : linkCrc.toNat = Library.Hashing.Crc.Spec.crc32 link := by
  have h := Library.Hashing.Crc.Proof.crc32_spec linkWords 16
  rw [crc32_linkWords] at h
  rw [← linkWords_bytes]
  exact h

theorem min1 : min (1 : UInt64).toNat 8 = 1 := rfl
theorem min3 : min (3 : UInt64).toNat 8 = 3 := rfl
theorem min4 : min (4 : UInt64).toNat 8 = 4 := rfl
theorem min8 : min (8 : UInt64).toNat 8 = 8 := rfl

/-- `crc` of the requirements as CRC-32 of `LINK` followed by the bytes. -/
theorem crc_eq (bs : List UInt8) : crc bs = Library.Hashing.Crc.Spec.crc32 (link ++ bs) := by
  rw [Library.Hashing.Crc.Division.crc32_eq]
  rfl

theorem crc_lt (bs : List UInt8) : crc bs < 2 ^ 32 :=
  Library.Hashing.Crc.Proof.bitsValue_lt _

/-- `recCrc` computes the CRC of `LINK` and bytes 0 to 30 of the record in the last 35 bytes of
the buffer. -/
theorem recCrc_spec (b : Bytes40) : (recCrc b).toNat = crc ((b.bytes.drop 5).take 31) := by
  have e0 := crc32Word_spec link linkCrc linkCrc_spec (b.w0 <<< 40) 3
  have e1 := crc32Word_spec _ _ e0 b.w1 8
  have e2 := crc32Word_spec _ _ e1 b.w2 8
  have e3 := crc32Word_spec _ _ e2 b.w3 8
  have e4 := crc32Word_spec _ _ e3 b.w4 4
  have h0 := UInt64.toNat_lt b.w0
  have h1 := UInt64.toNat_lt b.w1
  have h2 := UInt64.toNat_lt b.w2
  have h3 := UInt64.toNat_lt b.w3
  have h4 := UInt64.toNat_lt b.w4
  show (crc32Word (crc32Word (crc32Word (crc32Word (crc32Word linkCrc (b.w0 <<< 40) 3) b.w1 8)
    b.w2 8) b.w3 8) b.w4 4).toNat = _
  rw [e4, crc_eq, sel_bytes]
  simp only [List.append_assoc]
  apply congrArg Library.Hashing.Crc.Spec.crc32
  apply congrArg (link ++ ·)
  simp only [min3, min4, min8]
  simp only [wordBytes, wordBytes8, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.cons.injEq, and_true]
  bytes_eq

/-- The bytes of an answer with the fields `board`, `answered`, `permit`, `state`, and `code`
before its CRC. -/
def bodyOf (board answered permit state code : Nat) : List UInt8 :=
  beBytes 1 answerTag ++ beBytes 4 board ++ beBytes 4 answered ++ beBytes 1 permit ++
    beBytes 1 state ++ beBytes 2 code

/-- The last 17 bytes of `answerSrc` are the answer's bytes and its CRC. -/
theorem answerSrc_spec (board answered permit state code : UInt64) (hb : board.toNat < 2 ^ 32)
    (ha : answered.toNat < 2 ^ 32) (hs : state.toNat < 2 ^ 8)
    (hc : code.toNat < 2 ^ 16) :
    (answerSrc board answered permit state code).bytes.drop 23 =
      bodyOf board.toNat answered.toNat permit.toNat state.toNat code.toNat ++
        beBytes 4 (crc (bodyOf board.toNat answered.toNat permit.toNat state.toNat code.toNat)) := by
  have e0 := crc32Word_spec link linkCrc linkCrc_spec 0x8000000000000000 1
  have e1 := crc32Word_spec _ _ e0 ((board <<< 32) + answered) 8
  have e2 := crc32Word_spec _ _ e1 ((permit <<< 56) + (state <<< 48) + (code <<< 32)) 4
  have hbody : link ++ (wordBytes 0x8000000000000000 (min (1 : UInt64).toNat 8)).map
      UInt64.toUInt8 ++ (wordBytes ((board <<< 32) + answered) (min (8 : UInt64).toNat 8)).map
      UInt64.toUInt8 ++ (wordBytes ((permit <<< 56) + (state <<< 48) + (code <<< 32))
      (min (4 : UInt64).toNat 8)).map UInt64.toUInt8 =
      link ++ bodyOf board.toNat answered.toNat permit.toNat state.toNat code.toNat := by
    simp only [List.append_assoc]
    apply congrArg (link ++ ·)
    simp only [min1, min4, min8]
    simp only [bodyOf, answerTag, beBytes, wordBytes,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.cons.injEq, and_true]
    bytes_eq
  rw [hbody, ← crc_eq] at e2
  have hC := crc_lt (bodyOf board.toNat answered.toNat permit.toNat state.toNat code.toNat)
  generalize crc (bodyOf board.toNat answered.toNat permit.toNat state.toNat code.toNat) = C
    at e2 hC
  clear e0 e1 hbody
  show ([(0x80 : UInt64).toUInt8] ++ wordBytes8 ((board <<< 32) + answered) ++
    wordBytes8 ((permit <<< 56) + (state <<< 48) + (code <<< 32) +
      crc32Word (crc32Word (crc32Word linkCrc 0x8000000000000000 1) ((board <<< 32) + answered)
        8) ((permit <<< 56) + (state <<< 48) + (code <<< 32)) 4)) = _
  generalize crc32Word (crc32Word (crc32Word linkCrc 0x8000000000000000 1)
    ((board <<< 32) + answered) 8) ((permit <<< 56) + (state <<< 48) + (code <<< 32)) 4 = W at e2
  simp only [bodyOf, answerTag, beBytes, wordBytes8, List.cons_append, List.nil_append,
    List.cons.injEq, and_true]
  bytes_eq


/-! ## The machine's state -/

/-- The protection state with the code `w`. -/
def modeOf (w : UInt64) : Mode :=
  if w = 1 then .standby else if w = 2 then .precharge else if w = 3 then .normal
  else if w = 4 then .fault else .resetRequired

/-- The specification's state that the program's state holds. -/
def absS (s : BmsState) : State where
  mode := modeOf s.mode
  diag := s.diag.toNat
  synced := s.synced == 1
  expected := s.expected.toNat
  answers := s.answers.toNat
  prevReset := s.prevReset == 1
  age := [s.age0.toNat, s.age1.toNat, s.age2.toNat]
  pcCount := s.pcCount.toNat
  first := s.first == 1

/-- The ranges of the machine's words: a state code from 0 to 4, a code of 16 bits, flags 0 or 1,
sequence numbers of 32 bits, ages up to `D_edm`, and a precharge count below `N_pc`. -/
structure StInv (s : BmsState) : Prop where
  mode : s.mode.toNat ≤ 4
  diag : s.diag.toNat < 2 ^ 16
  synced : s.synced = 0 ∨ s.synced = 1
  expected : s.expected.toNat < 2 ^ 32
  answers : s.answers.toNat < 2 ^ 32
  prevReset : s.prevReset = 0 ∨ s.prevReset = 1
  age0 : s.age0.toNat ≤ 2
  age1 : s.age1.toNat ≤ 2
  age2 : s.age2.toNat ≤ 2
  pcCount : s.pcCount.toNat < 10
  first : s.first = 0 ∨ s.first = 1

theorem mode_cases {w : UInt64} (h : w.toNat ≤ 4) : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 := by
  have : w.toNat = 0 ∨ w.toNat = 1 ∨ w.toNat = 2 ∨ w.toNat = 3 ∨ w.toNat = 4 := by omega
  rcases this with h | h | h | h | h
  · exact Or.inl (UInt64.toNat_inj.mp h)
  · exact Or.inr (Or.inl (UInt64.toNat_inj.mp h))
  · exact Or.inr (Or.inr (Or.inl (UInt64.toNat_inj.mp h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (UInt64.toNat_inj.mp h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (UInt64.toNat_inj.mp h))))

theorem modeOf_code {w : UInt64} (h : w.toNat ≤ 4) : (modeOf w).code = w.toNat := by
  rcases mode_cases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem permitOf_toNat (w : UInt64) : (permitOf w).toNat = (modeOf w).permit := by
  unfold permitOf modeOf
  by_cases h1 : w = 1 <;> by_cases h2 : w = 2 <;> by_cases h3 : w = 3 <;> by_cases h4 : w = 4 <;>
    simp_all [Mode.permit]

/-- The code of a failing check as a word, and 0 when every check passes. -/
def optCode : Option Nat → UInt64
  | none => 0
  | some c => UInt64.ofNat c

theorem firstFailure_cons (b : Bool) (c : Nat) (cs : List (Bool × Nat)) :
    firstFailure ((b, c) :: cs) = if b then some c else firstFailure cs := by
  cases b <;> simp [firstFailure, List.find?]

theorem firstFailure_nil : firstFailure [] = none := rfl

theorem optCode_ite (p : Prop) [Decidable p] (a : Nat) (x : Option Nat) :
    optCode (if p then some a else x) = if p then UInt64.ofNat a else optCode x := by
  split <;> rfl

/-! ## The checks -/

theorem bias16_toNat (t : UInt64) : (bias16 t).toNat = (t.toNat + 32768) % 65536 := by
  simp only [bias16, UInt64.toNat_and, UInt64.toNat_add, UInt64.reduceToNat, and_65535]
  omega

theorem signed16_eq {t : UInt64} (h : t.toNat < 2 ^ 16) :
    signed 16 t.toNat = ((bias16 t).toNat : Int) - 32768 := by
  rw [bias16_toNat, signed]
  split <;> omega

theorem bias32_toNat (c : UInt64) : (bias32 c).toNat = (c.toNat + 2147483648) % 4294967296 := by
  simp only [bias32, UInt64.toNat_and, UInt64.toNat_add, UInt64.reduceToNat, and_4294967295]
  omega

theorem signed32_eq {c : UInt64} (h : c.toNat < 2 ^ 32) :
    signed 32 c.toNat = ((bias32 c).toNat : Int) - 2147483648 := by
  rw [bias32_toNat, signed]
  split <;> omega

theorem bitW_toNat (w r : UInt64) : (bitW w r).toNat = w.toNat / 2 ^ (r.toNat % 64) % 2 := by
  simp only [bitW, UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    UInt64.reduceToNat, and_1]

theorem testBit_eq (w : UInt64) (r : Nat) :
    w.toNat.testBit r = decide (w.toNat / 2 ^ r % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq

theorem natAbs_le_iff (z : Int) (a : Nat) : z.natAbs ≤ a ↔ -(a : Int) ≤ z ∧ z ≤ a := by omega

theorem lt_natAbs_iff (a : Nat) (z : Int) : a < z.natAbs ↔ (a : Int) < z ∨ z < -(a : Int) := by
  omega

/-- A Bool equation as an equivalence of propositions over the words' values. -/
macro "flag_eq" : tactic => `(tactic| (
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, UInt64.lt_iff_toNat_lt,
    UInt64.le_iff_toNat_le, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true',
    UInt64.toNat_add, UInt64.reduceToNat, testBit_eq, bitW_toNat, Nat.reduceMod, Nat.reducePow,
    UInt64.toNat_inj.symm.eq, List.any_cons, List.any_nil, Bool.or_false, UInt64.toNat_and,
    and_7, decide_eq_decide, natAbs_le_iff, lt_natAbs_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, List.getD_cons_zero, List.getD_cons_succ, and_true, true_and,
    not_true_eq_false, and_false, false_and, not_false_eq_true, Nat.zero_ne_one, Nat.one_ne_zero]
  try simp only [vMax, vMin, tMax, tMin, tChgMin, tChgMax, iChgMax, iDisMax, iChgDetect, vSensLo,
    vSensHi, tSensLo, tSensHi, pSensHi, tolSum, tolPc, dEdm]
  all_goals omega))

theorem reserved_eq {sc : ScanW} (hb : ScanBounds sc) :
    (scanAbs sc).reserved = decide (64 ≤ sc.dig) := by
  have := hb.dig
  simp only [Scan.reserved, scanAbs, List.range, List.range.loop]
  flag_eq


theorem sensor_eq {sc : ScanW} (hb : ScanBounds sc) : sensorFault (scanAbs sc) = sensorW sc := by
  have := hb.c0; have := hb.c1; have := hb.c2; have := hb.c3; have := hb.pack; have := hb.bus
  simp only [sensorFault, scanAbs, sensorW, cellOutW, tempOutW, signed16_eq hb.t0,
    signed16_eq hb.t1]
  flag_eq

theorem overV_eq {sc : ScanW} : ((scanAbs sc).cells.any fun c => vMax < c) = overVW sc := by
  simp only [scanAbs, overVW]
  flag_eq

theorem underV_eq {sc : ScanW} : ((scanAbs sc).cells.any fun c => c < vMin) = underVW sc := by
  simp only [scanAbs, underVW]
  flag_eq

theorem overT_eq {sc : ScanW} (hb : ScanBounds sc) :
    ((scanAbs sc).temps.any fun t => tMax < t) = overTW sc := by
  simp only [scanAbs, overTW, signed16_eq hb.t0, signed16_eq hb.t1]
  flag_eq

theorem underT_eq {sc : ScanW} (hb : ScanBounds sc) :
    ((scanAbs sc).temps.any fun t => t < tMin) = underTW sc := by
  simp only [scanAbs, underTW, signed16_eq hb.t0, signed16_eq hb.t1]
  flag_eq

theorem chgOver_eq {sc : ScanW} (hb : ScanBounds sc) :
    decide (iChgMax < (scanAbs sc).current) = chgOverW sc := by
  simp only [scanAbs, chgOverW, signed32_eq hb.cur]
  flag_eq

theorem disOver_eq {sc : ScanW} (hb : ScanBounds sc) :
    decide ((scanAbs sc).current < -iDisMax) = disOverW sc := by
  simp only [scanAbs, disOverW, signed32_eq hb.cur]
  flag_eq

theorem chgTemp_eq {sc : ScanW} (hb : ScanBounds sc) :
    chargeTempFault (scanAbs sc) = chgTempW sc := by
  simp only [chargeTempFault, scanAbs, chgTempW, chgOutW, signed32_eq hb.cur,
    signed16_eq hb.t0, signed16_eq hb.t1]
  flag_eq

theorem sum_eq {sc : ScanW} (hb : ScanBounds sc) : sumFault (scanAbs sc) = sumW sc := by
  have := hb.c0; have := hb.c1; have := hb.c2; have := hb.c3; have := hb.pack
  simp only [sumFault, scanAbs, sumW, List.sum_cons, List.sum_nil]
  flag_eq

theorem pcCond_eq {sc : ScanW} (hb : ScanBounds sc) :
    prechargeCondition (scanAbs sc) = pcCondW sc := by
  have := hb.pack; have := hb.bus
  simp only [prechargeCondition, Scan.aux, scanAbs, pcCondW]
  flag_eq

theorem stopOk_eq {sc : ScanW} : (scanAbs sc).stopOk = (bitW sc.dig 3 == 1) := by
  simp only [Scan.stopOk, scanAbs]
  flag_eq

theorem reset_eq {sc : ScanW} : (scanAbs sc).reset = (bitW sc.dig 4 == 1) := by
  simp only [Scan.reset, scanAbs]
  flag_eq

theorem run_eq {sc : ScanW} : (scanAbs sc).run = (bitW sc.dig 5 == 1) := by
  simp only [Scan.run, scanAbs]
  flag_eq

theorem accept_eq {s : BmsState} (hs : StInv s) {sc : ScanW} :
    acceptanceWith (absS s).synced (absS s).prevReset (scanAbs sc) = acceptW s sc := by
  have := hs.prevReset
  simp only [acceptanceWith, absS, Scan.reset, Scan.run, Scan.auxWord, scanAbs, acceptW,
    UInt64.toNat_and, and_7]
  rcases hs.prevReset with h | h <;> rw [h] <;> flag_eq

theorem start_eq {sc : ScanW} : startCondition (scanAbs sc) = startW sc := by
  simp only [startCondition, Scan.run, Scan.auxWord, scanAbs, startW, UInt64.toNat_and, and_7]
  flag_eq

theorem aux_eq {s : BmsState} {sc : ScanW} :
    auxFault (absS s).mode.permit (absS s).age (scanAbs sc) = auxW (permitOf s.mode) s sc := by
  simp only [absS, scanAbs, ← permitOf_toNat]
  simp only [auxFault, Scan.aux, auxW, List.range, List.range.loop]
  flag_eq


/-- The program's checks 7 to 17 are the specification's. -/
theorem contentW_spec {s : BmsState} {sc : ScanW} (hb : ScanBounds sc) :
    contentW (permitOf s.mode) s sc =
      optCode (firstFailure (contentChecks (absS s).mode.permit (absS s).age (scanAbs sc))) := by
  rw [contentChecks, aux_eq, chgTemp_eq hb, sum_eq hb, disOver_eq hb, chgOver_eq hb, underT_eq hb,
    overT_eq hb, underV_eq, overV_eq, sensor_eq hb, reserved_eq hb]
  simp only [firstFailure_cons, firstFailure_nil, decide_eq_true_eq, optCode_ite]
  rfl

/-- The program's view of a segment's result `x`: `kind` 2 for an overflow, 1 for a decode error,
and 0 for decoded bytes, of which `olen` gives the number, and for a record of 35 bytes, the
specification's fields `scanAbs sc` and whether its CRC field matches, `crcOk`. -/
def ViewOf (kind olen : UInt64) (crcOk : Bool) (sc : ScanW) (x : Input) : Prop :=
  (kind = 2 ∧ x = .error .overflow) ∨ (kind = 1 ∧ x = .error .decode) ∨
    (kind = 0 ∧ ∃ bs, x = .ok bs ∧ olen.toNat = bs.length ∧
      (bs.length = 35 → decodeScan bs = scanAbs sc ∧ crcOk = Spec.crcOk x))

/-- The program's checks 1 to 17 are the specification's. -/
theorem failW_spec {s : BmsState} {kind olen : UInt64} {crcOk : Bool}
    {sc : ScanW} (hb : ScanBounds sc) {x : Input} (hv : ViewOf kind olen crcOk sc x) :
    failW s kind olen crcOk sc = optCode (failure (absS s) x) := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, bs, rfl, hl, hr⟩
  · rfl
  · rfl
  · by_cases h35 : bs.length = 35
    · obtain ⟨hd, hc⟩ := hr h35
      have ho : olen = 35 := UInt64.toNat_inj.mp (by rw [hl, h35]; rfl)
      subst ho
      have hsc : scanOf (.ok bs) = scanAbs sc := hd
      have ht : (!((scanAbs sc).tag == scanTag)) = (sc.tag != 0x10) := by
        simp only [scanAbs, scanTag]
        flag_eq
      have hq : ((absS s).synced && (scanAbs sc).seq != (absS s).expected) =
          (s.synced == 1 && sc.seq != s.expected) := by
        simp only [scanAbs, absS]
        flag_eq
      simp only [Spec.failure, checks, recordChecks, List.cons_append, List.nil_append,
        firstFailure_cons, isError, lengthOk, bytesOf, h35, scanLength, ← hc, tagOk, hsc,
        seqFault, ht, hq, optCode_ite]
      rw [← contentW_spec hb]
      rfl
    · have ho : olen ≠ 35 := fun h => h35 (by rw [← hl, h]; rfl)
      simp only [Spec.failure, checks, recordChecks, List.cons_append, List.nil_append,
        firstFailure_cons, isError, lengthOk, bytesOf, scanLength, optCode_ite]
      unfold failW
      simp [ho, h35]
      rfl


/-! ## The transitions -/

/-- The specification's next state, code, and precharge count that the words hold. -/
def absN (n : NextW) : Next := ⟨modeOf n.mode, n.diag.toNat, n.pcCount.toNat⟩

/-- The ranges of the next state's words. -/
structure NInv (n : NextW) : Prop where
  mode : n.mode.toNat ≤ 4
  diag : n.diag.toNat < 2 ^ 16
  pcCount : n.pcCount.toNat < 10

theorem modeOf_0 : modeOf 0 = .resetRequired := rfl
theorem modeOf_1 : modeOf 1 = .standby := rfl
theorem modeOf_2 : modeOf 2 = .precharge := rfl
theorem modeOf_3 : modeOf 3 = .normal := rfl
theorem modeOf_4 : modeOf 4 = .fault := rfl

theorem bitW_zero (w r : UInt64) : (bitW w r == 0) = !(bitW w r == 1) := by
  have h := bitW_toNat w r
  rcases Nat.mod_two_eq_zero_or_one (w.toNat / 2 ^ (r.toNat % 64)) with e | e <;>
    rw [e] at h
  · rw [show bitW w r = 0 from UInt64.toNat_inj.mp h]
    rfl
  · rw [show bitW w r = 1 from UInt64.toNat_inj.mp h]
    rfl

theorem pc_le {p : UInt64} (h : p.toNat < 10) : (10 ≤ p + 1) ↔ nPc ≤ p.toNat + 1 := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]
  simp only [UInt64.reduceToNat, nPc]
  omega

theorem rule4W_spec {s : BmsState} (hs : StInv s) :
    absN (rule4W s) = rule4 (absS s) ∧ NInv (rule4W s) := by
  have := hs.diag; have := hs.pcCount
  rcases mode_cases hs.mode with h | h | h | h | h <;>
    simp [rule4W, rule4, absN, absS, h, modeOf_0, modeOf_1, modeOf_2, modeOf_3, modeOf_4,
      codeStop] <;> constructor <;> simp_all

theorem rule5W_inv {s : BmsState} (hs : StInv s) (sc : ScanW) : NInv (rule5W s sc) := by
  have := hs.mode; have := hs.diag; have := hs.pcCount
  unfold rule5W
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> constructor <;>
    simp only [UInt64.toNat_add, UInt64.reduceToNat, UInt64.le_iff_toNat_le] at * <;> omega

theorem rule5W_spec {s : BmsState} (hs : StInv s) {sc : ScanW} (hb : ScanBounds sc) :
    absN (rule5W s sc) = rule5 (absS s) (scanAbs sc) ∧ NInv (rule5W s sc) := by
  refine ⟨?_, rule5W_inv hs sc⟩
  have := hs.diag; have hp := hs.pcCount
  rcases mode_cases hs.mode with h | h | h | h | h
  · have hm : (absS s).mode = .resetRequired := by simp [absS, h, modeOf_0]
    simp only [rule5, hm, accept_eq hs]
    unfold rule5W
    simp only [h]
    split_ifs <;> simp_all [absN, absS, modeOf_0, modeOf_1, codeNone]
  · have hm : (absS s).mode = .standby := by simp [absS, h, modeOf_1]
    simp only [rule5, hm, start_eq]
    unfold rule5W
    simp only [h]
    split_ifs <;> simp_all [absN, absS, modeOf_1, modeOf_2]
  · have hm : (absS s).mode = .precharge := by simp [absS, h, modeOf_2]
    simp only [rule5, hm, run_eq, pcCond_eq hb, ← bitW_zero]
    unfold rule5W
    simp only [h, pc_le hp]
    split_ifs <;> simp_all [absN, absS, modeOf_1, modeOf_2, modeOf_3, modeOf_4, codePrecharge,
      nPc, UInt64.toNat_add] <;> omega
  · have hm : (absS s).mode = .normal := by simp [absS, h, modeOf_3]
    simp only [rule5, hm, run_eq, ← bitW_zero]
    unfold rule5W
    simp only [h]
    split_ifs <;> simp_all [absN, absS, modeOf_1, modeOf_3]
  · have hm : (absS s).mode = .fault := by simp [absS, h, modeOf_4]
    simp only [rule5, hm, accept_eq hs]
    unfold rule5W
    simp only [h]
    split_ifs <;> simp_all [absN, absS, modeOf_1, modeOf_4, codeNone]


theorem failure_pos {s : State} {x : Input} {c : Nat} (h : Spec.failure s x = some c) : 0 < c := by
  have := firstFailure_mem h
  rw [checks_codes] at this
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (subst h; decide)

/-- A segment that passes every check is a record of 35 bytes, whose fields the program holds. -/
theorem view_pass {s : BmsState} {kind olen : UInt64} {crcOk : Bool} {sc : ScanW} {x : Input}
    (hv : ViewOf kind olen crcOk sc x) (hf : Spec.failure (absS s) x = none) :
    kind = 0 ∧ olen = 35 ∧ crcOk = true ∧ scanOf x = scanAbs sc ∧ good x = true := by
  have hg : good x = true := (checks_none_iff.mp hf).1
  rcases hv with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, bs, rfl, hl, hr⟩
  · simp [good, recordChecks, isError] at hg
  · simp [good, recordChecks, isError] at hg
  · have h35 : bs.length = 35 := by
      simp only [good, recordChecks, isError, lengthOk, bytesOf, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, scanLength] at hg
      simpa using hg.2.2.1
    obtain ⟨hd, hc⟩ := hr h35
    refine ⟨rfl, UInt64.toNat_inj.mp (by rw [hl, h35]; rfl), ?_, hd, hg⟩
    rw [hc]
    simp only [good, recordChecks, List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hg
    simpa using hg.2.2.2.1

theorem nextW_spec {s : BmsState} (hs : StInv s) {kind olen : UInt64} {crcOk : Bool}
    {sc : ScanW} (hb : ScanBounds sc) {x : Input} (hv : ViewOf kind olen crcOk sc x) :
    absN (nextW s (failW s kind olen crcOk sc) sc) = next (absS s) x ∧
      NInv (nextW s (failW s kind olen crcOk sc) sc) := by
  rw [failW_spec hb hv]
  cases hf : Spec.failure (absS s) x with
  | some c =>
    have h1 := failure_lt hf
    have h2 := failure_pos hf
    rw [next_failure hf]
    have hc : (UInt64.ofNat c).toNat = c := UInt64.toNat_ofNat_of_lt' (by
      simp only [UInt64.size]; omega)
    have hne : (UInt64.ofNat c != 0) = true := by
      simp only [bne_iff_ne, ne_eq, UInt64.toNat_inj.symm.eq, hc, UInt64.reduceToNat]
      omega
    have := hs.diag; have := hs.pcCount
    simp only [nextW, optCode, hne, ↓reduceIte, absN, modeOf_4]
    rcases mode_cases hs.mode with h | h | h | h | h <;>
      simp [absS, h, modeOf_0, modeOf_1, modeOf_2, modeOf_3, modeOf_4, hc] <;>
      constructor <;> simp_all <;> omega
  | none =>
    obtain ⟨-, -, -, hx, -⟩ := view_pass hv hf
    rw [next_pass hf, hx, stopOk_eq]
    simp only [nextW, optCode, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    split
    · exact rule5W_spec hs hb
    · exact rule4W_spec hs


/-! ## The step -/

theorem view_good {kind olen : UInt64} {crcOk : Bool} {sc : ScanW} {x : Input}
    (hv : ViewOf kind olen crcOk sc x) (hg : good x = true) : scanOf x = scanAbs sc := by
  rcases hv with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, bs, rfl, -, hr⟩
  · simp [good, recordChecks, isError] at hg
  · simp [good, recordChecks, isError] at hg
  · have h35 : bs.length = 35 := by
      simp only [good, recordChecks, isError, lengthOk, bytesOf, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, scanLength] at hg
      simpa using hg.2.2.1
    exact (hr h35).1

theorem goodW_eq {kind olen : UInt64} {crcOk : Bool} {sc : ScanW} {x : Input}
    (hv : ViewOf kind olen crcOk sc x) : goodW kind olen crcOk sc = good x := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, bs, rfl, hl, hr⟩
  · rfl
  · rfl
  · by_cases h35 : bs.length = 35
    · obtain ⟨hd, hc⟩ := hr h35
      have ho : olen = 35 := UInt64.toNat_inj.mp (by rw [hl, h35]; rfl)
      subst ho
      have ht : (sc.tag == 0x10) = ((scanAbs sc).tag == scanTag) := by
        simp only [scanAbs, scanTag]
        flag_eq
      simp only [goodW, good, recordChecks, isError, lengthOk, bytesOf, List.all_cons,
        List.all_nil, h35, scanLength, ← hc, tagOk, scanOf, hd, ht]
      cases crcOk <;> simp
    · have ho : (olen == 35) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        exact h35 (by rw [← hl, h]; rfl)
      simp only [goodW, good, recordChecks, isError, lengthOk, bytesOf, List.all_cons,
        List.all_nil, h35, scanLength, ho]
      simp [h35]

theorem answered_eq {kind olen : UInt64} {crcOk : Bool} {sc : ScanW} {x : Input}
    (hv : ViewOf kind olen crcOk sc x) :
    (if kind == 0 && olen == 35 && crcOk then sc.seq else 0xFFFFFFFF).toNat =
      if lengthOk x && Spec.crcOk x then (scanOf x).seq else unanswered := by
  rcases hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, bs, rfl, hl, hr⟩
  · rfl
  · rfl
  · by_cases h35 : bs.length = 35
    · obtain ⟨hd, hc⟩ := hr h35
      have ho : olen = 35 := UInt64.toNat_inj.mp (by rw [hl, h35]; rfl)
      subst ho
      simp only [lengthOk, bytesOf, h35, scanLength, ← hc, scanOf, hd]
      cases crcOk <;> rfl
    · have ho : (olen == 35) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h
        exact h35 (by rw [← hl, h]; rfl)
      simp [lengthOk, bytesOf, h35, scanLength, ho, unanswered]

theorem commW_eq {s : BmsState} {kind olen : UInt64} {crcOk : Bool} {sc : ScanW} {x : Input}
    (hv : ViewOf kind olen crcOk sc x) :
    (goodW kind olen crcOk sc && !(s.synced == 1 && sc.seq != s.expected)) =
      passesCommWith (absS s).synced (absS s).expected x := by
  rw [goodW_eq hv, passesCommWith]
  cases hg : good x
  · rfl
  · rw [seqFault, view_good hv hg]
    simp only [absS, scanAbs, Bool.true_and]
    congr 1
    flag_eq

theorem bitW_ne (P Q r : UInt64) :
    (bitW P r != bitW Q r) = (P.toNat.testBit (r.toNat % 64) != Q.toNat.testBit (r.toNat % 64)) := by
  flag_eq

theorem ageW_toNat {first : UInt64} (ch comm : Bool) {a : UInt64}
    (ha : a.toNat ≤ 2) :
    (ageW first ch comm a).toNat =
      if (first == 1) || ch then 0 else if comm then min (a.toNat + 1) dEdm else a.toNat := by
  unfold ageW
  split_ifs <;> simp_all [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, dEdm] <;> omega

theorem ageW_le {first : UInt64} (ch comm : Bool) {a : UInt64} (ha : a.toNat ≤ 2) :
    (ageW first ch comm a).toNat ≤ 2 := by
  unfold ageW
  split_ifs <;> simp_all [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  omega

theorem bitW_01 (w r : UInt64) : bitW w r = 0 ∨ bitW w r = 1 := by
  have h := bitW_toNat w r
  rcases Nat.mod_two_eq_zero_or_one (w.toNat / 2 ^ (r.toNat % 64)) with e | e <;> rw [e] at h
  · exact Or.inl (UInt64.toNat_inj.mp h)
  · exact Or.inr (UInt64.toNat_inj.mp h)


/-- The program's next state of the machine is the specification's. -/
theorem updW_spec {s : BmsState} (hs : StInv s) {kind olen : UInt64} {crcOk : Bool}
    {sc : ScanW} (hb : ScanBounds sc) {x : Input} (hv : ViewOf kind olen crcOk sc x) :
    absS (updW s (goodW kind olen crcOk sc)
        (goodW kind olen crcOk sc && !(s.synced == 1 && sc.seq != s.expected)) sc
        (nextW s (failW s kind olen crcOk sc) sc)) = (step (absS s) x).1 ∧
      StInv (updW s (goodW kind olen crcOk sc)
        (goodW kind olen crcOk sc && !(s.synced == 1 && sc.seq != s.expected)) sc
        (nextW s (failW s kind olen crcOk sc) sc)) := by
  obtain ⟨hn, hni⟩ := nextW_spec hs hb hv
  rw [commW_eq hv, goodW_eq hv]
  generalize nextW s (failW s kind olen crcOk sc) sc = n at hn hni
  have hmode : (next (absS s) x).mode = modeOf n.mode := by rw [← hn]; rfl
  have hdiag : (next (absS s) x).diag = n.diag.toNat := by rw [← hn]; rfl
  have hpc : (next (absS s) x).pcCount = n.pcCount.toNat := by rw [← hn]; rfl
  have hcg : passesCommWith (absS s).synced (absS s).expected x = true → good x = true := by
    intro h
    simp only [passesCommWith, Bool.and_eq_true] at h
    exact h.1
  simp only [step]
  generalize passesCommWith (absS s).synced (absS s).expected x = c at hcg ⊢
  have := hb.seq; have := hs.answers; have := hs.expected
  have ha0 := hs.age0; have ha1 := hs.age1; have ha2 := hs.age2
  constructor
  · simp only [hmode, hdiag, hpc]
    simp only [absS, updW, State.mk.injEq]
    refine ⟨trivial, trivial, ?_, ?_, ?_, ?_, ?_, trivial, rfl⟩
    · cases good x <;> rfl
    · cases hg : good x
      · rfl
      · rw [view_good hv hg]
        simp only [scanAbs, ↓reduceIte, UInt64.toNat_and, UInt64.toNat_add, UInt64.reduceToNat,
          and_4294967295]
        omega
    · simp only [UInt64.toNat_and, UInt64.toNat_add, UInt64.reduceToNat, and_4294967295]
      omega
    · cases c
      · rfl
      · rw [view_good hv (hcg rfl), reset_eq]
        rfl
    · rw [ageW_toNat _ _ ha0, ageW_toNat _ _ ha1, ageW_toNat _ _ ha2,
        bitW_ne, bitW_ne, bitW_ne, permitOf_toNat, permitOf_toNat]
      rfl
  · simp only [updW]
    refine ⟨hni.mode, hni.diag, ?_, ?_, ?_, ?_, ageW_le _ _ ha0, ageW_le _ _ ha1, ageW_le _ _ ha2,
      hni.pcCount, Or.inl rfl⟩
    · cases good x <;> simp
    · split
      · simp only [UInt64.toNat_and, UInt64.toNat_add, UInt64.reduceToNat, and_4294967295]
        omega
      · exact hs.expected
    · simp only [UInt64.toNat_and, UInt64.toNat_add, UInt64.reduceToNat, and_4294967295]
      omega
    · cases c
      · exact hs.prevReset
      · exact bitW_01 _ _


/-! ## The window of a delimiter -/

theorem crcField_eq (b : Bytes40) : field (b.bytes.drop 5) 31 4 = (b.w4 &&& 0xFFFFFFFF).toNat := by
  have h4 := UInt64.toNat_lt b.w4
  rw [sel_bytes]
  field_eq

theorem crcOk_eq (b : Bytes40) :
    (recCrc b == (b.w4 &&& 0xFFFFFFFF)) = Spec.crcOk (.ok (b.bytes.drop 5)) := by
  simp only [Spec.crcOk, bytesOf]
  rw [crcField_eq, ← recCrc_spec]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← UInt64.toNat_inj]
  exact eq_comm

/-- The decoder's result for the segment of `len` bytes that `seg` holds is the program's view of
the framing's result for it. -/
theorem view_decode (seg : Bytes40) (len : UInt64) :
    ViewOf (segKind (decodeWords seg len) len) (decodeWords seg len).olen
      (recCrc (decodeWords seg len).out == ((decodeWords seg len).out.w4 &&& 0xFFFFFFFF))
      (decodeRec (decodeWords seg len).out)
      (if UInt64.ofNat 36 < len then .error .overflow
        else segResult 36 (seg.bytes.drop (40 - min len.toNat 36))) := by
  have h36 : UInt64.ofNat 36 = 36 := rfl
  rw [h36]
  by_cases ho : 36 < len
  · left
    exact ⟨by rw [segKind, ite_eq_left ho], by rw [ite_eq_left ho]⟩
  · have hn : len.toNat ≤ 36 := by
      have := UInt64.lt_iff_toNat_lt.not.mp ho
      simp at this
      omega
    have hmin : min len.toNat 36 = len.toNat := by omega
    have hL : (seg.bytes.drop (40 - len.toNat)).length = len.toNat := by
      rw [List.length_drop, length_bytes]
      omega
    have hno : ¬36 < (seg.bytes.drop (40 - len.toNat)).length := by
      rw [hL]
      omega
    rw [ite_eq_right ho, hmin, segResult, ite_eq_right hno, decodeWords_eq seg (by omega)]
    have hol := decodeWords_olen seg (n := len) (by omega)
    generalize decodeWords seg len = d at hol ⊢
    by_cases hv : d.ok = 1 ∧ d.rem = 0 ∧ d.zero = 1
    · rw [ite_eq_left hv]
      have hk : segKind d len = 0 := by
        rw [segKind, ite_eq_right ho]
        simp [hv.1, hv.2.1, hv.2.2]
      right; right
      refine ⟨hk, _, rfl, ?_, fun h35 => ?_⟩
      · rw [List.length_drop, length_bytes]
        omega
      · have h5 : 40 - d.olen.toNat = 5 := by
          rw [List.length_drop, length_bytes] at h35
          omega
        rw [h5]
        exact ⟨decodeRec_spec d.out, crcOk_eq d.out⟩
    · rw [ite_eq_right hv]
      have hk : segKind d len = 1 := by
        rw [segKind, ite_eq_right ho]
        simp only [Bool.and_eq_true, beq_iff_eq]
        rw [ite_eq_right (fun h => hv ⟨h.1.1, h.1.2, h.2⟩)]
      right; left
      exact ⟨hk, rfl⟩


theorem permitOf_lt (w : UInt64) : (permitOf w).toNat < 2 ^ 8 := by
  unfold permitOf
  split_ifs <;> decide

/-- The program's answer bytes are the specification's answer. -/
theorem answer_eq {s : BmsState} (hs : StInv s) {kind olen : UInt64} {crcOk : Bool}
    {sc : ScanW} (hb : ScanBounds sc) {x : Input} (hv : ViewOf kind olen crcOk sc x) :
    (answerSrc s.answers (if kind == 0 && olen == 35 && crcOk then sc.seq else 0xFFFFFFFF)
        (permitOf (nextW s (failW s kind olen crcOk sc) sc).mode)
        (nextW s (failW s kind olen crcOk sc) sc).mode
        (nextW s (failW s kind olen crcOk sc) sc).diag).bytes.drop 23 =
      encodeAnswer (step (absS s) x).2 := by
  obtain ⟨hn, hni⟩ := nextW_spec hs hb hv
  have ha := answered_eq hv
  generalize nextW s (failW s kind olen crcOk sc) sc = n at hn hni
  have hal : (if kind == 0 && olen == 35 && crcOk then sc.seq else 0xFFFFFFFF).toNat < 2 ^ 32 := by
    split
    · exact hb.seq
    · decide
  have hst : n.mode.toNat < 2 ^ 8 := by have := hni.mode; omega
  rw [answerSrc_spec _ _ _ _ _ hs.answers hal hst hni.diag]
  have e : (step (absS s) x).2 = ⟨s.answers.toNat,
      (if kind == 0 && olen == 35 && crcOk then sc.seq else 0xFFFFFFFF).toNat,
      (permitOf n.mode).toNat, modeOf n.mode, n.diag.toNat⟩ := by
    rw [ha, permitOf_toNat]
    show Answer.mk _ _ (next (absS s) x).mode.permit (next (absS s) x).mode (next (absS s) x).diag =
      _
    rw [← hn]
    rfl
  rw [e, encodeAnswer, answerBody, modeOf_code hni.mode]
  rfl


/-- The framing's result for the segment that the step's state holds: an overflow above 36
bytes, and otherwise the result for the last `len` bytes of the segment's buffer. -/
def segInput (f : BmsFrame) : Input :=
  if UInt64.ofNat 36 < f.len then .error .overflow
  else segResult 36 (f.seg.bytes.drop (40 - min f.len.toNat 36))

/-- The window of a `0x00` after a non-empty segment: the machine's next state and its answer,
encoded and followed by `0x00`, ready to write. -/
theorem bmsDelim_spec (status : UInt64) (f : BmsFrame) (hs : StInv f.m) :
    ∃ out k m, bmsDelim status f = (⟨2, 0, f.seg, out, k, m⟩, readReq status) ∧
      absS m = (machine (absS f.m) (segInput f)).1 ∧ StInv m ∧
      out.bytes.take k.toNat = cobsEncode (machine (absS f.m) (segInput f)).2 ++ [0] ∧
      2 ≤ k.toNat ∧ k.toNat ≤ 40 := by
  have hv := view_decode f.seg f.len
  have hb := decodeRec_bounds (decodeWords f.seg f.len).out
  obtain ⟨hu, hui⟩ := updW_spec hs hb hv
  have ha := answer_eq hs hb hv
  have hr := encAll_spec (answerSrc f.m.answers
    (if segKind (decodeWords f.seg f.len) f.len == 0 && (decodeWords f.seg f.len).olen == 35 &&
        (recCrc (decodeWords f.seg f.len).out ==
          ((decodeWords f.seg f.len).out.w4 &&& 0xFFFFFFFF))
      then (decodeRec (decodeWords f.seg f.len).out).seq else 0xFFFFFFFF)
    (permitOf (nextW f.m (failW f.m (segKind (decodeWords f.seg f.len) f.len)
      (decodeWords f.seg f.len).olen (recCrc (decodeWords f.seg f.len).out ==
        ((decodeWords f.seg f.len).out.w4 &&& 0xFFFFFFFF)) (decodeRec (decodeWords f.seg f.len).out))
      (decodeRec (decodeWords f.seg f.len).out)).mode)
    (nextW f.m (failW f.m (segKind (decodeWords f.seg f.len) f.len)
      (decodeWords f.seg f.len).olen (recCrc (decodeWords f.seg f.len).out ==
        ((decodeWords f.seg f.len).out.w4 &&& 0xFFFFFFFF)) (decodeRec (decodeWords f.seg f.len).out))
      (decodeRec (decodeWords f.seg f.len).out)).mode
    (nextW f.m (failW f.m (segKind (decodeWords f.seg f.len) f.len)
      (decodeWords f.seg f.len).olen (recCrc (decodeWords f.seg f.len).out ==
        ((decodeWords f.seg f.len).out.w4 &&& 0xFFFFFFFF)) (decodeRec (decodeWords f.seg f.len).out))
      (decodeRec (decodeWords f.seg f.len).out)).diag) (n := 17) (by decide)
  rw [show 40 - (17 : UInt64).toNat = 23 from rfl, ha] at hr
  obtain ⟨h1, h2, h3⟩ := answer_rel hr (by simp [answerLength])
  exact ⟨_, _, _, rfl, hu, hui, h1, h2, h3⟩

/-! ## The step -/

/-- The framing's state over lists with the specification's machine state. -/
def bmsAbs (f : BmsFrame) : Delim State :=
  ⟨f.phase, f.len, f.seg.bytes.drop (40 - min f.len.toNat 36), f.out.bytes.take f.k.toNat,
    absS f.m⟩

/-- The states on which `bmsAbs` commutes with the step: at most 40 bytes to write, at least one in
the phases that write, and the machine's words in their ranges. -/
def BmsInv (f : BmsFrame) : Prop :=
  f.k.toNat ≤ 40 ∧ (f.phase ≠ 0 → f.phase ≠ 1 → 1 ≤ f.k.toNat) ∧ StInv f.m

theorem bmsInit_inv : BmsInv bmsInit :=
  ⟨by decide, fun h => absurd rfl h, ⟨by decide, by decide, Or.inl rfl, by decide, by decide,
    Or.inr rfl, by decide, by decide, by decide, by decide, Or.inr rfl⟩⟩

theorem bmsAbs_init : bmsAbs bmsInit = delim0 init := rfl

/-- `bmsPhases` computes `delimTick` of the specification's machine with segments of at most 36
bytes under `bmsAbs`, for every register map, on the states of `BmsInv`, and it keeps `BmsInv`. -/
theorem bmsPhases_abs (rx tx status rxFull txMask txRoom : UInt64) (f : BmsFrame) (v : UInt64)
    (hI : BmsInv f) :
    BmsInv (bmsPhases rx tx status rxFull txMask txRoom f v).1 ∧
      delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f) v =
        (bmsAbs (bmsPhases rx tx status rxFull txMask txRoom f v).1,
          (bmsPhases rx tx status rxFull txMask txRoom f v).2) := by
  obtain ⟨hk, hk1, hm⟩ := hI
  have h36 : UInt64.ofNat maxSegment = 36 := rfl
  by_cases p0 : (f.phase == 0) = true
  · have hd : (f.phase == 1 && v &&& 255 == 0 && f.len != 0) = false := by
      simp only [beq_iff_eq] at p0
      simp [p0]
    by_cases hx : (v &&& rxFull != 0) = true
    · have e1 : bmsPhases rx tx status rxFull txMask txRoom f v =
          ({ f with phase := 1 }, readReq rx) := by
        unfold bmsPhases bmsPoll
        rw [hd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_left p0, ite_eq_left hx]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f) v =
          ({ bmsAbs f with phase := 1 }, readReq rx) := by
        unfold delimTick bmsAbs
        dsimp only
        rw [ite_eq_left p0, ite_eq_left hx]
      rw [e1, e2]
      exact ⟨⟨hk, fun _ h => absurd rfl h, hm⟩, rfl⟩
    · have e1 : bmsPhases rx tx status rxFull txMask txRoom f v = (f, readReq status) := by
        unfold bmsPhases bmsPoll
        rw [hd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_left p0, ite_eq_right hx]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f) v =
          (bmsAbs f, readReq status) := by
        unfold delimTick bmsAbs
        dsimp only
        rw [ite_eq_left p0, ite_eq_right hx]
      rw [e1, e2]
      exact ⟨⟨hk, hk1, hm⟩, rfl⟩
  by_cases p1 : (f.phase == 1) = true
  · by_cases hb : (v &&& 255 != 0) = true
    · have hd : (f.phase == 1 && v &&& 255 == 0 && f.len != 0) = false := by
        simp only [bne_iff_ne, ne_eq] at hb
        simp [hb]
      have e1 : bmsPhases rx tx status rxFull txMask txRoom f v =
          ({ f with
              phase := 0,
              len := if f.len ≤ 36 then f.len + 1 else f.len,
              seg := if f.len < 36 then push40 f.seg v else f.seg }, readReq status) := by
        unfold bmsPhases bmsPoll
        rw [hd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_right p0, ite_eq_left p1, ite_eq_left hb]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f) v =
          ({ bmsAbs f with
              phase := 0,
              len := if f.len ≤ 36 then f.len + 1 else f.len,
              seg := if f.len < 36 then f.seg.bytes.drop (40 - min f.len.toNat 36) ++
                [(v &&& 255).toUInt8] else f.seg.bytes.drop (40 - min f.len.toNat 36) },
            readReq status) := by
        unfold delimTick bmsAbs
        dsimp only
        rw [ite_eq_right p0, ite_eq_left p1, ite_eq_left hb, h36]
      rw [e1, e2]
      refine ⟨⟨hk, fun h => absurd rfl h, hm⟩, ?_⟩
      simp only [bmsAbs, Prod.mk.injEq, Delim.mk.injEq, and_true, true_and]
      exact (seg_store f.seg f.len v).symm
    · have hb0 : (v &&& 255 == 0) = true := by simpa using hb
      by_cases hl : (f.len == 0) = true
      · have hd : (f.phase == 1 && v &&& 255 == 0 && f.len != 0) = false := by
          simp only [beq_iff_eq] at hl
          simp [hl]
        have e1 : bmsPhases rx tx status rxFull txMask txRoom f v =
            ({ f with phase := 0 }, readReq status) := by
          unfold bmsPhases bmsPoll
          rw [hd]
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [ite_eq_right p0, ite_eq_left p1, ite_eq_right hb]
        have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f)
            v = ({ bmsAbs f with phase := 0 }, readReq status) := by
          unfold delimTick bmsAbs
          dsimp only
          rw [ite_eq_right p0, ite_eq_left p1, ite_eq_right hb, ite_eq_left hl]
        rw [e1, e2]
        exact ⟨⟨hk, fun h => absurd rfl h, hm⟩, rfl⟩
      · have hd : (f.phase == 1 && v &&& 255 == 0 && f.len != 0) = true := by
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
          exact ⟨⟨p1, hb0⟩, by simpa using hl⟩
        obtain ⟨out, k, m, he, hu, hui, ho, h2, h40⟩ := bmsDelim_spec status f hm
        have e1 : bmsPhases rx tx status rxFull txMask txRoom f v =
            (⟨2, 0, f.seg, out, k, m⟩, readReq status) := by
          unfold bmsPhases
          rw [hd]
          exact he
        have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f)
            v = (⟨2, 0, [], cobsEncode (machine (absS f.m) (segInput f)).2 ++ [0],
              (machine (absS f.m) (segInput f)).1⟩, readReq status) := by
          unfold delimTick bmsAbs
          dsimp only
          rw [ite_eq_right p0, ite_eq_left p1, ite_eq_right hb, ite_eq_right hl]
          rfl
        rw [e1, e2]
        refine ⟨⟨h40, fun _ _ => Nat.le_trans (by decide) h2, hui⟩, ?_⟩
        simp only [bmsAbs, Prod.mk.injEq, Delim.mk.injEq, and_true, true_and]
        refine ⟨?_, ho.symm, hu.symm⟩
        rw [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_min, Nat.sub_zero, drop40]
  have p0' : f.phase ≠ 0 := by simpa using p0
  have p1' : f.phase ≠ 1 := by simpa using p1
  have hk1' := hk1 p0' p1'
  have hd : (f.phase == 1 && v &&& 255 == 0 && f.len != 0) = false := by
    simp [p1']
  by_cases p2 : (f.phase == 2) = true
  · by_cases hx : (v &&& txMask == txRoom) = true
    · have e1 : bmsPhases rx tx status rxFull txMask txRoom f v =
          ({ f with phase := 3 }, writeReq tx (first40 f.out)) := by
        unfold bmsPhases bmsPoll
        rw [hd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_right p0, ite_eq_right p1, ite_eq_left p2, ite_eq_left hx]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f) v =
          ({ bmsAbs f with phase := 3 },
            writeReq tx ((f.out.bytes.take f.k.toNat).headD 0).toUInt64) := by
        unfold delimTick bmsAbs
        dsimp only
        rw [ite_eq_right p0, ite_eq_right p1, ite_eq_left p2, ite_eq_left hx]
      rw [e1, e2, headD_take hk1', first40_val]
      exact ⟨⟨hk, fun _ _ => hk1', hm⟩, rfl⟩
    · have e1 : bmsPhases rx tx status rxFull txMask txRoom f v = (f, readReq status) := by
        unfold bmsPhases bmsPoll
        rw [hd]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_right p0, ite_eq_right p1, ite_eq_left p2, ite_eq_right hx]
      have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f) v =
          (bmsAbs f, readReq status) := by
        unfold delimTick bmsAbs
        dsimp only
        rw [ite_eq_right p0, ite_eq_right p1, ite_eq_left p2, ite_eq_right hx]
      rw [e1, e2]
      exact ⟨⟨hk, hk1, hm⟩, rfl⟩
  · have hkm : (f.k - 1).toNat = f.k.toNat - 1 := toNat_sub_one (by omega)
    have hlen : (f.out.bytes.take f.k.toNat).length = f.k.toNat := by
      rw [List.length_take, length_bytes]
      omega
    have hc : (f.k ≤ 1) ↔ ((f.out.bytes.take f.k.toNat).length ≤ 1) := by
      rw [hlen, UInt64.le_iff_toNat_le]
      rfl
    have e1 : bmsPhases rx tx status rxFull txMask txRoom f v =
        ({ f with phase := if f.k ≤ 1 then 0 else 2, out := push40 f.out 0, k := f.k - 1 },
          readReq status) := by
      unfold bmsPhases bmsPoll
      rw [hd]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ite_eq_right p0, ite_eq_right p1, ite_eq_right p2]
    have e2 : delimTick ⟨rx, tx, status, rxFull, txMask, txRoom⟩ maxSegment machine (bmsAbs f) v =
        ({ bmsAbs f with
            phase := if f.k ≤ 1 then 0 else 2, out := (f.out.bytes.take f.k.toNat).tail },
          readReq status) := by
      unfold delimTick bmsAbs
      dsimp only
      rw [ite_eq_right p0, ite_eq_right p1, ite_eq_right p2]
      by_cases h : f.k ≤ 1
      · rw [ite_eq_left (hc.mp h), ite_eq_left h]
      · rw [ite_eq_right (fun e => h (hc.mpr e)), ite_eq_right h]
    rw [e1, e2]
    refine ⟨⟨by rw [hkm]; omega, fun h _ => ?_, hm⟩, ?_⟩
    · show 1 ≤ (f.k - 1).toNat
      by_cases hk2 : f.k ≤ 1
      · rw [ite_eq_left hk2] at h
        exact absurd rfl h
      · rw [hkm]
        have := UInt64.le_iff_toNat_le.not.mp hk2
        simp at this
        omega
    · simp only [bmsAbs, Prod.mk.injEq, Delim.mk.injEq, and_true, true_and]
      rw [push40_bytes, hkm, show ((0 : UInt64).toUInt8) = 0 from rfl,
        tail_take_push (length_bytes _) hk1' hk]

/-- USART3's registers in `bmsTickUsart3`. -/
def bmsUsart3 : Uart := ⟨0x1209, 0x120A, 0x1207, 0x20, 0x80, 0x80⟩

/-- UART0's registers in `bmsTick`. -/
def bmsCmsdk : Uart := ⟨0x1000, 0x1000, 0x1001, 2, 1, 0⟩

theorem bmsUsart3_abs (f : BmsFrame) (v : UInt64) (h : BmsInv f) :
    BmsInv (bmsTickUsart3 f v).1 ∧
      delimTick bmsUsart3 maxSegment machine (bmsAbs f) v =
        (bmsAbs (bmsTickUsart3 f v).1, (bmsTickUsart3 f v).2) :=
  bmsPhases_abs 0x1209 0x120A 0x1207 0x20 0x80 0x80 f v h

theorem bmsTick_abs (f : BmsFrame) (v : UInt64) (h : BmsInv f) :
    BmsInv (bmsTick f v).1 ∧
      delimTick bmsCmsdk maxSegment machine (bmsAbs f) v =
        (bmsAbs (bmsTick f v).1, (bmsTick f v).2) :=
  bmsPhases_abs 0x1000 0x1000 0x1001 2 1 0 f v h

section

variable {α : Type} (B : Bus α) {u : Uart} {tick : BmsFrame → UInt64 → BmsFrame × UInt64}
  (htick : ∀ f v, BmsInv f → BmsInv (tick f v).1 ∧
    delimTick u maxSegment machine (bmsAbs f) v = (bmsAbs (tick f v).1, (tick f v).2))
  (hrx : u.rx.toNat < 65536) (htx : u.tx.toNat < 65536) (hs : u.status.toNat < 65536)
  (hrs : u.rx ≠ u.status) (σ : Nat → UInt32) (n : Nat)

include htick hrx htx hs hrs in
/-- F3 for a step that `bmsPhases_abs` covers: the bytes that the first `n` windows write begin
the encoded answers of the specification's machine to the non-empty segments of the bytes that
they read. -/
theorem bms_prefix :
    dataOut B u (windows (reqTrace B tick bmsInit σ) n) <+:
      (delimAnswers machine maxSegment init ((dataIn B u (windows (reqTrace B tick bmsInit σ)
        n)).map UInt64.toUInt8)).map UInt8.toUInt64 := by
  rw [← reqTrace_mapOn bmsAbs BmsInv htick bmsInit bmsInit_inv σ, bmsAbs_init]
  exact delim_prefix hrx htx hs hrs (by decide) σ n

include htick hrx htx hs hrs in
/-- F3 for a window that reads a byte, for a step that `bmsPhases_abs` covers. -/
theorem bms_answered (hread : dataIn B u (reqTrace B tick bmsInit σ n) ≠ []) :
    dataOut B u (windows (reqTrace B tick bmsInit σ) n) =
      (delimAnswers machine maxSegment init ((dataIn B u (windows (reqTrace B tick bmsInit σ)
        n)).map UInt64.toUInt8)).map UInt8.toUInt64 := by
  rw [← reqTrace_mapOn bmsAbs BmsInv htick bmsInit bmsInit_inv σ, bmsAbs_init] at hread ⊢
  exact delim_answered hrx htx hs hrs (by decide) σ n hread

end

theorem bms_usart3_prefix {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat) :
    dataOut B bmsUsart3 (windows (reqTrace B bmsTickUsart3 bmsInit σ) n) <+:
      (delimAnswers machine maxSegment init ((dataIn B bmsUsart3
        (windows (reqTrace B bmsTickUsart3 bmsInit σ) n)).map UInt64.toUInt8)).map
        UInt8.toUInt64 :=
  bms_prefix B bmsUsart3_abs (by decide) (by decide) (by decide) (by decide) σ n

theorem bms_usart3_answered {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat)
    (hread : dataIn B bmsUsart3 (reqTrace B bmsTickUsart3 bmsInit σ n) ≠ []) :
    dataOut B bmsUsart3 (windows (reqTrace B bmsTickUsart3 bmsInit σ) n) =
      (delimAnswers machine maxSegment init ((dataIn B bmsUsart3
        (windows (reqTrace B bmsTickUsart3 bmsInit σ) n)).map UInt64.toUInt8)).map
        UInt8.toUInt64 :=
  bms_answered B bmsUsart3_abs (by decide) (by decide) (by decide) (by decide) σ n hread

theorem bms_cmsdk_prefix {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat) :
    dataOut B bmsCmsdk (windows (reqTrace B bmsTick bmsInit σ) n) <+:
      (delimAnswers machine maxSegment init ((dataIn B bmsCmsdk
        (windows (reqTrace B bmsTick bmsInit σ) n)).map UInt64.toUInt8)).map UInt8.toUInt64 :=
  bms_prefix B bmsTick_abs (by decide) (by decide) (by decide) (by decide) σ n

theorem bms_cmsdk_answered {α : Type} (B : Bus α) (σ : Nat → UInt32) (n : Nat)
    (hread : dataIn B bmsCmsdk (reqTrace B bmsTick bmsInit σ n) ≠ []) :
    dataOut B bmsCmsdk (windows (reqTrace B bmsTick bmsInit σ) n) =
      (delimAnswers machine maxSegment init ((dataIn B bmsCmsdk
        (windows (reqTrace B bmsTick bmsInit σ) n)).map UInt64.toUInt8)).map UInt8.toUInt64 :=
  bms_answered B bmsTick_abs (by decide) (by decide) (by decide) (by decide) σ n hread

/-! ## The answers written -/

/-- The complete segments of a prefix begin the complete segments of the whole. -/
theorem segments_prefix {a b : List UInt8} (h : a <+: b) : segments a <+: segments b := by
  obtain ⟨c, rfl⟩ := h
  have e : split (a ++ c) = c.foldl splitByte ⟨(split a).done, (split a).cur⟩ := by
    show List.foldl splitByte ⟨[], []⟩ (a ++ c) = _
    rw [List.foldl_append]
    rfl
  unfold segments
  rw [e, foldl_splitByte]
  exact ⟨_, rfl⟩

theorem getElem?_of_prefix {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂) {n : Nat} {x : α}
    (hx : l₁[n]? = some x) : l₂[n]? = some x := by
  obtain ⟨t, rfl⟩ := h
  have hn : n < l₁.length := by
    rcases Nat.lt_or_ge n l₁.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx
      exact absurd hx (by simp)
  rw [List.getElem?_append_left hn, hx]

/-- The bytes written as bytes, when they begin the bytes of the answers as words. -/
theorem prefix_toUInt8 {out : List UInt64} {A : List UInt8}
    (h : out <+: A.map UInt8.toUInt64) : out.map UInt64.toUInt8 <+: A := by
  have := h.map UInt64.toUInt8
  rwa [List.map_map, show UInt64.toUInt8 ∘ UInt8.toUInt64 = id from funext fun b => by
    apply UInt8.toNat_inj.mp
    simp [UInt64.toNat_toUInt8, UInt8.toNat_toUInt64], List.map_id] at this

/-- M1 over a prefix of the answers to the bytes `bs`: an answer among the complete segments of
`out` with a nonzero permit byte is the answer `a_n` of the run over the non-empty segments of
`bs`, and M1 holds of it. -/
theorem m1_prefix {bs out : List UInt8} (hp : out <+: delimAnswers machine maxSegment init bs)
    (n : Nat) (s raw : List UInt8) (hs : (segments out)[n]? = some s)
    (hd : cobsDecode s = some raw) (hpm : field raw 9 1 ≠ 0) :
    n < (records bs).length ∧ raw = encodeAnswer (answerAt (inputs bs) n) ∧
      ∃ i j, Permitted (inputs bs) n i j :=
  m1_stream bs n s raw (getElem?_of_prefix (segments_prefix hp) hs) hd hpm

end Demos.Bms.Program
