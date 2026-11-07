import LeanExe.M7.Isla.Check
import LeanExe.M7.Isla.Profile

/-!
Theorems of `Agrees` for the immediate and move forms of `LeanExe/M7/Machine.lean`: `AND.W` and
`EOR.W` with an immediate, `MOV.W` with an immediate, `MOVW`, and `MOVT`, from the traces of
`tests/isla/m7` under the profile `sys` of `LeanExe/M7/Isla/Profile.lean`.  Each theorem holds
for every register of r0 to r7 in each register field, every value of the immediate fields, every
machine whose program counter plus 4 is below 2^32, every platform, and every sequence of device
values.  The model's immediates of `AND.W`, `EOR.W`, and `MOV.W` have `i:imm3` 0000, and the
traces fix those bits, so `T32ExpandImm` gives the 8-bit field.  `tests/isla/m7-theorems.sh`
elaborates the module and prints the axioms of its theorems.

The proofs follow those of `tests/TestSupport/M7/Isla/Register.lean`: the forward direction takes
each path of the trace to its outcome, and the backward direction builds the path that keeps bits
63 to 32 of the written register.  A lemma per form states the trace's value on the low word of
the registers as the model's value.  `MOVT` keeps bits 15 to 0 of its register, so the value that
it writes is the bitwise OR of a masked word and the shifted immediate, whose bound `imm_lt`
proves.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode)

/-- The footprint of `AND.W Rd, Rn, #imm8`. -/
def andImmT : Footprint := isla_trace% "tests/isla/m7/and-imm"

/-- The footprint of `EOR.W Rd, Rn, #imm8`. -/
def eorImmT : Footprint := isla_trace% "tests/isla/m7/eor-imm"

/-- The footprint of `MOV.W Rd, #imm8`. -/
def movImmT : Footprint := isla_trace% "tests/isla/m7/mov-imm"

/-- The footprint of `MOVW Rd, #imm16`. -/
def movwT : Footprint := isla_trace% "tests/isla/m7/movw"

/-- The footprint of `MOVT Rd, #imm16`. -/
def movtT : Footprint := isla_trace% "tests/isla/m7/movt"

/-- The fields of a form of the registers `d` and `n` with the immediate `imm`. -/
def immFields (d n : Fin 8) (imm : Fin 256) : Fields :=
  [("Rn", n.val), ("Rd", d.val), ("imm8", imm.val)]

/-- The fields of `MOV.W` for the register `d` and the immediate `imm`. -/
def movFields (d : Fin 8) (imm : Fin 256) : Fields := [("Rd", d.val), ("imm8", imm.val)]

/-- The fields of `MOVW` and `MOVT` for the register `d` and the immediate `imm4:i:imm3:imm8`. -/
def wideFields (d : Fin 8) (imm4 : Fin 16) (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256) :
    Fields :=
  [("i", i.val), ("imm4", imm4.val), ("imm3", imm3.val), ("Rd", d.val), ("imm8", imm8.val)]

/-! The trace's values as the model's. -/

theorem ofNat_andImm (a : UInt32) {k : Nat} (hk : k < 4294967296) :
    UInt32.ofNat (a.toNat &&& k) = a &&& UInt32.ofNat k := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_and, Nat.reducePow, Nat.mod_eq_of_lt hk]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hk)

theorem ofNat_xorImm (a : UInt32) {k : Nat} (hk : k < 4294967296) :
    UInt32.ofNat (a.toNat ^^^ k) = a ^^^ UInt32.ofNat k := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_xor, Nat.reducePow, Nat.mod_eq_of_lt hk]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 32) a.toNat_lt hk)

/-- The immediate of `MOVW` and `MOVT` as the trace's concatenation of the fields gives it. -/
theorem imm16_eq (imm4 : Fin 16) (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256) :
    imm16 imm4 i imm3 imm8 =
      UInt32.ofNat (((imm4.val * 2 + i.val) * 8 + imm3.val) * 256 + imm8.val) := by
  unfold imm16
  exact congrArg UInt32.ofNat (by omega)

/-- Bits 15 to 0 of `a` and the 16-bit `n` above them. -/
theorem lo_or_hi (a n : Nat) :
    (a &&& 65535) ||| n * 65536 = a % 65536 + n * 65536 := by
  rw [show (65535 : Nat) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.or_comm,
    show (65536 : Nat) = 2 ^ 16 from rfl, Nat.mul_comm n,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by decide)) n]
  omega

/-- The value that `MOVT` writes, as the trace computes it on the low word of the register. -/
theorem ofNat_movt (a : UInt32) {n : Nat} (hn : n < 65536) :
    UInt32.ofNat ((a.toNat &&& 65535) ||| n * 65536 % 4294967296) =
      a &&& (0xFFFF : UInt32) ||| UInt32.ofNat n <<< (16 : UInt32) := by
  apply UInt32.toNat_inj.mp
  have ha := a.toNat_lt
  rw [UInt32.toNat_or, UInt32.toNat_and, UInt32.toNat_shiftLeft, UInt32.toNat_ofNat',
    UInt32.toNat_ofNat', show (0xFFFF : UInt32).toNat = 65535 from rfl,
    show (16 : UInt32).toNat = 16 from rfl, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show n * 65536 < 4294967296 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), lo_or_hi]
  simp only [Nat.reducePow, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show n * 65536 < 4294967296 by omega), lo_or_hi]
  omega

/-! The end of a path. -/

/-- Proves that a value that a trace writes to the low word of a register is below 2^32: a value
of `t32_lt`, or the bitwise OR of a masked value and a remainder modulo 2^32.  The last
alternative fails, so that `first` runs the others without error recovery: inside a discharger of
`simp`, `all_goals` of `<;>` with recovery would log the error of a failed bound. -/
macro "imm_lt" : tactic => `(tactic| first
  | t32_lt
  | (apply lt32_or <;> first | omega | (apply lt32_and; omega))
  | fail "imm_lt: no bound")

/-- `t32_reg_end` with `imm_lt` for the bound of the written value, for a form whose written value
may already be the model's, as that of `MOV.W` is. -/
syntax "imm_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| imm_end [$xs,*]) => `(tactic| (
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    t32_pc
    simp only [Outcome.done.injEq, and_true, true_and]
    simp (disch := first | omega | imm_lt) only [setX_low, setX_keep]
    apply exists_mach
    · simp only [setLow_r]
      apply state_eq
      simp -failIfUnchanged (disch := omega) only [x_mod, low_r, $xs,*]
      try rfl
    · rfl
    · rfl))

/-- Two machines that differ only in their model states are equal when the states are. -/
theorem mach_with_s {m : Mach} {a b : State} (h : a = b) :
    ({ m with s := a } : Mach) = { m with s := b } := by
  rw [h]

/-- `t32_reg_bwd` with `imm_lt` for the bound of the written value, comparing the model states with
`mach_with_s` and `state_eq`. -/
syntax "imm_bwd " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| imm_bwd [$xs,*]) => `(tactic| (
    simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
    t32_pc
    simp only [Outcome.done.injEq, and_true, true_and]
    simp (disch := first | omega | imm_lt) only [setX_keep]
    simp only [setLow_r]
    apply mach_with_s
    apply Eq.symm
    apply state_eq
    simp -failIfUnchanged (disch := omega) only [x_mod, low_r, $xs,*]
    try rfl))

/-- Proves the paths of `Agrees` for the footprint `F` with the fields `fs` of a form that writes
one register of r0 to r7 and leaves the flags: the premise on `σ`, every path of the trace by
`t32_fwd` and `imm_end`, and the path that keeps the high words with the values `vs` before the
reads of `R0` to `R30`, `t32_gprs` of the machine `m`, and the values `ws` after them, among which
`false` chooses the write that keeps bits 63 to 32.  `k` is the number of the decode clause, which
the trace writes to `SEE`, and the lemmas in brackets turn the written value into the model's. -/
syntax "imm_paths " ident ident num term:max "[" term,* "]" "[" term,* "]"
  "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| imm_paths $F $fs $k $m [$vs,*] [$ws,*] [$xs,*]) => `(tactic| (
    intro σ hσ s' hs
    simp only [exec, Option.some.injEq] at hs
    subst hs
    t32_reads [$F:ident, sys_get, sys] at hσ
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
      (.bits 128 $k), fun o h => ?_, ?_, by t32_frame⟩
    · unfold footRun at h
      simp only [$F:ident, LeanExe.A64.Isla.Footprint.vars, $fs:ident, List.foldl, List.lookup,
        String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
        Nat.reduceDiv] at h
      t32_fwd h using omega with [hσ]
      all_goals imm_end [$xs,*]
    · unfold footRun
      simp only [$F:ident, LeanExe.A64.Isla.Footprint.vars, $fs:ident, List.foldl, List.lookup,
        String.reduceBEq, Option.getD, LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd,
        Nat.reduceDiv]
      t32_bwd [$vs,*] using omega with [hσ]
      t32_gprs $m using omega with [hσ]
      t32_bwd [$ws,*] using omega with [hσ]
      all_goals first
        | imm_bwd [$xs,*]
        | t32_side))

/-- Proves `Agrees` for the footprint `F` with the fields `fs`: the decode from the opcode's word,
and the paths by `imm_paths`. -/
syntax "imm_agrees " ident ident num term:max "[" term,* "]" "[" term,* "]"
  "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| imm_agrees $F $fs $k $m [$vs,*] [$ws,*] [$xs,*]) => `(tactic| without_info
    refine ⟨by decide, by decide, ?_, ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, $F:ident, $fs:ident, encodeNat,
        List.lookup, String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · imm_paths $F $fs $k $m [$vs,*] [$ws,*] [$xs,*])

/-! The opcode of `MOV.W`.  The tactic proof of its decode, as `imm_agrees` writes it, elaborates,
but the kernel's check of it overflows its stack, so the decode follows from the opcode's word as a
term. -/

theorem movImmT_opcode :
    movImmT.opcode = [.bits 21 0b111100000100111100000, .field "Rd" 3, .field "imm8" 8] := rfl

theorem movImm_word (d : Fin 8) (imm : Fin 256) :
    Opcode.word movImmT.opcode (movFields d imm) = 61519 * 65536 + (d.val * 256 + imm.val) := by
  rw [movImmT_opcode]
  simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, movFields, List.lookup,
    String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
  omega

theorem movImm_width : movImmT.opcode.width = 32 := by decide

theorem movImm_decode (d : Fin 8) (imm : Fin 256) :
    decode (halves movImmT.opcode (movFields d imm)) =
      some (.movImm d imm, movImmT.opcode.width / 16) :=
  decode_halves movImm_width (by intro h; cases h) (movImm_word d imm)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `AND.W Rd, Rn, #imm8` agrees with `exec` for every register of r0 to r7 in each
field, every immediate, and every machine whose program counter plus 4 is below 2^32. -/
theorem andImm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n : Fin 8)
    (imm : Fin 256) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] andImmT (immFields d n imm)
      (.andImm d n imm) m := by
  imm_agrees andImmT immFields 2844 m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat]
    [false] [ofNat_andImm]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `EOR.W Rd, Rn, #imm8` agrees with `exec` for every register of r0 to r7 in each
field, every immediate, and every machine whose program counter plus 4 is below 2^32. -/
theorem eorImm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d n : Fin 8)
    (imm : Fin 256) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] eorImmT (immFields d n imm)
      (.eorImm d n imm) m := by
  imm_agrees eorImmT immFields 2904 m [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat]
    [false] [ofNat_xorImm]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `MOV.W Rd, #imm8` agrees with `exec` for every register of r0 to r7, every
immediate, and every machine whose program counter plus 4 is below 2^32. -/
theorem movImm_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d : Fin 8)
    (imm : Fin 256) (m : Mach) (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] movImmT (movFields d imm)
      (.movImm d imm) m := by
  without_info
    refine ⟨by decide, by decide, movImm_decode d imm, ?_⟩
    imm_paths movImmT movFields 3012 m
      [u.feature, if m.s.cFlag then 1 else 0, m.s.pc.toNat, false] [] []

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `MOVW Rd, #imm16` agrees with `exec` for every register of r0 to r7, every value
of the immediate's fields, and every machine whose program counter plus 4 is below 2^32. -/
theorem movw_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d : Fin 8) (imm4 : Fin 16)
    (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256) (m : Mach)
    (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] movwT
      (wideFields d imm4 i imm3 imm8) (.movw d imm4 i imm3 imm8) m := by
  imm_agrees movwT wideFields 3013 m [u.feature, m.s.pc.toNat, false] [] [imm16_eq]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `MOVT Rd, #imm16` agrees with `exec` for every register of r0 to r7, every value
of the immediate's fields, and every machine whose program counter plus 4 is below 2^32. -/
theorem movt_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (d : Fin 8) (imm4 : Fin 16)
    (i : Fin 2) (imm3 : Fin 8) (imm8 : Fin 256) (m : Mach)
    (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] movtT
      (wideFields d imm4 i imm3 imm8) (.movt d imm4 i imm3 imm8) m := by
  imm_agrees movtT wideFields 3022 m [u.feature, m.s.pc.toNat] [false] [ofNat_movt, imm16_eq]

#print axioms andImm_agrees
#print axioms eorImm_agrees
#print axioms movImm_agrees
#print axioms movw_agrees
#print axioms movt_agrees

end TestSupport.M7.Isla
