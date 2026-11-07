import LeanExe.A64.Isla.Check
import LeanExe.A64.Isla.Profile

/-!
Theorems of `Agrees` for the immediate and move forms of `LeanExe/A64/Machine.lean`: `ADD`,
`SUB`, and `SUBS` with an immediate, `MOVZ`, `MOVK`, `LSR` with an immediate, `CSINC`, `ADR`, and
`ADRP`.  They come from the traces of `tests/isla/tcg` and `tests/isla/kvm` under the profiles
`tcg` and `kvm` with the arguments `tcr`, and each holds for every value of every field of its
opcode, register 31 included, and for every state.  The two traces of each form are equal, so the
theorem under `kvm` follows from the theorem under `tcg` as in `Register.lean`, and
`tests/isla/theorems.sh` elaborates the module and prints the axioms of its theorems.

Each proof follows `addReg_tcg`: `isla_fwd` takes every path of the trace to its outcome, and the
backward direction builds one path for each case of register 31 among the register fields.
Register 31 is `SP_EL1` as `Rn` of `ADD`, `SUB`, and `SUBS` and as `Rd` of `ADD` and `SUB`, where
the traces read `PSTATE.SP` and `PSTATE.EL` and access `SP_EL1` as a register of the model, and
the zero register elsewhere.  `MOVZ` and `MOVK` shift the immediate by `concat hw #x0`, so
their proofs take the four values of `hw` in turn, which leaves numbers for the shifts and masks.

The trace of `LSR` computes `UBFM` with the shift as `immr` and 63 as `imms`, through a rotation,
masks, and remainders of 128-bit integers, and forks on `immr = 0`.  Its proof decides the
remainders, the conditions of `ite`, and the comparisons with `omega` as it walks the trace, and
`lsr_bits` reduces the rotated and masked value to the shift.  The condition of `CSINC` evaluates
to a Boolean formula in the field `cond` and the flags, which `cond_fwd` and `cond_bwd` tie to
`State.condHolds`: they abstract the field and the flags, and the kernel decides the formula for
every condition and every value of the flags.  The backward direction of `CSINC` evaluates both
branches of the trace's fork on the condition and takes the one that `condHolds` selects.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/-- The footprint of `ADD Xd|SP, Xn|SP, #imm` under the profile `tcg`. -/
def addImmTcg : Footprint := isla_trace% "tests/isla/tcg/add-imm"

/-- The footprint of `ADD Xd|SP, Xn|SP, #imm` under the profile `kvm`. -/
def addImmKvm : Footprint := isla_trace% "tests/isla/kvm/add-imm"

/-- The footprint of `SUB Xd|SP, Xn|SP, #imm` under the profile `tcg`. -/
def subImmTcg : Footprint := isla_trace% "tests/isla/tcg/sub-imm"

/-- The footprint of `SUB Xd|SP, Xn|SP, #imm` under the profile `kvm`. -/
def subImmKvm : Footprint := isla_trace% "tests/isla/kvm/sub-imm"

/-- The footprint of `SUBS Xd, Xn|SP, #imm` under the profile `tcg`. -/
def subsImmTcg : Footprint := isla_trace% "tests/isla/tcg/subs-imm"

/-- The footprint of `SUBS Xd, Xn|SP, #imm` under the profile `kvm`. -/
def subsImmKvm : Footprint := isla_trace% "tests/isla/kvm/subs-imm"

/-- The footprint of `MOVZ Xd, #imm, LSL #(16 * hw)` under the profile `tcg`. -/
def movzTcg : Footprint := isla_trace% "tests/isla/tcg/movz"

/-- The footprint of `MOVZ Xd, #imm, LSL #(16 * hw)` under the profile `kvm`. -/
def movzKvm : Footprint := isla_trace% "tests/isla/kvm/movz"

/-- The footprint of `MOVK Xd, #imm, LSL #(16 * hw)` under the profile `tcg`. -/
def movkTcg : Footprint := isla_trace% "tests/isla/tcg/movk"

/-- The footprint of `MOVK Xd, #imm, LSL #(16 * hw)` under the profile `kvm`. -/
def movkKvm : Footprint := isla_trace% "tests/isla/kvm/movk"

/-- The footprint of `LSR Xd, Xn, #sh` under the profile `tcg`. -/
def lsrImmTcg : Footprint := isla_trace% "tests/isla/tcg/lsr-imm"

/-- The footprint of `LSR Xd, Xn, #sh` under the profile `kvm`. -/
def lsrImmKvm : Footprint := isla_trace% "tests/isla/kvm/lsr-imm"

/-- The footprint of `CSINC Xd, Xn, Xm, cond` under the profile `tcg`. -/
def csincTcg : Footprint := isla_trace% "tests/isla/tcg/csinc"

/-- The footprint of `CSINC Xd, Xn, Xm, cond` under the profile `kvm`. -/
def csincKvm : Footprint := isla_trace% "tests/isla/kvm/csinc"

/-- The footprint of `ADR Xd` under the profile `tcg`. -/
def adrTcg : Footprint := isla_trace% "tests/isla/tcg/adr"

/-- The footprint of `ADR Xd` under the profile `kvm`. -/
def adrKvm : Footprint := isla_trace% "tests/isla/kvm/adr"

/-- The footprint of `ADRP Xd` under the profile `tcg`. -/
def adrpTcg : Footprint := isla_trace% "tests/isla/tcg/adrp"

/-- The footprint of `ADRP Xd` under the profile `kvm`. -/
def adrpKvm : Footprint := isla_trace% "tests/isla/kvm/adrp"

/-- The fields of `ADD`, `SUB`, and `SUBS` with an immediate for the registers `d` and `n` and the
immediate `imm`. -/
def arithFields (d n : Fin 32) (imm : Fin 4096) : Fields :=
  [("imm12", imm.val), ("Rn", n.val), ("Rd", d.val)]

/-- The fields of `MOVZ` and `MOVK` for the register `d`, the immediate `imm`, and the shift
`16 * hw`. -/
def moveFields (d : Fin 32) (imm : Fin 65536) (hw : Fin 4) : Fields :=
  [("hw", hw.val), ("imm16", imm.val), ("Rd", d.val)]

/-- The fields of `LSR` with an immediate for the registers `d` and `n` and the shift `sh`, which
the field `immr` holds. -/
def lsrImmFields (d n : Fin 32) (sh : Fin 64) : Fields :=
  [("immr", sh.val), ("Rn", n.val), ("Rd", d.val)]

/-- The fields of `CSINC` for the registers `d`, `n`, and `m` and the condition `cond`. -/
def csincFields (d n m : Fin 32) (cond : Fin 16) : Fields :=
  [("Rm", m.val), ("cond", cond.val), ("Rn", n.val), ("Rd", d.val)]

/-- The fields of `ADR` and `ADRP` for the register `d` and the immediate's fields `immlo`, `lo`,
and `immhi`, `hi`. -/
def adrFields (d : Fin 32) (lo : Fin 4) (hi : Fin 524288) : Fields :=
  [("immlo", lo.val), ("immhi", hi.val), ("Rd", d.val)]

/-- The model's read of a register below 31, where register 31 is the stack pointer, as the
vector primitive reads it. -/
theorem xsp_lt {s : State} {n : Fin 32} (h : n.val < 31) : s.xsp n = regAt s n.val := by
  unfold State.xsp regAt
  rw [dite_eq_left h, dite_eq_left h]

/-- The model's read of register 31 as the stack pointer. -/
theorem xsp_31 {s : State} {n : Fin 32} (h : n.val = 31) : s.xsp n = s.sp := by
  unfold State.xsp
  rw [dite_eq_right (by omega)]

/-- The model's write of a register below 31, where register 31 is the stack pointer, as the
vector primitive writes it. -/
theorem setXsp_lt {s : State} {d : Fin 32} (h : d.val < 31) (v : UInt64) :
    s.setXsp d v = setRegAt s d.val v := by
  unfold State.setXsp setRegAt
  rw [ite_eq_left h, ite_eq_left h]

/-- The model's write of register 31 as the stack pointer. -/
theorem setXsp_31 {s : State} {d : Fin 32} (h : d.val = 31) (v : UInt64) :
    s.setXsp d v = { s with sp := v } := by
  unfold State.setXsp
  rw [ite_eq_right (by omega)]

/-- The flag `N`, `Z`, `C`, or `V` as the bit that the trace of `CSINC` reads is below 2. -/
theorem bit_lt (b : Bool) : (if b = true then 1 else 0) < 2 := by
  cases b <;> decide

/-- `bvand immr #b111111`, which the trace of `LSR` computes, is `immr`. -/
theorem and63 (r : Fin 64) : r.val &&& 63 = r.val := by
  have h := Nat.and_two_pow_sub_one_eq_mod r.val 6
  simp only [Nat.reducePow, Nat.reduceSub] at h
  rw [h]
  exact Nat.mod_eq_of_lt r.isLt

/-- `bvsub` of 64-bit numbers without a borrow is the difference. -/
theorem sub64 {a b : Nat} (h : b ≤ a) (ha : a < 18446744073709551616) :
    (a + (18446744073709551616 - b)) % 18446744073709551616 = a - b := by omega

/-- `bvsrem` of a 128-bit number below 64 by 64, which the trace of `LSR` computes for the
rotation, is the number. -/
theorem srem64 {r : Nat} (h : r < 64) : srem 128 r 64 = r := by
  unfold srem urem neg
  (repeat' split) <;> omega

/-- The AND with 64 ones is the remainder modulo `2 ^ 64`. -/
theorem and_ones (x : Nat) : x &&& 18446744073709551615 = x % 18446744073709551616 := by
  have h := Nat.and_two_pow_sub_one_eq_mod x 64
  simp only [Nat.reducePow, Nat.reduceSub] at h
  exact h

/-- `UBFM` with a shift `r` from 1 to 63 as `immr` and 63 as `imms`: the rotation of `x` right by
`r`, masked by the rotation of the ones and by the low `64 - r` bits, is `x` shifted right by
`r`. -/
theorem lsr_bits {x r : Nat} (hx : x < 2 ^ 64) (h0 : 0 < r) (hr : r < 64) :
    (x / 2 ^ r ||| x * 2 ^ (64 - r) % 2 ^ 64) &&&
        ((2 ^ 64 - 1) / 2 ^ r ||| (2 ^ 64 - 1) * 2 ^ (64 - r) % 2 ^ 64) &&&
      (2 ^ 64 - 1) / 2 ^ r = x / 2 ^ r := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h : i + r < 64
  · have h1 : ¬ 64 - r ≤ i := by omega
    simp [h, h1]
  · have hb : x.testBit (i + r) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h, hb]

/-- The value that the trace of `LSR` writes for a shift `r` from 1 to 63 is the model's shift,
where `k`, the shift of the last mask, is `r`. -/
theorem lsr_pos {x : UInt64} {r k : Nat} (h0 : 0 < r) (hr : r < 64) (hk : k = r) :
    UInt64.ofNat ((x.toNat / 2 ^ r ||| x.toNat * 2 ^ (64 - r) % 18446744073709551616) &&&
        (18446744073709551615 / 2 ^ r ||| 18446744073709551615 * 2 ^ (64 - r) %
          18446744073709551616) &&&
      18446744073709551615 / 2 ^ k) = x >>> UInt64.ofNat r := by
  subst k
  have h := lsr_bits (toNat_lt x) h0 hr
  simp only [Nat.reducePow, Nat.reduceSub] at h
  rw [h]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_ofNat', UInt64.toNat_shiftRight, UInt64.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : r < 2 ^ 64), Nat.mod_eq_of_lt (by omega : r < 64)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (toNat_lt x))

/-- The value that the trace of `LSR` writes for a shift of 0 is the model's shift, where `k`, the
shift of the last mask, is 0. -/
theorem lsr_zero {x : UInt64} {r k : Nat} (hr : r = 0) (hk : k = 0) :
    UInt64.ofNat (x.toNat &&& 18446744073709551615 &&& 18446744073709551615 / 2 ^ k) =
      x >>> UInt64.ofNat r := by
  subst hr hk
  apply UInt64.toNat_inj.mp
  simp only [Nat.pow_zero, Nat.div_one, and_ones, UInt64.toNat_ofNat', UInt64.toNat_shiftRight,
    toNat_mod, Nat.reducePow, Nat.zero_mod, Nat.shiftRight_zero]

/-- `lsr_zero` with the last mask evaluated, as the backward direction leaves it once the shift
is known to be 0. -/
theorem lsr_ones {x : UInt64} {r : Nat} (hr : r = 0) :
    UInt64.ofNat (x.toNat &&& 18446744073709551615 &&& 18446744073709551615) =
      x >>> UInt64.ofNat r := by
  subst hr
  apply UInt64.toNat_inj.mp
  simp only [and_ones, UInt64.toNat_ofNat', UInt64.toNat_shiftRight, toNat_mod, Nat.reducePow,
    Nat.zero_mod, Nat.shiftRight_zero]

/-- The model's shift of the zero register is the 0 that the trace of `LSR` writes for register
31. -/
theorem zero_shr (a : UInt64) : (0 : UInt64) >>> a = UInt64.ofNat 0 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_zero, Nat.zero_shiftRight, UInt64.toNat_ofNat',
    Nat.zero_mod]

/-- The value of `MOVK`, a register with a field cleared and the shifted immediate ORed in, is
below `2 ^ 64`. -/
theorem or_and_mod {x y z : Nat} (hx : x < 18446744073709551616) (hz : z < 18446744073709551616) :
    (x &&& y ||| z) % 18446744073709551616 = x &&& y ||| z :=
  Nat.mod_eq_of_lt (Nat.or_lt_two_pow (n := 64) (Nat.lt_of_le_of_lt Nat.and_le_left hx) hz)

/-- The model's `sext 21 v` is `(_ sign_extend 43)` of the 21-bit `v`, as the traces of `ADR` and
`ADRP` compute it. -/
theorem sext21 {v : Nat} (h : v < 2097152) :
    (sext 21 v).toNat = v + v / 1048576 * 18446744073707454464 := by
  unfold sext
  simp only [Nat.reduceSub, Nat.reducePow]
  split
  · rw [UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  · rw [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega

/-- The mask `0xfffffffffffff000` of the trace of `ADRP` clears the low 12 bits, as the model's
`pc - pc % 4096` does. -/
theorem and_page {a : Nat} (h : a < 18446744073709551616) :
    a &&& 18446744073709547520 = a - a % 4096 := by
  have e1 : (18446744073709547520 : Nat) = (2 ^ 52 - 1) * 2 ^ 12 := by decide
  have e2 : a - a % 4096 = a / 2 ^ 12 * 2 ^ 12 := by
    rw [show (2 : Nat) ^ 12 = 4096 from rfl]
    omega
  rw [e1, e2]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h1 : 12 ≤ i
  · have e3 : i - 12 + 12 = i := by omega
    by_cases h2 : i < 64
    · simp [h1, e3, show i - 12 < 52 by omega]
    · have hb : a.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h
          (show (18446744073709551616 : Nat) ≤ 2 ^ i from
            Nat.pow_le_pow_right (n := 2) (i := 64) (by decide) (by omega)))
      simp [h1, e3, hb, show ¬ i - 12 < 52 by omega]
  · simp [h1]

/-- Proves that the outcome at the end of a path of the trace of an immediate form is `exec`'s, as
`gpr_end` does, with the reads and writes of register 31 as the stack pointer and with the lemmas
in brackets for the written value. -/
syntax "imm_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| imm_end [$xs,*]) => `(tactic| (
      simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
        true_and]
      simp (disch := omega) only [x_lt, x_31, xsp_lt, xsp_31, setX_eq_setRegAt, setXsp_lt,
        setXsp_31, setRegAt_lt, setRegAt_31, State.mk.injEq, and_true, true_and]
      try (funext j; split <;> (try with_reducible rfl))
      try (apply UInt64.toNat_inj.mp
           simp (disch := omega) only [UInt64.toNat_ofNat', UInt64.toNat_zero, UInt64.reduceToNat,
             toNat_mod, Nat.zero_add, Nat.add_zero, Nat.reducePow, Nat.mod_mod, $xs,*]
           try omega)))

/-- Proves `State.condHolds s c = b` from the hypothesis that the trace of `CSINC` asserts its
condition to be `b`: it abstracts the flag `N` of `s` in every hypothesis and the goal, reverts
the hypotheses that mention it, among them the condition, abstracts the other flags and the field
`c` in the goal, and the kernel decides the statement for every condition and every value of the
flags. -/
syntax "cond_fwd " term:max term:max : tactic
macro_rules
  | `(tactic| cond_fwd $s $c) => `(tactic| (
      unfold State.condHolds
      generalize State.nFlag $s = a at *
      revert a
      generalize State.zFlag $s = b
      generalize State.cFlag $s = e
      generalize State.vFlag $s = f
      revert b e f
      have hlt := Fin.isLt $c
      revert hlt
      generalize Fin.val $c = k
      revert k
      decide +kernel))

/-- Proves that the condition of the trace of `CSINC` has the value that `State.condHolds s c`
has by the hypothesis `h`: it reverts `h`, abstracts the flags of `s` and the field `c`, and the
kernel decides the statement for every condition and every value of the flags. -/
syntax "cond_bwd " ident term:max term:max : tactic
macro_rules
  | `(tactic| cond_bwd $h $s $c) => `(tactic| (
      revert $h:ident
      unfold State.condHolds
      generalize State.nFlag $s = a
      generalize State.zFlag $s = b
      generalize State.cFlag $s = e
      generalize State.vFlag $s = f
      revert a b e f
      have hlt := Fin.isLt $c
      revert hlt
      generalize Fin.val $c = k
      revert k
      decide +kernel))

set_option maxHeartbeats 4000000 in
/-- The trace of `ADD Xd|SP, Xn|SP, #imm` under `tcg` agrees with `exec` for every register number,
with register 31 the stack pointer, every immediate, and every state.  The backward direction
builds the path of each of the 4 cases of register 31 among `d` and `n`, and the events that the
two directions evaluate take more than the default budget of heartbeats. -/
theorem addImm_tcg (P : Platform) (u : Unknown) (d n : Fin 32) (imm : Fin 4096) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] addImmTcg (arithFields d n imm)
      (.addImm d n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : addImmTcg.opcode.word (arithFields d n imm) = encodeNat (.addImm d n imm) := by
      simp only [Opcode.word, Opcode.wordFrom, addImmTcg, arithFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [addImmTcg, Profile.sys_get, Profile.sys] at hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 18),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [addImmTcg, Footprint.vars, arithFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      isla_fwd h using omega with [hσ]
      all_goals imm_end [UInt64.toNat_add]
    · subst h
      unfold Footprint.Run
      simp only [addImmTcg, Footprint.vars, arithFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      by_cases hn : n.val = 31 <;> by_cases hd : d.val = 31
      · isla_bwd [s.pc.toNat, s.sp.toNat] using omega with [hσ, hn, hd]
        all_goals first
          | exact toNat_lt _
          | imm_end [UInt64.toNat_add]
          | (simp only [sint, Nat.reducePow]; omega)
          | omega
      · isla_bwd [s.pc.toNat, s.sp.toNat] using omega with [hσ, hn, hd]
        isla_gprs s using omega with [hσ, hn, hd]
        all_goals first
          | exact toNat_lt _
          | imm_end [UInt64.toNat_add]
          | (simp only [sint, Nat.reducePow]; omega)
          | omega
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hn, hd]
        isla_gprs s using omega with [hσ, hn, hd]
      all_goals first
        | exact toNat_lt _
        | imm_end [UInt64.toNat_add]
        | (simp only [sint, Nat.reducePow]; omega)
        | omega

/-- The trace of `ADD Xd|SP, Xn|SP, #imm` under `kvm` agrees with `exec` for every register
number, every immediate, and every state. -/
theorem addImm_kvm (P : Platform) (u : Unknown) (d n : Fin 32) (imm : Fin 4096) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] addImmKvm (arithFields d n imm)
      (.addImm d n imm) s := by
  rw [show addImmKvm = addImmTcg from rfl]
  exact (addImm_tcg P u d n imm s).of_reads
    (by isla_reads [addImmTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `SUB Xd|SP, Xn|SP, #imm` under `tcg` agrees with `exec` for every register number,
with register 31 the stack pointer, every immediate, and every state.  Its proof is that of
`addImm_tcg` with the model's subtraction. -/
theorem subImm_tcg (P : Platform) (u : Unknown) (d n : Fin 32) (imm : Fin 4096) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] subImmTcg (arithFields d n imm)
      (.subImm d n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : subImmTcg.opcode.word (arithFields d n imm) = encodeNat (.subImm d n imm) := by
      simp only [Opcode.word, Opcode.wordFrom, subImmTcg, arithFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [subImmTcg, Profile.sys_get, Profile.sys] at hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 20),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [subImmTcg, Footprint.vars, arithFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      isla_fwd h using omega with [hσ]
      all_goals imm_end [UInt64.toNat_sub]
    · subst h
      unfold Footprint.Run
      simp only [subImmTcg, Footprint.vars, arithFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      by_cases hn : n.val = 31 <;> by_cases hd : d.val = 31
      · isla_bwd [s.pc.toNat, s.sp.toNat] using omega with [hσ, hn, hd]
        all_goals first
          | exact toNat_lt _
          | imm_end [UInt64.toNat_sub]
          | (simp only [sint, Nat.reducePow]; omega)
          | omega
      · isla_bwd [s.pc.toNat, s.sp.toNat] using omega with [hσ, hn, hd]
        isla_gprs s using omega with [hσ, hn, hd]
        all_goals first
          | exact toNat_lt _
          | imm_end [UInt64.toNat_sub]
          | (simp only [sint, Nat.reducePow]; omega)
          | omega
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hn, hd]
        isla_gprs s using omega with [hσ, hn, hd]
      all_goals first
        | exact toNat_lt _
        | imm_end [UInt64.toNat_sub]
        | (simp only [sint, Nat.reducePow]; omega)
        | omega

/-- The trace of `SUB Xd|SP, Xn|SP, #imm` under `kvm` agrees with `exec` for every register
number, every immediate, and every state. -/
theorem subImm_kvm (P : Platform) (u : Unknown) (d n : Fin 32) (imm : Fin 4096) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] subImmKvm (arithFields d n imm)
      (.subImm d n imm) s := by
  rw [show subImmKvm = subImmTcg from rfl]
  exact (subImm_tcg P u d n imm s).of_reads
    (by isla_reads [subImmTcg, Profile.sys_get, Profile.sys])

/-- Proves that the outcome at the end of a path of the trace of `SUBS` with an immediate is
`exec`'s, for the first operand `a` and the immediate `b`.  The trace's flags are the bits of a
word of 4 bits, and its V flag compares the sign-extended result with the sum of the
sign-extended operands, which `omega` decides once the sign of `a`, the carry, and the sign of the
result are known. -/
syntax "subs_end " term:max term:max : tactic
macro_rules
  | `(tactic| subs_end $a $b) => `(tactic| (
      done_end
      simp only [Bool.cond_eq_ite, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      simp (disch := omega) only [State.subs, xsp_lt, xsp_31, setX_eq_setRegAt, setRegAt_lt,
        setRegAt_31, vflag]
      simp only [nflag, zflag, cflag, UInt64.toNat_sub, UInt64.toNat_ofNat', Nat.reducePow,
        State.mk.injEq, eq_self_iff_true, true_and, and_true]
      simp (disch := first | omega | (split <;> omega)) only [word_n, word_z, word_c, word_v]
      simp (disch := omega) only [Nat.mod_eq_of_lt, decide_eq_decide]
      repeat' apply And.intro
      all_goals first
        | (funext j
           split <;> (try with_reducible rfl)
           apply UInt64.toNat_inj.mp
           simp only [UInt64.toNat_ofNat', UInt64.toNat_sub, Nat.reducePow]
           omega)
        | ((repeat' split) <;> omega)
        | (rcases Nat.lt_or_ge $a 9223372036854775808 with _ | _ <;>
           rcases Nat.lt_or_ge ($a + (18446744073709551616 - $b)) 18446744073709551616 with
             _ | _ <;>
           rcases Nat.lt_or_ge (($a + (18446744073709551616 - $b)) % 18446744073709551616)
             9223372036854775808 with _ | _ <;>
           (repeat' split) <;> omega)))

set_option maxHeartbeats 8000000 in
/-- The trace of `SUBS Xd, Xn|SP, #imm` under `tcg` agrees with `exec` for every register number,
with register 31 the stack pointer as `n` and the zero register as `d`, every immediate, and every
state.  The forward direction takes the cases of `n` before the trace, so that `subs_end` names
the first operand. -/
theorem subsImm_tcg (P : Platform) (u : Unknown) (d n : Fin 32) (imm : Fin 4096) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] subsImmTcg (arithFields d n imm)
      (.subsImm d n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : subsImmTcg.opcode.word (arithFields d n imm) = encodeNat (.subsImm d n imm) := by
      simp only [Opcode.word, Opcode.wordFrom, subsImmTcg, arithFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [subsImmTcg, Profile.sys_get, Profile.sys] at hσ
    have : s.sp.toNat < 18446744073709551616 := toNat_lt s.sp
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 21),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [subsImmTcg, Footprint.vars, arithFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      by_cases hn : n.val = 31
      · isla_fwd h using omega with [hσ, hn]
        all_goals subs_end s.sp.toNat imm.val
      · isla_fwd h using omega with [hσ, hn]
        all_goals subs_end (regAt s n.val).toNat imm.val
    · subst h
      unfold Footprint.Run
      simp only [subsImmTcg, Footprint.vars, arithFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      by_cases hn : n.val = 31 <;> by_cases hd : d.val = 31
      · isla_bwd [s.pc.toNat, s.sp.toNat] using omega with [hσ, hn, hd]
        all_goals first
          | exact toNat_lt _
          | (apply Eq.symm; subs_end s.sp.toNat imm.val)
          | (simp only [sint, Nat.reducePow]; omega)
          | omega
      · isla_bwd [s.pc.toNat, s.sp.toNat] using omega with [hσ, hn, hd]
        isla_gprs s using omega with [hσ, hn, hd]
        all_goals first
          | exact toNat_lt _
          | (apply Eq.symm; subs_end s.sp.toNat imm.val)
          | (simp only [sint, Nat.reducePow]; omega)
          | omega
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hn, hd]
        isla_gprs s using omega with [hσ, hn, hd]
      all_goals first
        | exact toNat_lt _
        | (apply Eq.symm; subs_end (regAt s n.val).toNat imm.val)
        | (simp only [sint, Nat.reducePow]; omega)
        | omega

/-- The trace of `SUBS Xd, Xn|SP, #imm` under `kvm` agrees with `exec` for every register number,
every immediate, and every state. -/
theorem subsImm_kvm (P : Platform) (u : Unknown) (d n : Fin 32) (imm : Fin 4096) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] subsImmKvm (arithFields d n imm)
      (.subsImm d n imm) s := by
  rw [show subsImmKvm = subsImmTcg from rfl]
  exact (subsImm_tcg P u d n imm s).of_reads
    (by isla_reads [subsImmTcg, Profile.sys_get, Profile.sys])

/-- Proves that the outcome at the end of a path of the trace of `MOVZ` or `MOVK` is `exec`'s for
one value of `hw`, which the fact in brackets gives: with the shift a number, the trace's value and
the model's are the same bitwise expression in the register and the immediate. -/
syntax "move_end " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| move_end [$xs,*]) => `(tactic| (
      simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
        true_and]
      simp (disch := omega) only [x_lt, x_31, setX_eq_setRegAt, setRegAt_lt, setRegAt_31,
        State.mk.injEq, and_true, true_and]
      try (funext j; split <;> (try with_reducible rfl))
      try (apply UInt64.toNat_inj.mp
           simp (disch := omega) only [UInt64.toNat_ofNat', UInt64.toNat_or, UInt64.toNat_and,
             UInt64.toNat_not, UInt64.toNat_shiftLeft, UInt64.reduceToNat, UInt64.size,
             Nat.shiftLeft_eq, Nat.reduceShiftLeft, Nat.reducePow, Nat.reduceMod, Nat.reduceMul,
             Nat.reduceSub, Nat.mul_one, or_and_mod, Nat.mod_eq_of_lt, toNat_mod, $xs,*]
           try omega)))

set_option maxHeartbeats 4000000 in
/-- The trace of `MOVZ Xd, #imm, LSL #(16 * hw)` under `tcg` agrees with `exec` for every register
number, with register 31 the zero register, every immediate, every shift, and every state.  Both
directions take the 4 values of `hw` in turn. -/
theorem movz_tcg (P : Platform) (u : Unknown) (d : Fin 32) (imm : Fin 65536) (hw : Fin 4)
    (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] movzTcg (moveFields d imm hw)
      (.movz d imm hw) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : movzTcg.opcode.word (moveFields d imm hw) = encodeNat (.movz d imm hw) := by
      simp only [Opcode.word, Opcode.wordFrom, movzTcg, moveFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [movzTcg, Profile.sys_get, Profile.sys] at hσ
    have hk : hw.val = 0 ∨ hw.val = 1 ∨ hw.val = 2 ∨ hw.val = 3 := by omega
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 698),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [movzTcg, Footprint.vars, moveFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      rcases hk with hk | hk | hk | hk
      all_goals
        isla_fwd h using omega with [hσ, hk]
        all_goals move_end [hk]
    · subst h
      unfold Footprint.Run
      simp only [movzTcg, Footprint.vars, moveFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      rcases hk with hk | hk | hk | hk <;> by_cases hd : d.val = 31
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hk, hd]
        try isla_gprs s using omega with [hσ, hk, hd]
      all_goals first
        | exact toNat_lt _
        | move_end [hk]
        | (simp only [sint, Nat.reducePow]; omega)
        | omega

/-- The trace of `MOVZ Xd, #imm, LSL #(16 * hw)` under `kvm` agrees with `exec` for every register
number, every immediate, every shift, and every state. -/
theorem movz_kvm (P : Platform) (u : Unknown) (d : Fin 32) (imm : Fin 65536) (hw : Fin 4)
    (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] movzKvm (moveFields d imm hw)
      (.movz d imm hw) s := by
  rw [show movzKvm = movzTcg from rfl]
  exact (movz_tcg P u d imm hw s).of_reads
    (by isla_reads [movzTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `MOVK Xd, #imm, LSL #(16 * hw)` under `tcg` agrees with `exec` for every register
number, with register 31 the zero register, every immediate, every shift, and every state.  Both
directions take the 4 values of `hw` in turn. -/
theorem movk_tcg (P : Platform) (u : Unknown) (d : Fin 32) (imm : Fin 65536) (hw : Fin 4)
    (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] movkTcg (moveFields d imm hw)
      (.movk d imm hw) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : movkTcg.opcode.word (moveFields d imm hw) = encodeNat (.movk d imm hw) := by
      simp only [Opcode.word, Opcode.wordFrom, movkTcg, moveFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [movkTcg, Profile.sys_get, Profile.sys] at hσ
    have hk : hw.val = 0 ∨ hw.val = 1 ∨ hw.val = 2 ∨ hw.val = 3 := by omega
    have : (regAt s d.val).toNat < 18446744073709551616 := toNat_lt _
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 696),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [movkTcg, Footprint.vars, moveFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      rcases hk with hk | hk | hk | hk
      all_goals
        isla_fwd h using omega with [hσ, hk]
        all_goals move_end [hk]
    · subst h
      unfold Footprint.Run
      simp only [movkTcg, Footprint.vars, moveFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      rcases hk with hk | hk | hk | hk <;> by_cases hd : d.val = 31
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hk, hd]
        try isla_gprs s using omega with [hσ, hk, hd]
      all_goals first
        | exact toNat_lt _
        | move_end [hk]
        | (simp only [sint, Nat.reducePow]; omega)
        | omega

/-- The trace of `MOVK Xd, #imm, LSL #(16 * hw)` under `kvm` agrees with `exec` for every register
number, every immediate, every shift, and every state. -/
theorem movk_kvm (P : Platform) (u : Unknown) (d : Fin 32) (imm : Fin 65536) (hw : Fin 4)
    (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] movkKvm (moveFields d imm hw)
      (.movk d imm hw) s := by
  rw [show movkKvm = movkTcg from rfl]
  exact (movk_tcg P u d imm hw s).of_reads
    (by isla_reads [movkTcg, Profile.sys_get, Profile.sys])

/-- Proves that the outcome at the end of a path of the trace of `LSR` with an immediate is
`exec`'s: it rewrites the trace's value with `lsr_pos`, `lsr_zero`, `lsr_ones`, or `zero_shr` to
the model's shift. -/
macro "lsr_end" : tactic => `(tactic| (
  simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true,
    true_and]
  simp (disch := omega) only [x_lt, x_31, setX_eq_setRegAt, setRegAt_lt, setRegAt_31,
    State.mk.injEq, and_true, true_and, lsr_pos, lsr_zero, lsr_ones, zero_shr]))

set_option maxHeartbeats 8000000 in
/-- The trace of `LSR Xd, Xn, #sh` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, every shift, and every state.  Both directions evaluate the trace
with `omega` deciding remainders, comparisons, and the conditions of `ite` and `decide`, and the
backward direction builds the path of each of the 8 cases of a zero shift and of register 31
among `d` and `n`. -/
theorem lsrImm_tcg (P : Platform) (u : Unknown) (d n : Fin 32) (sh : Fin 64) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] lsrImmTcg (lsrImmFields d n sh)
      (.lsrImm d n sh) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : lsrImmTcg.opcode.word (lsrImmFields d n sh) = encodeNat (.lsrImm d n sh) := by
      simp only [Opcode.word, Opcode.wordFrom, lsrImmTcg, lsrImmFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [lsrImmTcg, Profile.sys_get, Profile.sys] at hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 78),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [lsrImmTcg, Footprint.vars, lsrImmFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      isla_fwd h using omega with [hσ, and63, sint, srem64, sub64, Nat.div_eq_of_lt,
        Nat.mod_eq_of_lt, ite_eq_left, decide_eq_true, decide_eq_false, Nat.zero_div, Nat.zero_mod,
        Nat.zero_or, Nat.zero_and, Nat.or_zero, Nat.and_zero]
      all_goals lsr_end
    · subst h
      unfold Footprint.Run
      simp only [lsrImmTcg, Footprint.vars, lsrImmFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      by_cases h0 : sh.val = 0 <;> by_cases hn : n.val = 31 <;> by_cases hd : d.val = 31
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hn, hd, and63, sint, srem64, sub64,
          Nat.div_eq_of_lt, Nat.mod_eq_of_lt, ite_eq_left, decide_eq_true, decide_eq_false,
          Nat.zero_div, Nat.zero_mod, Nat.zero_or, Nat.zero_and, Nat.or_zero, Nat.and_zero]
        try isla_gprs s using omega with [hσ, hn, hd, and63, sint, srem64, sub64,
          Nat.div_eq_of_lt, Nat.mod_eq_of_lt, ite_eq_left, decide_eq_true, decide_eq_false,
          Nat.zero_div, Nat.zero_mod, Nat.zero_or, Nat.zero_and, Nat.or_zero, Nat.and_zero]
      all_goals first
        | exact toNat_lt _
        | (apply Eq.symm; lsr_end)
        | (simp only [sint, Nat.reducePow]; omega)
        | omega

/-- The trace of `LSR Xd, Xn, #sh` under `kvm` agrees with `exec` for every register number, every
shift, and every state. -/
theorem lsrImm_kvm (P : Platform) (u : Unknown) (d n : Fin 32) (sh : Fin 64) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] lsrImmKvm (lsrImmFields d n sh)
      (.lsrImm d n sh) s := by
  rw [show lsrImmKvm = lsrImmTcg from rfl]
  exact (lsrImm_tcg P u d n sh s).of_reads
    (by isla_reads [lsrImmTcg, Profile.sys_get, Profile.sys])

/-- Proves that the outcome at the end of a path of the trace of `CSINC` is `exec`'s, with the
value of `State.condHolds` that the hypothesis `h` gives. -/
syntax "csinc_end " ident : tactic
macro_rules
  | `(tactic| csinc_end $h) => `(tactic| (
      try simp only [$h:ident, ↓reduceIte, Bool.false_eq_true, eq_self_iff_true]
      imm_end [UInt64.toNat_add]))

set_option maxHeartbeats 8000000 in
/-- The trace of `CSINC Xd, Xn, Xm, cond` under `tcg` agrees with `exec` for every register
number, with register 31 the zero register, every condition, and every state.  The forward
direction derives the value of `State.condHolds` on each path from the trace's condition with
`cond_fwd`.  The backward direction takes the cases of `condHolds` and of register 31 among `d`
and the register that the condition selects, evaluates both branches of the trace's fork on the
condition, takes the branch that `condHolds` selects, and proves the trace's condition with
`cond_bwd`. -/
theorem csinc_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (cond : Fin 16) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] csincTcg (csincFields d n m cond)
      (.csinc d n m cond) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : csincTcg.opcode.word (csincFields d n m cond) = encodeNat (.csinc d n m cond) := by
      simp only [Opcode.word, Opcode.wordFrom, csincTcg, csincFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [csincTcg, Profile.sys_get, Profile.sys] at hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 188),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [csincTcg, Footprint.vars, csincFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      isla_fwd h using omega with [hσ]
      all_goals first
        | (have hc : State.condHolds s cond = true := by cond_fwd s cond
           csinc_end hc)
        | (have hc : State.condHolds s cond = false := by cond_fwd s cond
           csinc_end hc)
    · subst h
      unfold Footprint.Run
      simp only [csincTcg, Footprint.vars, csincFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      by_cases hc : State.condHolds s cond = true
      · by_cases hn : n.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [if s.zFlag then 1 else 0, if s.cFlag then 1 else 0, if s.nFlag then 1 else 0,
            if s.vFlag then 1 else 0, s.pc.toNat] using omega with [hσ, hn, hd]
          refine Or.inl ?_
          isla_walk using omega with [hσ, hn, hd]
          try isla_gprs s using omega with [hσ, hn, hd]
        all_goals first
          | exact toNat_lt _
          | exact bit_lt _
          | cond_bwd hc s cond
          | csinc_end hc
          | (simp only [sint, Nat.reducePow]; omega)
          | omega
      · by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
        all_goals
          isla_bwd [if s.zFlag then 1 else 0, if s.cFlag then 1 else 0, if s.nFlag then 1 else 0,
            if s.vFlag then 1 else 0, s.pc.toNat] using omega with [hσ, hm, hd]
          refine Or.inr ?_
          isla_walk using omega with [hσ, hm, hd]
          try isla_gprs s using omega with [hσ, hm, hd]
        all_goals first
          | exact toNat_lt _
          | exact bit_lt _
          | cond_bwd hc s cond
          | csinc_end hc
          | (simp only [sint, Nat.reducePow]; omega)
          | omega

/-- The trace of `CSINC Xd, Xn, Xm, cond` under `kvm` agrees with `exec` for every register number,
every condition, and every state. -/
theorem csinc_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (cond : Fin 16) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] csincKvm (csincFields d n m cond)
      (.csinc d n m cond) s := by
  rw [show csincKvm = csincTcg from rfl]
  exact (csinc_tcg P u d n m cond s).of_reads
    (by isla_reads [csincTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `ADR Xd` under `tcg` agrees with `exec` for every register number, with register
31 the zero register, every immediate, and every state. -/
theorem adr_tcg (P : Platform) (u : Unknown) (d : Fin 32) (lo : Fin 4) (hi : Fin 524288)
    (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] adrTcg (adrFields d lo hi)
      (.adr d lo hi) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : adrTcg.opcode.word (adrFields d lo hi) = encodeNat (.adr d lo hi) := by
      simp only [Opcode.word, Opcode.wordFrom, adrTcg, adrFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [adrTcg, Profile.sys_get, Profile.sys] at hσ
    have : s.pc.toNat < 18446744073709551616 := toNat_lt s.pc
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 34),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [adrTcg, Footprint.vars, adrFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      isla_fwd h using omega with [hσ]
      all_goals imm_end [UInt64.toNat_add, sext21]
    · subst h
      unfold Footprint.Run
      simp only [adrTcg, Footprint.vars, adrFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      by_cases hd : d.val = 31
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hd]
        try isla_gprs s using omega with [hσ, hd]
      all_goals first
        | exact toNat_lt _
        | imm_end [UInt64.toNat_add, sext21]
        | (simp only [sint, Nat.reducePow]; omega)
        | omega

/-- The trace of `ADR Xd` under `kvm` agrees with `exec` for every register number, every
immediate, and every state. -/
theorem adr_kvm (P : Platform) (u : Unknown) (d : Fin 32) (lo : Fin 4) (hi : Fin 524288)
    (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] adrKvm (adrFields d lo hi)
      (.adr d lo hi) s := by
  rw [show adrKvm = adrTcg from rfl]
  exact (adr_tcg P u d lo hi s).of_reads
    (by isla_reads [adrTcg, Profile.sys_get, Profile.sys])

set_option maxHeartbeats 4000000 in
/-- The trace of `ADRP Xd` under `tcg` agrees with `exec` for every register number, with register
31 the zero register, every immediate, and every state. -/
theorem adrp_tcg (P : Platform) (u : Unknown) (d : Fin 32) (lo : Fin 4) (hi : Fin 524288)
    (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] adrpTcg (adrFields d lo hi)
      (.adrp d lo hi) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : adrpTcg.opcode.word (adrFields d lo hi) = encodeNat (.adrp d lo hi) := by
      simp only [Opcode.word, Opcode.wordFrom, adrpTcg, adrFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [adrpTcg, Profile.sys_get, Profile.sys] at hσ
    have : s.pc.toNat < 18446744073709551616 := toNat_lt s.pc
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 35),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [adrpTcg, Footprint.vars, adrFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      isla_fwd h using omega with [hσ]
      all_goals imm_end [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_mod,
        sext21, and_page]
    · subst h
      unfold Footprint.Run
      simp only [adrpTcg, Footprint.vars, adrFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      by_cases hd : d.val = 31
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hd]
        try isla_gprs s using omega with [hσ, hd]
      all_goals first
        | exact toNat_lt _
        | imm_end [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_mul, UInt64.toNat_mod, sext21,
            and_page]
        | (simp only [sint, Nat.reducePow]; omega)
        | omega

/-- The trace of `ADRP Xd` under `kvm` agrees with `exec` for every register number, every
immediate, and every state. -/
theorem adrp_kvm (P : Platform) (u : Unknown) (d : Fin 32) (lo : Fin 4) (hi : Fin 524288)
    (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] adrpKvm (adrFields d lo hi)
      (.adrp d lo hi) s := by
  rw [show adrpKvm = adrpTcg from rfl]
  exact (adrp_tcg P u d lo hi s).of_reads
    (by isla_reads [adrpTcg, Profile.sys_get, Profile.sys])

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.addImm_tcg
#print axioms TestSupport.A64.Isla.addImm_kvm
#print axioms TestSupport.A64.Isla.subImm_tcg
#print axioms TestSupport.A64.Isla.subImm_kvm
#print axioms TestSupport.A64.Isla.subsImm_tcg
#print axioms TestSupport.A64.Isla.subsImm_kvm
#print axioms TestSupport.A64.Isla.movz_tcg
#print axioms TestSupport.A64.Isla.movz_kvm
#print axioms TestSupport.A64.Isla.movk_tcg
#print axioms TestSupport.A64.Isla.movk_kvm
#print axioms TestSupport.A64.Isla.lsrImm_tcg
#print axioms TestSupport.A64.Isla.lsrImm_kvm
#print axioms TestSupport.A64.Isla.csinc_tcg
#print axioms TestSupport.A64.Isla.csinc_kvm
#print axioms TestSupport.A64.Isla.adr_tcg
#print axioms TestSupport.A64.Isla.adr_kvm
#print axioms TestSupport.A64.Isla.adrp_tcg
#print axioms TestSupport.A64.Isla.adrp_kvm
