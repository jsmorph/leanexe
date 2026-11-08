import F7.FPToFixed
import F7.FPMul32

/-!
FPToFixed of Sail's Lean translation of the Armv9.4-A model, as FCVTZU Xd, Sn calls it,
`FPToFixed(op, 0, TRUE, FPCR, FPRounding_ZERO, 64)` on a 32-bit operand under FPCR 0x02000000,
returns Talos's `i64TruncSatF32U` of its operand for every word and sets in FPSR the bits of
`fixMask32`, from every state that satisfies `Hyp`.  The proof follows `fpToFixed_run` of
`F7/FPToFixed.lean` with the binary32 unpacking: for a finite word whose magnitude is `m` in units
of 2^-149, `fix32_pos`, `fix32_neg0`, and `fix32_neg1` give the floor and the test of an integer
value through the quotient and the remainder of `m` by 2^149, the quotient that Talos's
`IEEE32.truncatedInt` takes (`trunc32_fin`); SatQ at 64 bits is `bind_satQ` of the 64-bit module.

`fpToFixed32S_eq_i32TruncSatF32S` states the same of FCVTZS Wd, Sn,
`FPToFixed(op, 0, FALSE, FPCR, FPRounding_ZERO, 32)`, and Talos's `i32TruncSatF32S`, with
`fixMask32S`.  SignedSatQ at 32 bits saturates the truncation `t` to `[-2^31, 2^31 - 1]` and returns
its low 32 bits, `BitVec.ofInt 32` of the saturated value (`bind_satQS`, `subrange32`), which is
Talos's `intToUInt32` inside the range (`intToUInt32_ofInt`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem scale_149 (m : ℕ) :
    (m : ℝ) * (2 : ℝ) ^ (-149 : ℤ) = (m : ℝ) / ((2 ^ 149 : ℕ) : ℝ) := by
  rw [zpow_neg, zpow_ofNat, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]

/-- The value of a nonnegative finite binary32 word: its truncation and whether it is inexact. -/
theorem fix32_pos (m : ℕ) :
    round_down ((m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) = ((m / 2 ^ 149 : ℕ) : ℤ) ∧
      (sub_real ((m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) (to_real ((m / 2 ^ 149 : ℕ) : ℤ)) == 0) =
        decide (m % 2 ^ 149 = 0) := by
  rw [scale_149]
  have hd : 0 < 2 ^ 149 := pow_pos (by norm_num) 149
  refine ⟨floor_div_nat _ _, ?_⟩
  rw [err_div _ _ hd, beq_zero_div _ _ hd]

/-- The value of a negative finite binary32 word whose magnitude is a multiple of 2^149. -/
theorem fix32_neg0 (m : ℕ) (hr : m % 2 ^ 149 = 0) :
    round_down (-(m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) = -((m / 2 ^ 149 : ℕ) : ℤ) ∧
      (sub_real (-(m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) (to_real (-((m / 2 ^ 149 : ℕ) : ℤ))) == 0) =
        true := by
  rw [neg_mul, scale_149, nat_div_exact m _ (pow_pos (by norm_num) 149) hr]
  have e : -(((m / 2 ^ 149 : ℕ) : ℝ)) = ((-((m / 2 ^ 149 : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [Int.cast_neg, Int.cast_natCast]
  refine ⟨?_, ?_⟩
  · rw [e]; simp only [round_down, Int.floor_intCast]
  · rw [beq_eq_decide, decide_eq_true_iff]
    simp only [sub_real, to_real, Int.cast_neg, Int.cast_natCast, sub_self]

/-- The value of a negative finite binary32 word whose magnitude is not a multiple of 2^149. -/
theorem fix32_neg1 (m : ℕ) (hr : m % 2 ^ 149 ≠ 0) :
    round_down (-(m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) = -((m / 2 ^ 149 : ℕ) : ℤ) - 1 ∧
      (sub_real (-(m : ℝ) * (2 : ℝ) ^ (-149 : ℤ))
        (to_real (-((m / 2 ^ 149 : ℕ) : ℤ) - 1)) == 0) = false := by
  rw [neg_mul, scale_149]
  have hd : 0 < 2 ^ 149 := pow_pos (by norm_num) 149
  refine ⟨floor_neg_nat_div m _ hd hr, ?_⟩
  obtain ⟨hx, h1, -⟩ := nat_div_parts m _ hd
  rw [beq_eq_decide, decide_eq_false_iff_not]
  simp only [sub_real, to_real, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_natCast, hx]
  intro h0
  linarith

theorem val32_of_nan (x : BitVec 32) (h : isNaNT (ty32 x) = true) : val32 x = 0 := by
  unfold ty32 at h
  unfold val32
  split_ifs at h ⊢ <;> first | rfl | exact absurd h (by decide)

theorem trunc32_fin (x : BitVec 32) (h : ex32 x ≠ 255) :
    Wasm.IEEE32.truncatedInt (UInt32.ofBitVec x) =
      some (if sg32 x then -((Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x) / 2 ^ 149 : ℕ) : ℤ)
        else ((Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x) / 2 ^ 149 : ℕ) : ℤ)) := by
  have hf : Wasm.IEEE32.isFinite (UInt32.ofBitVec x) = true := by
    simp only [Wasm.IEEE32.isFinite, t_exp32]; simpa using h
  unfold Wasm.IEEE32.truncatedInt
  rw [ite_eq_left hf, t_sign32]

theorem trunc32_none (x : BitVec 32) (h : ex32 x = 255) :
    Wasm.IEEE32.truncatedInt (UInt32.ofBitVec x) = none := by
  have hf : Wasm.IEEE32.isFinite (UInt32.ofBitVec x) = false := by
    simp only [Wasm.IEEE32.isFinite, t_exp32, h]; rfl
  unfold Wasm.IEEE32.truncatedInt
  rw [ite_eq_right (by simp [hf])]

theorem ex32_of_nan (x : BitVec 32) (h : isNaNT (ty32 x) = true) : ex32 x = 255 := by
  by_contra he
  unfold ty32 at h
  split_ifs at h <;> exact absurd h (by decide)

theorem intToUInt64_nat32 (q : ℕ) :
    (Wasm.IEEE32.intToUInt64 (q : ℤ)).toBitVec = BitVec.ofNat 64 q := by
  unfold Wasm.IEEE32.intToUInt64
  rw [ite_eq_right (by omega), Int.natAbs_natCast]
  rfl

/-- The bits of FPSR that FPToFixed sets for a binary32 operand under FPCR 0x02000000, unsigned at
64 bits with no fraction bits and rounding toward zero: IOC for a NaN, an infinity, or a truncation
outside `[0, 2^64)`, and IXC for an inexact truncation inside it. -/
def fixMask32 (a : BitVec 32) : BitVec 64 :=
  match Wasm.IEEE32.truncatedInt (UInt32.ofBitVec a) with
  | none => 1#64
  | some t =>
    if t < 0 ∨ 2 ^ 64 ≤ t then 1#64
    else if Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) % 2 ^ 149 = 0 then 0#64 else 0x10#64

set_option hygiene false in
/-- Closes a case of `fpToFixed32_run` once the run has reached its result. -/
macro "fix_fin32" : tactic => `(tactic| (
  refine ⟨_, ok_congr ?_, ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
  · first
    | (split_ifs <;>
        first
        | (exfalso; omega)
        | decide
        | (rw [intToUInt64_nat32, Int.toNat_natCast])
        | (obtain rfl : q = 0 := by omega
           decide)
        | (obtain rfl : q = 18446744073709551615 := by omega
           decide))
    | rfl
  · simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
      upd_or _ _ (by norm_num : 4 < 64), (or_masks _).2.2.1, (or_masks _).2.1]
    split_ifs <;>
      first
      | (exfalso; omega)
      | rfl
      | (rw [BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)))

set_option maxHeartbeats 160000 in
theorem fpToFixed32_run (a : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPToFixed a 0 true fpcrV .FPRounding_ZERO 64).run s =
        .ok (Wasm.i64TruncSatF32U (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| fixMask32 a) ∧ Frame s s' := by
  subst hs
  simp only [FPToFixed]
  sail_simp [bne, h.hfi, h.hps, h.nrw, h.aa64]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run32 a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp [ty_nan_or, mult_pow_zero]
  simp only [Wasm.i64TruncSatF32U, Wasm.IEEE32.truncSatI64U, t_isNaN32, fixMask32]
  by_cases hn : isNaNT (ty32 a) = true
  · rw [val32_of_nan a hn, trunc32_none a (ex32_of_nan a hn)]
    simp only [hn, ↓reduceIte]
    sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, fix_zero,
      bind_satQ, satI]
    refine ⟨_, rfl, ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
    simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
      (or_masks _).2.2.1]
  · have hn' : isNaNT (ty32 a) = false := by simpa using hn
    simp only [hn', Bool.false_eq_true, ↓reduceIte]
    by_cases hi : ty32 a = .FPType_Infinity
    · obtain ⟨n, hn1, hn2⟩ := inf_val_nat
      unfold val32
      obtain ⟨he, hf⟩ := ty32_inf a hi
      rw [trunc32_none a he, ite_eq_left he, ite_eq_left hf, hn1, t_sign32]
      cases hsa : sg32 a
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have o1 : decide (2 ^ 64 - 1 < (n : ℤ) ∨ (n : ℤ) < 0) = true :=
          decide_eq_true (by omega)
        have s1 : satI (n : ℤ) = 2 ^ 64 - 1 := by unfold satI; rw [ite_eq_left (by omega)]
        sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr,
          fix_nat, bind_satQ, o1, s1]
        refine ⟨_, ok_congr (by decide), ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
        simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
          (or_masks _).2.2.1]
      · simp only [↓reduceIte]
        have o1 : decide (2 ^ 64 - 1 < -(n : ℤ) ∨ -(n : ℤ) < 0) = true :=
          decide_eq_true (by omega)
        have s1 : satI (-(n : ℤ)) = 0 := by
          unfold satI; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr,
          fix_negnat, bind_satQ, o1, s1]
        refine ⟨_, rfl, ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
        simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
          (or_masks _).2.2.1]
    · have hfin := ty32_fin a hi hn'
      rw [val32_fin a hfin, sv32_eq, trunc32_fin a hfin]
      generalize Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) = m
      cases hsa : sg32 a
      · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_natCast]
        rw [(fix32_pos m).1, (fix32_pos m).2]
        generalize m / 2 ^ 149 = q
        generalize m % 2 ^ 149 = r
        have o0 : decide ((q : ℤ) < 0) = false := decide_eq_false (by omega)
        sail_simp [o0, bind_satQ]
        by_cases hq64 : 2 ^ 64 ≤ q
        · have o1 : decide (2 ^ 64 - 1 < (q : ℤ) ∨ (q : ℤ) < 0) = true :=
            decide_eq_true (by omega)
          have s1 : satI (q : ℤ) = 2 ^ 64 - 1 := by unfold satI; rw [ite_eq_left (by omega)]
          sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
          fix_fin32
        · have o1 : decide (2 ^ 64 - 1 < (q : ℤ) ∨ (q : ℤ) < 0) = false :=
            decide_eq_false (by omega)
          have s1 : satI (q : ℤ) = q := by
            unfold satI; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          by_cases hr0 : r = 0
          · sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1,
              hr0]
            fix_fin32
          · sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1,
              hr0]
            fix_fin32
      · simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast]
        by_cases hr0 : m % 2 ^ 149 = 0
        · rw [(fix32_neg0 m hr0).1, (fix32_neg0 m hr0).2]
          generalize m / 2 ^ 149 = q
          generalize m % 2 ^ 149 = r at hr0 ⊢
          sail_simp [bind_satQ]
          by_cases hq0 : q = 0
          · subst hq0
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, satI,
              Nat.cast_zero, neg_zero]
            fix_fin32
          · have o1 : decide (2 ^ 64 - 1 < -(q : ℤ) ∨ -(q : ℤ) < 0) = true :=
              decide_eq_true (by omega)
            have s1 : satI (-(q : ℤ)) = 0 := by
              unfold satI; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
            fix_fin32
        · rw [(fix32_neg1 m hr0).1, (fix32_neg1 m hr0).2]
          generalize m / 2 ^ 149 = q
          generalize m % 2 ^ 149 = r at hr0 ⊢
          have o0 : decide (-(q : ℤ) - 1 < 0) = true := decide_eq_true (by omega)
          sail_simp [o0, bind_satQ, sub_add_cancel]
          by_cases hq0 : q = 0
          · subst hq0
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, satI,
              Nat.cast_zero, neg_zero]
            fix_fin32
          · have o1 : decide (2 ^ 64 - 1 < -(q : ℤ) ∨ -(q : ℤ) < 0) = true :=
              decide_eq_true (by omega)
            have s1 : satI (-(q : ℤ)) = 0 := by
              unfold satI; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
            fix_fin32

/-- FPToFixed of a binary32 word at 64 bits under FPCR 0x02000000, unsigned with no fraction bits
and rounding toward zero, returns Talos's `i64TruncSatF32U` for every word from every state that
satisfies the state hypothesis.  FPSR becomes `fpsr ||| fixMask32 a`, and the other registers, the
memory, the tags, the cycle count, and the output do not change. -/
theorem fpToFixed32_eq_i64TruncSatF32U (a : BitVec 32) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPToFixed a 0 true fpcrV .FPRounding_ZERO 64).run s =
        .ok (Wasm.i64TruncSatF32U (UInt32.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| fixMask32 a) ∧ Frame s s' :=
  fpToFixed32_run a h rfl

theorem subrange32 (t : ℤ) :
    BitVec.setWidth 32 (integer_subrange t (32 - 1) 0) = BitVec.ofInt 32 t := by
  apply BitVec.eq_of_toNat_eq
  simp only [integer_subrange, get_slice_int, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofInt, Int.reduceSub, Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd,
    Nat.shiftRight_zero, Nat.reducePow, Nat.cast_ofNat]
  omega

/-- The integer that SatQ saturates `t` to at 32 bits, signed. -/
def satS (t : ℤ) : ℤ := if 2 ^ 31 - 1 < t then 2 ^ 31 - 1 else if t < -2 ^ 31 then -2 ^ 31 else t

theorem bind_satQS {β} (t : ℤ) (f : BitVec 32 × Bool → SailM β) (σ : State) :
    (SatQ t 32 false >>= f).run σ =
      (f (BitVec.ofInt 32 (satS t), decide (2 ^ 31 - 1 < t ∨ t < -2 ^ 31))).run
        (bump .bool (bump .int (bump .bool (bump (.bitvector 32) σ)))) := by
  simp only [SatQ, SignedSatQ]
  sail_simp [ipow, Nat.cast_ofNat, Int.reduceSub]
  congr 2
  unfold satS
  by_cases h1 : 2 ^ 31 - 1 < t
  · simp only [↓reduceIte, h1, true_or, decide_true, Prod.mk.injEq, and_true]
    exact subrange32 _
  · by_cases h2 : t < -2 ^ 31
    · simp only [↓reduceIte, h1, h2, or_true, decide_true, decide_false, Prod.mk.injEq]
      exact ⟨subrange32 _, rfl⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, h1, h2, or_false, decide_false, Prod.mk.injEq,
        and_true]
      exact subrange32 _

theorem intToUInt32_ofInt (v : ℤ) (h1 : -2 ^ 31 < v) (h2 : v < 2 ^ 31 - 1) :
    (Wasm.IEEE32.intToUInt32 v).toBitVec = BitVec.ofInt 32 v := by
  unfold Wasm.IEEE32.intToUInt32
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 _).toNat = _
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  split_ifs with hv <;> omega

/-- The bits of FPSR that FPToFixed sets for a binary32 operand under FPCR 0x02000000, signed at
32 bits with no fraction bits and rounding toward zero: IOC for a NaN, an infinity, or a truncation
outside `[-2^31, 2^31)`, and IXC for an inexact truncation inside it. -/
def fixMask32S (a : BitVec 32) : BitVec 64 :=
  match Wasm.IEEE32.truncatedInt (UInt32.ofBitVec a) with
  | none => 1#64
  | some t =>
    if 2 ^ 31 - 1 < t ∨ t < -2 ^ 31 then 1#64
    else if Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) % 2 ^ 149 = 0 then 0#64 else 0x10#64

set_option hygiene false in
/-- Closes a case of `fpToFixed32S_run` once the run has reached its result. -/
macro "fix_fin32S" : tactic => `(tactic| (
  refine ⟨_, ok_congr ?_, ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
  · first
    | (split_ifs <;>
        first
        | (exfalso; omega)
        | decide
        | exact (intToUInt32_ofInt _ (by omega) (by omega)).symm
        | (obtain rfl : q = 0 := by omega
           decide)
        | (obtain rfl : q = 2147483648 := by omega
           decide)
        | (obtain rfl : q = 2147483647 := by omega
           decide))
    | rfl
  · simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
      upd_or _ _ (by norm_num : 4 < 64), (or_masks _).2.2.1, (or_masks _).2.1]
    split_ifs <;>
      first
      | (exfalso; omega)
      | rfl
      | (rw [BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)))

set_option maxHeartbeats 170000 in
theorem fpToFixed32S_run (a : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPToFixed a 0 false fpcrV .FPRounding_ZERO 32).run s =
        .ok (Wasm.i32TruncSatF32S (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| fixMask32S a) ∧ Frame s s' := by
  subst hs
  simp only [FPToFixed]
  sail_simp [bne, h.hfi, h.hps, h.nrw, h.aa64]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run32 a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp [ty_nan_or, mult_pow_zero]
  simp only [Wasm.i32TruncSatF32S, Wasm.IEEE32.truncSatI32S, t_isNaN32, fixMask32S]
  by_cases hn : isNaNT (ty32 a) = true
  · rw [val32_of_nan a hn, trunc32_none a (ex32_of_nan a hn)]
    simp only [hn, ↓reduceIte]
    sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, fix_zero,
      bind_satQS, satS]
    refine ⟨_, rfl, ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
    simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
      (or_masks _).2.2.1]
  · have hn' : isNaNT (ty32 a) = false := by simpa using hn
    simp only [hn', Bool.false_eq_true, ↓reduceIte]
    by_cases hi : ty32 a = .FPType_Infinity
    · obtain ⟨n, hn1, hn2⟩ := inf_val_nat
      unfold val32
      obtain ⟨he, hf⟩ := ty32_inf a hi
      rw [trunc32_none a he, ite_eq_left he, ite_eq_left hf, hn1, t_sign32]
      cases hsa : sg32 a
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have o1 : decide (2 ^ 31 - 1 < (n : ℤ) ∨ (n : ℤ) < -2 ^ 31) = true :=
          decide_eq_true (by omega)
        have s1 : satS (n : ℤ) = 2 ^ 31 - 1 := by unfold satS; rw [ite_eq_left (by omega)]
        sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr,
          fix_nat, bind_satQS, o1, s1]
        refine ⟨_, ok_congr (by decide), ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
        simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
          (or_masks _).2.2.1]
      · simp only [↓reduceIte]
        have o1 : decide (2 ^ 31 - 1 < -(n : ℤ) ∨ -(n : ℤ) < -2 ^ 31) = true :=
          decide_eq_true (by omega)
        have s1 : satS (-(n : ℤ)) = -2 ^ 31 := by
          unfold satS; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr,
          fix_negnat, bind_satQS, o1, s1]
        refine ⟨_, ok_congr (by decide), ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
        simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
          (or_masks _).2.2.1]
    · have hfin := ty32_fin a hi hn'
      rw [val32_fin a hfin, sv32_eq, trunc32_fin a hfin]
      generalize Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) = m
      cases hsa : sg32 a
      · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_natCast]
        rw [(fix32_pos m).1, (fix32_pos m).2]
        generalize m / 2 ^ 149 = q
        generalize m % 2 ^ 149 = r
        have o0 : decide ((q : ℤ) < 0) = false := decide_eq_false (by omega)
        sail_simp [o0, bind_satQS]
        by_cases hq : 2 ^ 31 - 1 < (q : ℤ)
        · have o1 : decide (2 ^ 31 - 1 < (q : ℤ) ∨ (q : ℤ) < -2 ^ 31) = true :=
            decide_eq_true (by omega)
          have s1 : satS (q : ℤ) = 2 ^ 31 - 1 := by unfold satS; rw [ite_eq_left hq]
          sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
          fix_fin32S
        · have o1 : decide (2 ^ 31 - 1 < (q : ℤ) ∨ (q : ℤ) < -2 ^ 31) = false :=
            decide_eq_false (by omega)
          have s1 : satS (q : ℤ) = q := by
            unfold satS; rw [ite_eq_right hq, ite_eq_right (by omega)]
          by_cases hr0 : r = 0
          · sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1,
              hr0]
            fix_fin32S
          · sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1,
              hr0]
            fix_fin32S
      · simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast]
        by_cases hr0 : m % 2 ^ 149 = 0
        · rw [(fix32_neg0 m hr0).1, (fix32_neg0 m hr0).2]
          generalize m / 2 ^ 149 = q
          generalize m % 2 ^ 149 = r at hr0 ⊢
          sail_simp [bind_satQS]
          by_cases hq : -(q : ℤ) < -2 ^ 31
          · have o1 : decide (2 ^ 31 - 1 < -(q : ℤ) ∨ -(q : ℤ) < -2 ^ 31) = true :=
              decide_eq_true (by omega)
            have s1 : satS (-(q : ℤ)) = -2 ^ 31 := by
              unfold satS; rw [ite_eq_right (by omega), ite_eq_left hq]
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
            fix_fin32S
          · have o1 : decide (2 ^ 31 - 1 < -(q : ℤ) ∨ -(q : ℤ) < -2 ^ 31) = false :=
              decide_eq_false (by omega)
            have s1 : satS (-(q : ℤ)) = -(q : ℤ) := by
              unfold satS; rw [ite_eq_right (by omega), ite_eq_right hq]
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
            fix_fin32S
        · rw [(fix32_neg1 m hr0).1, (fix32_neg1 m hr0).2]
          generalize m / 2 ^ 149 = q
          generalize m % 2 ^ 149 = r at hr0 ⊢
          have o0 : decide (-(q : ℤ) - 1 < 0) = true := decide_eq_true (by omega)
          sail_simp [o0, bind_satQS, sub_add_cancel]
          by_cases hq : -(q : ℤ) < -2 ^ 31
          · have o1 : decide (2 ^ 31 - 1 < -(q : ℤ) ∨ -(q : ℤ) < -2 ^ 31) = true :=
              decide_eq_true (by omega)
            have s1 : satS (-(q : ℤ)) = -2 ^ 31 := by
              unfold satS; rw [ite_eq_right (by omega), ite_eq_left hq]
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
            fix_fin32S
          · have o1 : decide (2 ^ 31 - 1 < -(q : ℤ) ∨ -(q : ℤ) < -2 ^ 31) = false :=
              decide_eq_false (by omega)
            have s1 : satS (-(q : ℤ)) = -(q : ℤ) := by
              unfold satS; rw [ite_eq_right (by omega), ite_eq_right hq]
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
            fix_fin32S

/-- FPToFixed of a binary32 word at 32 bits under FPCR 0x02000000, signed with no fraction bits
and rounding toward zero, returns Talos's `i32TruncSatF32S` for every word from every state that
satisfies the state hypothesis.  FPSR becomes `fpsr ||| fixMask32S a`, and the other registers,
the memory, the tags, the cycle count, and the output do not change. -/
theorem fpToFixed32S_eq_i32TruncSatF32S (a : BitVec 32) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPToFixed a 0 false fpcrV .FPRounding_ZERO 32).run s =
        .ok (Wasm.i32TruncSatF32S (UInt32.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| fixMask32S a) ∧ Frame s s' :=
  fpToFixed32S_run a h rfl

end F7
