import F7.FPMul

/-!
FPToFixed of Sail's Lean translation of the Armv9.4-A model, as FCVTZU Xd, Dn calls it,
`FPToFixed(op, 0, TRUE, FPCR, FPRounding_ZERO, 64)` on a 64-bit operand under FPCR 0x02000000,
returns Talos's `i64TruncSatF64U` of its operand for every word and sets in FPSR the bits of
`fixMask`, from every state that satisfies `Hyp`.

FPToFixed unpacks the operand, signals Invalid Operation for a NaN, whose value FPUnpack gives as
0, takes the floor of the value, adds 1 to the floor of a negative value that is not an integer,
which rounds toward zero, and saturates the integer to `[0, 2^64 - 1]` with SatQ.  It then
signals Invalid Operation when SatQ saturates and Inexact when the value was not an integer.
`bind_satQ` gives SatQ's result.  For a finite word whose magnitude is `m` in units of 2^-1074,
`fix_pos`, `fix_neg0`, and `fix_neg1` give the floor and the test of an integer value through the
quotient and the remainder of `m` by 2^1074, the quotient that Talos's `truncatedInt` takes
(`trunc_fin`).  FPUnpack gives an infinity the value ±2^1000000, an integer of at least 2^64
(`inf_val_nat`), so SatQ saturates it, and Talos's `truncatedInt` gives an infinity and a NaN no
value (`trunc_none`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

/-- The test of a NaN that FPToFixed and FPCompare write. -/
theorem ty_nan_or (t : FPType) :
    ((t == .FPType_SNaN) || (t == .FPType_QNaN)) = isNaNT t := by
  cases t <;> rfl

theorem mult_pow_zero (x : ℝ) : mult_real x (real_power 2 0) = x := by
  simp [mult_real, real_power]

theorem subrange64 (t : ℤ) (ht : 0 ≤ t) :
    BitVec.setWidth 64 (integer_subrange t (64 - 1) 0) = BitVec.ofNat 64 t.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, subrange_toNat t _ ht (by norm_num)]
  simp

/-- The integer that SatQ saturates `t` to at 64 bits, unsigned. -/
def satI (t : ℤ) : ℤ := if 2 ^ 64 - 1 < t then 2 ^ 64 - 1 else if t < 0 then 0 else t

theorem bind_satQ {β} (t : ℤ) (f : BitVec 64 × Bool → SailM β) (σ : State) :
    (SatQ t 64 true >>= f).run σ =
      (f (BitVec.ofNat 64 (satI t).toNat, decide (2 ^ 64 - 1 < t ∨ t < 0))).run
        (bump .bool (bump .int (bump .bool (bump (.bitvector 64) σ)))) := by
  simp only [SatQ, UnsignedSatQ]
  sail_simp [ipow, Nat.cast_ofNat]
  congr 2
  unfold satI
  by_cases h1 : 2 ^ 64 - 1 < t
  · simp only [↓reduceIte, h1, true_or, decide_true, Prod.mk.injEq, and_true]
    exact subrange64 _ (by norm_num)
  · by_cases h2 : t < 0
    · simp only [↓reduceIte, h1, h2, or_true, decide_true, decide_false, Prod.mk.injEq]
      exact ⟨subrange64 _ le_rfl, rfl⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, h1, h2, or_false, decide_false, Prod.mk.injEq,
        and_true]
      exact subrange64 _ (by omega)

theorem scale_1074 (m : ℕ) :
    (m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) = (m : ℝ) / ((2 ^ 1074 : ℕ) : ℝ) := by
  rw [zpow_neg, zpow_ofNat, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]

/-- `m / d` as the quotient of naturals and a fraction in `[0, 1)`. -/
theorem nat_div_parts (m d : ℕ) (hd : 0 < d) :
    (m : ℝ) / d = ((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ) / d ∧
      ((m % d : ℕ) : ℝ) / d < 1 ∧ (m % d ≠ 0 → 0 < ((m % d : ℕ) : ℝ) / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have e : (m : ℝ) = d * ((m / d : ℕ) : ℝ) + ((m % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod m d).symm
  have r2 : ((m % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt m hd
  refine ⟨by rw [e]; field_simp, (div_lt_one hd').mpr r2, fun hr => div_pos ?_ hd'⟩
  exact_mod_cast Nat.pos_of_ne_zero hr

theorem floor_neg_nat_div (m d : ℕ) (hd : 0 < d) (hr : m % d ≠ 0) :
    ⌊-((m : ℝ) / d)⌋ = -((m / d : ℕ) : ℤ) - 1 := by
  obtain ⟨hx, h1, h2⟩ := nat_div_parts m d hd
  have h3 := h2 hr
  rw [Int.floor_eq_iff, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_natCast, hx]
  constructor <;> linarith

theorem nat_div_exact (m d : ℕ) (hd : 0 < d) (hr : m % d = 0) :
    (m : ℝ) / d = ((m / d : ℕ) : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have e : (m : ℝ) = d * ((m / d : ℕ) : ℝ) := by
    have h := Nat.div_add_mod m d
    rw [hr, Nat.add_zero] at h
    exact_mod_cast h.symm
  rw [e, mul_div_cancel_left₀ _ hd']

/-- The value of a nonnegative finite word: its truncation and whether it is inexact. -/
theorem fix_pos (m : ℕ) :
    round_down ((m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) = ((m / 2 ^ 1074 : ℕ) : ℤ) ∧
      (sub_real ((m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) (to_real ((m / 2 ^ 1074 : ℕ) : ℤ)) == 0) =
        decide (m % 2 ^ 1074 = 0) := by
  rw [scale_1074]
  have hd : 0 < 2 ^ 1074 := pow_pos (by norm_num) 1074
  refine ⟨floor_div_nat _ _, ?_⟩
  rw [err_div _ _ hd, beq_zero_div _ _ hd]

/-- The value of a negative finite word whose magnitude is a multiple of 2^1074. -/
theorem fix_neg0 (m : ℕ) (hr : m % 2 ^ 1074 = 0) :
    round_down (-(m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) = -((m / 2 ^ 1074 : ℕ) : ℤ) ∧
      (sub_real (-(m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) (to_real (-((m / 2 ^ 1074 : ℕ) : ℤ))) == 0) =
        true := by
  rw [neg_mul, scale_1074, nat_div_exact m _ (pow_pos (by norm_num) 1074) hr]
  have e : -(((m / 2 ^ 1074 : ℕ) : ℝ)) = ((-((m / 2 ^ 1074 : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [Int.cast_neg, Int.cast_natCast]
  refine ⟨?_, ?_⟩
  · rw [e]; simp only [round_down, Int.floor_intCast]
  · rw [beq_eq_decide, decide_eq_true_iff]
    simp only [sub_real, to_real, Int.cast_neg, Int.cast_natCast, sub_self]

/-- The value of a negative finite word whose magnitude is not a multiple of 2^1074. -/
theorem fix_neg1 (m : ℕ) (hr : m % 2 ^ 1074 ≠ 0) :
    round_down (-(m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) = -((m / 2 ^ 1074 : ℕ) : ℤ) - 1 ∧
      (sub_real (-(m : ℝ) * (2 : ℝ) ^ (-1074 : ℤ))
        (to_real (-((m / 2 ^ 1074 : ℕ) : ℤ) - 1)) == 0) = false := by
  rw [neg_mul, scale_1074]
  have hd : 0 < 2 ^ 1074 := pow_pos (by norm_num) 1074
  refine ⟨floor_neg_nat_div m _ hd hr, ?_⟩
  obtain ⟨hx, h1, -⟩ := nat_div_parts m _ hd
  rw [beq_eq_decide, decide_eq_false_iff_not]
  simp only [sub_real, to_real, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_natCast, hx]
  intro h0
  linarith

theorem val_of_nan (x : BitVec 64) (h : isNaNT (ty64 x) = true) : val64 x = 0 := by
  unfold ty64 at h
  unfold val64
  split_ifs at h ⊢ <;> first | rfl | exact absurd h (by decide)

theorem trunc_fin (x : BitVec 64) (h : ex x ≠ 2047) :
    Wasm.IEEE64.truncatedInt (UInt64.ofBitVec x) =
      some (if sg x then -((Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) / 2 ^ 1074 : ℕ) : ℤ)
        else ((Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) / 2 ^ 1074 : ℕ) : ℤ)) := by
  have hf : Wasm.IEEE64.isFinite (UInt64.ofBitVec x) = true := by
    simp only [Wasm.IEEE64.isFinite, t_exp]; simpa using h
  unfold Wasm.IEEE64.truncatedInt
  rw [ite_eq_left hf, t_sign]

theorem trunc_none (x : BitVec 64) (h : ex x = 2047) :
    Wasm.IEEE64.truncatedInt (UInt64.ofBitVec x) = none := by
  have hf : Wasm.IEEE64.isFinite (UInt64.ofBitVec x) = false := by
    simp only [Wasm.IEEE64.isFinite, t_exp, h]; rfl
  unfold Wasm.IEEE64.truncatedInt
  rw [ite_eq_right (by simp [hf])]

theorem ex_of_nan (x : BitVec 64) (h : isNaNT (ty64 x) = true) : ex x = 2047 := by
  by_contra he
  unfold ty64 at h
  split_ifs at h <;> exact absurd h (by decide)

/-- FPUnpack's value of an infinity is a natural number of at least 2^64. -/
theorem inf_val_nat : ∃ n : ℕ, (2 : ℝ) ^ (1000000 : ℤ) = n ∧ 2 ^ 64 ≤ n :=
  ⟨2 ^ 1000000, by rw [zpow_ofNat, Nat.cast_pow, Nat.cast_ofNat],
    pow_le_pow_right₀ (by norm_num) (by norm_num)⟩

theorem fix_zero : round_down (0 : ℝ) = 0 ∧ (sub_real 0 (to_real 0) == (0 : ℝ)) = true := by
  simp [round_down, sub_real, to_real]

theorem fix_nat (n : ℕ) : round_down (n : ℝ) = (n : ℤ) ∧
    (sub_real (n : ℝ) (to_real (n : ℤ)) == (0 : ℝ)) = true := by
  simp [round_down, sub_real, to_real]

theorem fix_negnat (n : ℕ) : round_down (-(n : ℝ)) = -(n : ℤ) ∧
    (sub_real (-(n : ℝ)) (to_real (-(n : ℤ))) == (0 : ℝ)) = true := by
  refine ⟨?_, by simp [sub_real, to_real]⟩
  have : -(n : ℝ) = ((-(n : ℤ) : ℤ) : ℝ) := by push_cast; rfl
  rw [this]; simp only [round_down, Int.floor_intCast]

theorem intToUInt64_nat (q : ℕ) :
    (Wasm.IEEE64.intToUInt64 (q : ℤ)).toBitVec = BitVec.ofNat 64 q := by
  unfold Wasm.IEEE64.intToUInt64
  rw [ite_eq_right (by omega), Int.natAbs_natCast]
  rfl

/-- The bits of FPSR that FPToFixed sets at 64 bits under FPCR 0x02000000, unsigned with no
fraction bits and rounding toward zero: IOC for a NaN, an infinity, or a truncation outside
`[0, 2^64)`, and IXC for an inexact truncation inside it. -/
def fixMask (a : BitVec 64) : BitVec 64 :=
  match Wasm.IEEE64.truncatedInt (UInt64.ofBitVec a) with
  | none => 1#64
  | some t =>
    if t < 0 ∨ 2 ^ 64 ≤ t then 1#64
    else if Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec a) % 2 ^ 1074 = 0 then 0#64 else 0x10#64

set_option hygiene false in
/-- Closes a case of `fpToFixed_run` once the run has reached its result: the word against
Talos's, the register map against `fixMask`, and the frame. -/
macro "fix_fin" : tactic => `(tactic| (
  refine ⟨_, ok_congr ?_, ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
  · first
    | (split_ifs <;>
        first
        | (exfalso; omega)
        | decide
        | (rw [intToUInt64_nat, Int.toNat_natCast])
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
theorem fpToFixed_run (a : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPToFixed a 0 true fpcrV .FPRounding_ZERO 64).run s =
        .ok (Wasm.i64TruncSatF64U (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| fixMask a) ∧ Frame s s' := by
  subst hs
  simp only [FPToFixed]
  sail_simp [bne, h.hfi, h.hps, h.nrw, h.aa64]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp [ty_nan_or, mult_pow_zero]
  simp only [Wasm.i64TruncSatF64U, Wasm.IEEE64.truncSatI64U, t_isNaN, fixMask]
  by_cases hn : isNaNT (ty64 a) = true
  · rw [val_of_nan a hn, trunc_none a (ex_of_nan a hn)]
    simp only [hn, ↓reduceIte]
    sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, fix_zero,
      bind_satQ, satI]
    refine ⟨_, rfl, ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
    simp only [setReg_regs, bump_regs, faS_regs, hr1, upd_or _ _ (by norm_num : 0 < 64),
      (or_masks _).2.2.1]
  · have hn' : isNaNT (ty64 a) = false := by simpa using hn
    simp only [hn', Bool.false_eq_true, ↓reduceIte]
    by_cases hi : ty64 a = .FPType_Infinity
    · obtain ⟨n, hn1, hn2⟩ := inf_val_nat
      unfold val64
      obtain ⟨he, hf⟩ := ty_inf a hi
      rw [trunc_none a he, ite_eq_left he, ite_eq_left hf, hn1, t_sign]
      cases hsa : sg a
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
    · have hfin := ty_fin a hi hn'
      rw [val_fin a hfin, sv_eq, trunc_fin a hfin]
      generalize Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec a) = m
      cases hsa : sg a
      · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_natCast]
        rw [(fix_pos m).1, (fix_pos m).2]
        generalize m / 2 ^ 1074 = q
        generalize m % 2 ^ 1074 = r
        have o0 : decide ((q : ℤ) < 0) = false := decide_eq_false (by omega)
        sail_simp [o0, bind_satQ]
        by_cases hq64 : 2 ^ 64 ≤ q
        · have o1 : decide (2 ^ 64 - 1 < (q : ℤ) ∨ (q : ℤ) < 0) = true :=
            decide_eq_true (by omega)
          have s1 : satI (q : ℤ) = 2 ^ 64 - 1 := by unfold satI; rw [ite_eq_left (by omega)]
          sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
          fix_fin
        · have o1 : decide (2 ^ 64 - 1 < (q : ℤ) ∨ (q : ℤ) < 0) = false :=
            decide_eq_false (by omega)
          have s1 : satI (q : ℤ) = q := by
            unfold satI; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
          by_cases hr0 : r = 0
          · sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1,
              hr0]
            fix_fin
          · sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1,
              hr0]
            fix_fin
      · simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast]
        by_cases hr0 : m % 2 ^ 1074 = 0
        · rw [(fix_neg0 m hr0).1, (fix_neg0 m hr0).2]
          generalize m / 2 ^ 1074 = q
          generalize m % 2 ^ 1074 = r at hr0 ⊢
          sail_simp [bind_satQ]
          by_cases hq0 : q = 0
          · subst hq0
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, satI,
              Nat.cast_zero, neg_zero]
            fix_fin
          · have o1 : decide (2 ^ 64 - 1 < -(q : ℤ) ∨ -(q : ℤ) < 0) = true :=
              decide_eq_true (by omega)
            have s1 : satI (-(q : ℤ)) = 0 := by
              unfold satI; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
            fix_fin
        · rw [(fix_neg1 m hr0).1, (fix_neg1 m hr0).2]
          generalize m / 2 ^ 1074 = q
          generalize m % 2 ^ 1074 = r at hr0 ⊢
          have o0 : decide (-(q : ℤ) - 1 < 0) = true := decide_eq_true (by omega)
          sail_simp [o0, bind_satQ, sub_add_cancel]
          by_cases hq0 : q = 0
          · subst hq0
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, satI,
              Nat.cast_zero, neg_zero]
            fix_fin
          · have o1 : decide (2 ^ 64 - 1 < -(q : ℤ) ∨ -(q : ℤ) < 0) = true :=
              decide_eq_true (by omega)
            have s1 : satI (-(q : ℤ)) = 0 := by
              unfold satI; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
            sail_simp [FPProcessException, hr1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, o1, s1]
            fix_fin

/-- FPToFixed at 64 bits under FPCR 0x02000000, unsigned with no fraction bits and rounding toward
zero, returns Talos's `i64TruncSatF64U` for every word from every state that satisfies the state
hypothesis.  FPSR becomes `fpsr ||| fixMask a`, and the other registers, the memory, the tags, the
cycle count, and the output do not change. -/
theorem fpToFixed_eq_i64TruncSatF64U (a : BitVec 64) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPToFixed a 0 true fpcrV .FPRounding_ZERO 64).run s =
        .ok (Wasm.i64TruncSatF64U (UInt64.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| fixMask a) ∧ Frame s s' :=
  fpToFixed_run a h rfl

end F7
