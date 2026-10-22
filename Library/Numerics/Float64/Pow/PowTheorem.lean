import Library.Numerics.Float64.Pow.PowSpecial

/-!
The accuracy theorem of `Pow.pow`: for finite `x` and `y` with a real value of `x ^ y`, the
result lies within one representable step of the nearest-even reference of
`Real.rpow (value x) (value y)`.  The real value exists for `x > 0`, for `x < 0` and an integer
`y = n`, where `Real.rpow x n = x ^ n = (-1) ^ n |x| ^ n` as C99 Annex F gives it, and for
`x = ±0` and `y ≥ 0`, where it is 0 for `y > 0` and 1 for `y = 0`.  Overflow and underflow are
included: the reference of a value from the overflow threshold on is positive infinity.
-/

namespace Library.Numerics.Float64.Pow.PowTheorem
open CodeLib.IEEE64 LeanExe.ProofKit F64Magnitude PowSignRel PowNegBase PowSpecial

set_option exponentiation.threshold 4096

/-- For `x < 0` and an integer `n`, `Real.rpow x n = (-1) ^ n |x| ^ n`. -/
theorem neg_rpow (x : ℝ) (hx : x < 0) (n : Int) :
    x ^ (n : ℝ) = (-1 : ℝ) ^ n * |x| ^ (n : ℝ) := by
  rw [Real.rpow_intCast, Real.rpow_intCast, abs_of_neg hx, ← mul_zpow]
  congr 1
  ring

theorem zero_ref : F64SignedRounding.WithinSteps 1 0 0 := by
  have hbnd : value (UInt64.ofNat (2 * 2 ^ 52)) = (2 : ℝ) ^ (-1021 : Int) :=
    F64NearestBinade.boundary_power 2 (-1021) (by norm_num) (by norm_num) (by norm_num)
  have hs := F64FullStep.one_step_binades 0 0 0 2 (by norm_num) (by norm_num)
    (by rw [value_zero_boundary]) (fun _ => by rw [hbnd]; positivity)
    (by decide) (by rw [value_zero_boundary, value_zero])
    (by rw [hbnd, value_zero]; positivity) (by
      rw [value_zero, sub_zero, abs_zero]
      positivity)
  exact F64SignedRounding.within_of_nonneg 1 0 le_rfl 0 (by decide) hs.1 hs.2

theorem zero_word_within (w : UInt64) (h : w = 0 ∨ w = 0x8000000000000000) :
    F64SignedRounding.WithinSteps 1 0 w := by
  rcases h with rfl | rfl
  · exact zero_ref
  · have h := PowNegate.within_negrel 1 0 _ _
      (PowNegate.zero_word_rel _ _ (Or.inr rfl) (Or.inl rfl)) zero_ref
    simpa using h

theorem mag_of_value_zero (w : UInt64) (h : value w = 0) :
    Wasm.IEEE64.scaledMagnitude w = 0 := by
  rw [value] at h
  have hs : (Wasm.IEEE64.scaledValue w : ℝ) = 0 := by
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h (by positivity)
  have hs' : Wasm.IEEE64.scaledValue w = 0 := by exact_mod_cast hs
  rw [← natAbs_scaledValue, hs']
  rfl

theorem two_mul_of_low (w : UInt64) (h : w.toNat % 2 ^ 63 = 0) : 2 * w = 0 := by
  apply UInt64.toNat_inj.mp
  rw [two_mul_toNat, h]
  rfl

theorem zero_signaling (x : Float) (hx : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    Pow.issignaling x = false := by
  unfold Pow.issignaling
  rcases hx with h | h <;> rw [h] <;> decide

/-- The accuracy of `Pow.pow` against `Real.rpow`. -/
theorem pow_within (x y : Float) (hxf : Finite x.toBits) (hyf : Finite y.toBits)
    (hreal : 0 < value x.toBits ∨ (value x.toBits < 0 ∧ ∃ n : Int, value y.toBits = n) ∨
      (value x.toBits = 0 ∧ 0 ≤ value y.toBits)) :
    F64SignedRounding.WithinSteps 1 (value x.toBits ^ value y.toBits) (Pow.pow x y).toBits := by
  rcases hreal with hx | ⟨hx, n, hn⟩ | ⟨hx, hy⟩
  · exact PowTheoremPos.pow_pos_within x y hxf hx hyf
  · exact pow_neg_within x y hxf hx hyf n hn
  · have hx0 : x.toBits = 0 ∨ x.toBits = 0x8000000000000000 :=
      two_mul_zero _ (two_mul_of_low _ ((mag_zero _).mp (mag_of_value_zero _ hx)))
    rw [hx]
    rcases hy.lt_or_eq with hy | hy
    · have hy0 : 2 * y.toBits ≠ 0 := by
        intro h
        have := PowExpSign.value_mag_zero _ ((mag_zero _).mpr (low_zero _ h))
        linarith
      have hsy : Wasm.IEEE64.sign y.toBits = false := PowExpPaths.sign_of_pos _ hy
      rw [zero_base x y hx0 hyf hy0, hsy, ite_eq_right Bool.false_ne_true,
        Real.zero_rpow hy.ne']
      apply zero_word_within
      split_ifs <;> decide
    · have hy0 : 2 * y.toBits = 0 :=
        two_mul_of_low _ ((mag_zero _).mp (mag_of_value_zero _ hy.symm))
      have honef : Finite (0x3FF0000000000000 : UInt64) := by
        unfold CodeLib.IEEE64.Finite
        decide
      rw [zero_exp_one x y hy0 (zero_signaling x hx0), ← hy, Real.rpow_zero]
      exact PowPositive.exact_within _ honef 1 PowPositive.one_word_value (by norm_num)

#print axioms neg_rpow
#print axioms zero_ref
#print axioms zero_word_within
#print axioms pow_within

end Library.Numerics.Float64.Pow.PowTheorem
