import Library.Numerics.Float64.Tanh.TanhLarge

/-!
`Tanh.tanh` lies within three steps of `tanh x` on every finite input.  The ranges reach: one
step below `2 ^ -28` (the result is `x`, within `4/3 abs(x) ^ 3` of `tanh x`), three steps on
`[2 ^ -28, 1)` (`TanhSmall`), one step on `[1, 22)` (`TanhLarge`), and one step from 22 on (the
result is 1).
-/

namespace Library.Numerics.Float64.Tanh.TanhTheorem
open CodeLib.IEEE64 LeanExe.ProofKit Expm1Branches Expm1Theorem TanhBranches TanhWords

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem expCoeffs_four : TaylorRemainder.expCoeffs 4 = [1, 1, 1 / 2, 1 / 6] := by
  decide +kernel

/-- `abs(tanh a - a) ≤ 4/3 a ^ 3` for `0 ≤ a ≤ 2 ^ -28`. -/
theorem tanh_cubic (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1 / 2 ^ 28) :
    |a - Real.tanh a| ≤ 4 / 3 * a ^ 3 := by
  set x := 2 * a with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 ^ 27 := by rw [hx]; linarith
  have h := TaylorRemainder.exp_remainder (-x) (by rw [abs_neg, abs_of_nonneg hx0]; linarith) 4
    (by norm_num)
  rw [expCoeffs_four] at h
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at h
  norm_num [Nat.factorial] at h
  rw [abs_of_nonneg hx0] at h
  set E := Real.exp (-x)
  have hE0 := Real.exp_pos (-x)
  have hb := abs_le.mp h
  have hE' : Real.exp (-(2 * a)) = E := rfl
  rw [show Real.tanh a = (1 - E) / (1 + E) by
    rw [tanh_small_form, hE', show (2 : ℝ) - (1 - E) = 1 + E by ring]]
  have hden : 0 < 1 + E := by linarith
  have hx4 : x ^ 4 ≤ x ^ 3 * (1 / 2 ^ 27) := by
    rw [pow_succ]; exact mul_le_mul_of_nonneg_left hx1 (by positivity)
  have hx3 : 0 ≤ x ^ 3 := by positivity
  rw [show a - (1 - E) / (1 + E) = (a * (1 + E) - (1 - E)) / (1 + E) by field_simp, abs_div,
    abs_of_pos hden, div_le_iff₀ hden]
  have ha3 : 4 / 3 * a ^ 3 = x ^ 3 / 6 := by rw [hx]; ring
  rw [ha3]
  have hexp : a * (1 + E) - (1 - E) = x ^ 3 / 12 - x ^ 4 / 12 + (1 + x / 2) *
      (E - (1 - x + x ^ 2 / 2 - x ^ 3 / 6)) := by
    rw [hx]; ring
  rw [hexp]
  have hρ : |E - (1 - x + x ^ 2 / 2 - x ^ 3 / 6)| ≤ x ^ 4 * (5 / 96) := by
    rw [abs_le]; constructor <;> nlinarith
  have hρb := abs_le.mp hρ
  have hEge : 1 / 2 ≤ E := by nlinarith
  rw [abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hρb.2 (by positivity : (0 : ℝ) ≤ 1 + x / 2),
    mul_le_mul_of_nonneg_left hρb.1 (by positivity : (0 : ℝ) ≤ 1 + x / 2)]

/-- A nearest word `c` of `W` in `[0, 2 ^ -28)` against `y` within `4/3 W ^ 3`. -/
theorem tiny_core (W : ℝ) (c : UInt64) (hc : F64NearestNonnegative.Nearest W c) (y : ℝ)
    (hW0 : 0 ≤ W) (hW : W < 1 / 2 ^ 28) (hd : |W - y| ≤ 4 / 3 * W ^ 3) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hsq : W ^ 3 ≤ (1 / 2 ^ 56) * W := by
    have h2 : W ^ 2 ≤ (1 / 2 ^ 28) ^ 2 := pow_le_pow_left₀ hW0 hW.le 2
    have : W ^ 3 = W ^ 2 * W := by ring
    rw [this]
    have h3 : ((1 : ℝ) / 2 ^ 28) ^ 2 = 1 / 2 ^ 56 := by norm_num
    rw [h3] at h2
    exact mul_le_mul_of_nonneg_right h2 hW0
  have hdb := abs_le.mp hd
  have hy0 : 0 ≤ y := by nlinarith
  have hth : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
    unfold F64PositiveRounding.overflowThreshold; norm_num
  rcases lt_or_ge W (1 / 2 ^ 400) with hs | hl
  · refine F64NearestSteps.within_of_tiny y W c hy0 (by nlinarith) hc ?_
    have h1 : W ^ 3 ≤ (1 / 2 ^ 400) ^ 3 := pow_le_pow_left₀ hW0 hs.le 3
    have h2 : 4 / 3 * ((1 : ℝ) / 2 ^ 400) ^ 3 < 1 / 2 ^ 1074 := by norm_num
    linarith
  · have hyl : (1 - 1 / 2 ^ 54) * W ≤ y := by nlinarith
    refine F64NearestRelative.within_rel_of 1 le_rfl (by norm_num) y W c ?_ ?_ hc ?_
    · have : (1 : ℝ) / 2 ^ 1021 ≤ (1 - 1 / 2 ^ 54) * (1 / 2 ^ 400) := by norm_num
      have := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2 ^ 54)
      linarith
    · have : (1 : ℝ) / 2 ^ 28 < 2 ^ 1022 := by norm_num
      nlinarith
    · rw [hu]
      push_cast
      nlinarith

/-- The tiny range: `x` itself, for `abs(x) < 2 ^ -28`. -/
theorem tiny_within (w : UInt64) (hwf : Finite w) (hx : |value w| < 1 / 2 ^ 28) :
    F64SignedRounding.WithinSteps 1 (Real.tanh (value w)) w := by
  rcases lt_trichotomy (value w) 0 with hneg | hz | hpos
  · obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value w hwf
    have hns : Wasm.IEEE64.sign (Wasm.IEEE64.negate w) = false :=
      TanhSmall.sign_of_pos _ (by rw [hnv]; linarith)
    have hc := Expm1PathsEdge.nearest_self _ (F64Magnitude.lt_limit_of_finite _ hnf hns)
    rw [abs_of_neg hneg] at hx
    have h := tiny_core _ _ hc (Real.tanh (-value w)) (by rw [hnv]; linarith)
      (by rw [hnv]; exact hx) (by rw [hnv]; exact tanh_cubic _ (by linarith) hx.le)
    rw [Real.tanh_neg] at h
    have h' := (F64SignedRounding.within_negate 1 _ _).mpr h
    rwa [neg_neg, F64RelativeStep.negate_negate] at h'
  · have hm : Wasm.IEEE64.scaledMagnitude w = 0 := by
      have h := Expm1PathsEdge.abs_value w
      rw [hz, abs_zero] at h
      have : (Wasm.IEEE64.scaledMagnitude w : ℝ) = 0 := by
        have h74 : (0 : ℝ) < 2 ^ 1074 := by positivity
        field_simp at h
        linarith
      exact_mod_cast this
    rw [hz, Real.tanh_zero, F64Convert.zero_encoding _ hm]
    cases Wasm.IEEE64.sign w
    · exact Expm1PathsEdge.zero_within _ (Or.inl (by decide +kernel))
    · exact Expm1PathsEdge.zero_within _ (Or.inr (by decide +kernel))
  · have hs := TanhSmall.sign_of_pos w hpos
    have hc := Expm1PathsEdge.nearest_self _ (F64Magnitude.lt_limit_of_finite _ hwf hs)
    rw [abs_of_pos hpos] at hx
    exact tiny_core _ _ hc _ hpos.le hx (tanh_cubic _ hpos.le hx.le)

/-- From 22 on: the word of 1. -/
theorem huge_within (a : ℝ) (ha : 22 ≤ a) :
    F64SignedRounding.WithinSteps 1 (Real.tanh a) Expm1Words.one := by
  obtain ⟨-, -, -, -, -, -⟩ := exp_bounds
  have e5 := exp_taylor 1 (by norm_num)
  rw [abs_le] at e5
  norm_num at e5
  have he1 : (2718 / 1000 : ℝ) ≤ Real.exp 1 := by linarith [e5.1]
  have hT : (2 : ℝ) ^ 54 ≤ Real.exp (2 * a) := by
    have h1 : Real.exp 44 ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp 44 = Real.exp 1 ^ 44 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2718 / 1000 : ℝ) ^ 44 ≤ Real.exp 1 ^ 44 := pow_le_pow_left₀ (by norm_num) he1 44
    have h4 : (2 : ℝ) ^ 54 ≤ (2718 / 1000) ^ 44 := by norm_num
    linarith
  rw [tanh_large_form]
  have hone : value Expm1Words.one = 1 := Expm1KernelInner.const_values.1
  have hc : F64NearestNonnegative.Nearest 1 Expm1Words.one := by
    have h := Expm1PathsEdge.nearest_self Expm1Words.one
      (by unfold Expm1Words.one F64NearestNonnegative.limit; decide)
    rwa [hone] at h
  have hpos : (0 : ℝ) < Real.exp (2 * a) - 1 + 2 := by
    have := Real.exp_pos (2 * a); linarith
  have hsmall : 2 / (Real.exp (2 * a) - 1 + 2) < 2 / 2 ^ 54 :=
    div_lt_div_of_pos_left (by norm_num) (by positivity) (by linarith)
  have hq0 : 0 < 2 / (Real.exp (2 * a) - 1 + 2) := by positivity
  refine F64NearestSteps.within_of_interior _ 1 _ 1022 (by norm_num) (by norm_num) ?_ ?_ hc ?_
  · have h : ((2 : ℝ) ^ (1022 + 51) + 2 * 2 ^ (1022 - 1)) / 2 ^ 1074 = 1 / 2 + 1 / 2 ^ 52 := by
      norm_num
    rw [h]
    have : (2 : ℝ) / 2 ^ 54 ≤ 1 / 2 - 1 / 2 ^ 52 := by norm_num
    linarith
  · have : (1 : ℝ) < F64PositiveRounding.overflowThreshold := by
      unfold F64PositiveRounding.overflowThreshold; norm_num
    linarith
  · rw [show (1 : ℝ) - (1 - 2 / (Real.exp (2 * a) - 1 + 2)) = 2 / (Real.exp (2 * a) - 1 + 2) by
      ring, abs_of_pos hq0]
    have h : (2 : ℝ) ^ (1022 - 1) / 2 ^ 1074 = 1 / 2 ^ 53 := by norm_num
    rw [h]
    have : (2 : ℝ) / 2 ^ 54 = 1 / 2 ^ 53 := by norm_num
    linarith

theorem within_mono (k n : Nat) (hkn : k ≤ n) (y : ℝ) (w : UInt64)
    (h : F64SignedRounding.WithinSteps k y w) : F64SignedRounding.WithinSteps n y w := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, h2.trans ?_⟩
  exact_mod_cast hkn

theorem two_bits : (2.0 : Float).toBits = Expm1Words.two := rfl
theorem one_bits : (1.0 : Float).toBits = Expm1Words.one := rfl
theorem negTwo_bits : (-2.0 : Float).toBits = Expm1Words.negTwo := by
  rw [F64Bits.toBits_neg, two_bits]; decide +kernel

/-- `huge + x > 1` for a finite `x` below 1 in magnitude. -/
theorem huge_add_gt (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| < 1) :
    Float.ofBits 9094988921128908188 + x > 1.0 := by
  have hb : (Float.ofBits 9094988921128908188).toBits = 9094988921128908188 := by
    rw [F64Bits.toBits_ofBits]; decide +kernel
  have hhf : Finite (9094988921128908188 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hh := word_ge (10 ^ 299) (9094988921128908188 : UInt64) (by decide +kernel)
  have hh1 := word_le (10 ^ 301) (9094988921128908188 : UInt64) (by decide +kernel)
  push_cast at hh hh1
  have hxb := abs_lt.mp hx
  have hs : |value 9094988921128908188 + value x.toBits| < 2 ^ 1023 := by
    rw [abs_lt]; constructor <;> nlinarith [show (10 : ℝ) ^ 302 < 2 ^ 1023 by norm_num]
  have ha := F64AddBounds.add_real_relative _ _ hhf hxf hs
  rw [gt_iff_lt, F64Bits.lt_iff, F64Bits.toBits_add, hb, one_bits,
    Expm1FormsOne.lt_value _ _ Expm1KernelInner.const_finite.1 ha.1, decide_eq_true_iff,
    Expm1KernelInner.const_values.1]
  have hab := abs_le.mp ha.2
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [hu] at hab
  have : (0 : ℝ) < value 9094988921128908188 + value x.toBits := by nlinarith
  rw [abs_of_pos this] at hab
  nlinarith

#print axioms tanh_cubic
#print axioms tiny_within
#print axioms huge_within
#print axioms huge_add_gt

end Library.Numerics.Float64.Tanh.TanhTheorem
