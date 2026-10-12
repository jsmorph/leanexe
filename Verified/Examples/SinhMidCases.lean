import Verified.Examples.SinhMid

/-!
The bounds `E` of `SinhMid.mid_steps` from 1 to 22: `1.9803 u` on the path `k = 1` of `expm1`,
and `u τ + 1.9605 u` or `1.8501 u τ` from `θ2 ≈ 1.0397` on, by `SinhExpm1.near_k_pos`.
-/

namespace Verified.Examples.SinhMidCases
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords SinhCore SinhMid

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- `exp a ≤ 2.8285` below `1.5 ln 2`. -/
theorem exp_upper_θ2 (A : ℝ) (hA : A ≤ 10397206 / 10 ^ 7) : Real.exp A ≤ 28285 / 10000 := by
  obtain ⟨hl, -⟩ := ExpTight.log_two_bounds
  have h1 : Real.exp A ≤ Real.exp (3 / 2 * Real.log 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (3 / 2 * Real.log 2) * Real.exp (3 / 2 * Real.log 2) = 8 := by
    rw [← Real.exp_add, show 3 / 2 * Real.log 2 + 3 / 2 * Real.log 2 = ((3 : ℕ) : ℝ) * Real.log 2 by
      push_cast; ring, Real.exp_nat_mul, Real.exp_log two_pos]
    norm_num
  have h3 := Real.exp_pos (3 / 2 * Real.log 2)
  nlinarith

theorem exp_lower_θ2 (A : ℝ) (hA : 10397205 / 10 ^ 7 ≤ A) : 2816 / 1000 ≤ Real.exp A := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 10397205 / 10 ^ 7 by norm_num) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  have := Real.exp_le_exp.mpr hA
  linarith

/-- The check for an error `E` of `T` with `E (1 + 1/7) + 2.1 u ≤ 2.9375 u (τ + 0.63)`. -/
theorem mid_num (τ T E : ℝ) (hτ : 1718 / 1000 ≤ τ) (hT : |T - τ| ≤ E) (hET : E ≤ τ / 2 ^ 40)
    (hnum : E * (1 + 1 / 7) + 21 / 10 * u ≤ 2.9375 * u * (τ + 63 / 100)) :
    E * (1 + 1 / ((1 + T) * (1 + τ))) + 21 / 10 * u ≤ 2.9375 * u * (τ + τ / (1 + τ)) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  have hE0 : 0 ≤ E := le_trans (abs_nonneg _) hT
  have hT0 : 17 / 10 ≤ T := by
    have : τ / 2 ^ 40 ≤ τ / 2 := by gcongr; norm_num
    linarith
  have hB : 1 / ((1 + T) * (1 + τ)) ≤ 1 / 7 := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hB0 : 0 ≤ 1 / ((1 + T) * (1 + τ)) := by
    apply div_nonneg zero_le_one; nlinarith
  have hfrac : 63 / 100 ≤ τ / (1 + τ) := by rw [le_div_iff₀ (by linarith)]; linarith
  have h1 : E * (1 + 1 / ((1 + T) * (1 + τ))) ≤ E * (1 + 1 / 7) :=
    mul_le_mul_of_nonneg_left (by linarith) hE0
  have h2 : 2.9375 * u * (τ + 63 / 100) ≤ 2.9375 * u * (τ + τ / (1 + τ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by rw [hu]; positivity)
  linarith

/-- The path `k = 1`, from 1 to `θ2`. -/
theorem mid_one (x : Float) (hxf : Finite x.toBits) (hlo : 1 ≤ |value x.toBits|)
    (hhi : |value x.toBits| < value (UInt64.ofNat (1072734898 * 2 ^ 32))) :
    F64SignedRounding.WithinSteps 3 (Real.sinh |value x.toBits|)
      (0.5 * (Tanh.expm1 x.abs + Tanh.expm1 x.abs / (Tanh.expm1 x.abs + 1.0))).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  obtain ⟨haf, hav⟩ := abs_float x hxf
  obtain ⟨-, hθ1', -, hθ2', -⟩ := Expm1Near.threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  have hA22 : |value x.toBits| < 22 := by linarith
  obtain ⟨S, hn, hB2, -, -⟩ := SinhExpm1.near_one_pos x.abs haf
    (by rw [hav]; exact hθ1'.trans (by linarith)) (by rw [hav]; exact hhi)
  rw [hav] at hB2
  have htf := (nearest_finite S _ hn).1
  set A := |value x.toBits| with hAdef
  set τ := Real.exp A - 1 with hτdef
  have hτ1 : 1718 / 1000 ≤ τ := by
    have h1 : Real.exp 1 ≤ Real.exp A := Real.exp_le_exp.mpr hlo
    have h2 := Real.exp_one_gt_d9
    rw [hτdef]; norm_num at h2; linarith
  have hτ2 : τ ≤ 18285 / 10000 := by
    have := exp_upper_θ2 A (by linarith)
    rw [hτdef]; linarith
  have hS : |S - τ| ≤ 9803 / 10000 * u := by
    have : 4802 / 10000 * u + 3 * η + 2 * (1 / 2 ^ 55) ≤ 9803 / 10000 * u := by
      rw [hu, hη]; norm_num
    linarith
  obtain ⟨hS1, hS2⟩ := abs_le.mp hS
  rw [hu] at hS1 hS2
  have hr := F64NearestHalf.nearest_half S _ hn (by linarith) 1022 (by norm_num)
    (by rw [show (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 by norm_num]; linarith)
  rw [show (2 : ℝ) ^ 1022 / 2 / 2 ^ 1074 = 1 / 2 ^ 53 by norm_num] at hr
  obtain ⟨hr1, hr2⟩ := abs_le.mp hr
  have hT : |value (Tanh.expm1 x.abs).toBits - τ| ≤ 19803 / 10000 * u := by
    rw [abs_le, hu]; constructor <;> linarith
  have hE : 19803 / 10000 * u ≤ τ / 2 ^ 40 := by rw [hu]; linarith
  refine mid_steps x hlo hA22 _ htf hT hE ?_
  exact mid_num τ _ _ hτ1 hT hE (by rw [hu]; norm_num; linarith)

/-- The general path, from `θ2` to 22. -/
theorem mid_k (x : Float) (hxf : Finite x.toBits)
    (hlo : value (UInt64.ofNat (1072734898 * 2 ^ 32)) ≤ |value x.toBits|)
    (hhi : |value x.toBits| < 22) :
    F64SignedRounding.WithinSteps 3 (Real.sinh |value x.toBits|)
      (0.5 * (Tanh.expm1 x.abs + Tanh.expm1 x.abs / (Tanh.expm1 x.abs + 1.0))).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨haf, hav⟩ := abs_float x hxf
  obtain ⟨-, -, hθ2, -, -⟩ := Expm1Near.threshold_bounds
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  have hA1 : 1 ≤ |value x.toBits| := by linarith
  obtain ⟨S, htf, hS0, htS, hdisj⟩ := SinhExpm1.near_k_pos x.abs haf (by rw [hav]; exact hlo)
    (by rw [hav]; exact hhi.le)
  rw [hav] at hdisj
  set A := |value x.toBits| with hAdef
  set τ := Real.exp A - 1 with hτdef
  have hτ2 : 1816 / 1000 ≤ τ := by
    have := exp_lower_θ2 A (by linarith)
    rw [hτdef]; linarith
  obtain ⟨htS1, htS2⟩ := abs_le.mp htS
  rw [hu] at htS1 htS2
  rcases hdisj with hS | ⟨h3, hS⟩
  · obtain ⟨hS1, hS2⟩ := abs_le.mp hS
    rw [hu] at hS1 hS2
    have hT : |value (Tanh.expm1 x.abs).toBits - τ| ≤ u * τ + 19605 / 10000 * u := by
      rw [abs_le, hu]; constructor <;> nlinarith
    have hE : u * τ + 19605 / 10000 * u ≤ τ / 2 ^ 40 := by rw [hu]; linarith
    refine mid_steps x hA1 hhi _ htf hT hE ?_
    exact mid_num τ _ _ (by linarith) hT hE (by rw [hu]; linarith)
  · obtain ⟨hS1, hS2⟩ := abs_le.mp hS
    rw [hu] at hS1 hS2
    have hT : |value (Tanh.expm1 x.abs).toBits - τ| ≤ 18501 / 10000 * u * τ := by
      rw [abs_le, hu]; constructor <;> nlinarith
    have hE : 18501 / 10000 * u * τ ≤ τ / 2 ^ 40 := by rw [hu]; linarith
    refine mid_steps x hA1 hhi _ htf hT hE ?_
    exact mid_num τ _ _ (by linarith) hT hE (by rw [hu]; linarith)

/-- `sinh` from 1 to 22 for positive results. -/
theorem sinh_mid_pos (x : Float) (hxf : Finite x.toBits) (hlo : 1 ≤ |value x.toBits|)
    (hhi : |value x.toBits| < 22) :
    F64SignedRounding.WithinSteps 3 (Real.sinh |value x.toBits|)
      (0.5 * (Tanh.expm1 x.abs + Tanh.expm1 x.abs / (Tanh.expm1 x.abs + 1.0))).toBits := by
  by_cases h2 : |value x.toBits| < value (UInt64.ofNat (1072734898 * 2 ^ 32))
  · exact mid_one x hxf hlo h2
  · exact mid_k x hxf (le_of_not_gt h2) hhi

#print axioms mid_num
#print axioms mid_one
#print axioms mid_k
#print axioms sinh_mid_pos

end Verified.Examples.SinhMidCases
