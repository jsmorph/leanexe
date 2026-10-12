import Verified.Examples.TanhWords

/-!
The branch `2 ^ -28 ≤ abs(x) < 1` of fdlibm's `tanh`, which returns `-t / (t + 2)` with
`t = expm1(-2 abs(x))`, within three steps of `tanh abs(x)`.  With `P = 1 - exp(-2 abs(x))`,
`W` the value of `-t`, and `D` the value of `t + 2`, the exact quotient `W / D` differs from
`tanh abs(x) = P / (2 - P)` by `(2 (W - P) - P (D - 2 + W)) / (D (2 - P))`.  `small_core` turns a
bound `E` on `abs(W - P)` into three steps when `2 E + P u ≤ (47/16) u P (2 - P - 1/1000)`, and
the three ranges of the `expm1` paths supply `E`.
-/

namespace Verified.Examples.TanhSmall
open CodeLib.IEEE64 LeanExe.ProofKit TanhWords

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem sign_of_pos (w : UInt64) (h : 0 < value w) : Wasm.IEEE64.sign w = false := by
  have hm := Expm1Theorem.magnitude_pos w (by rw [abs_of_pos h]; exact h)
  have hs := F64Magnitude.sign_value w hm
  cases hsg : Wasm.IEEE64.sign w
  · rfl
  · rw [hsg] at hs; exact absurd (hs.mp rfl) (by linarith)

/-- Three steps for the quotient from a bound `E` on the error of `-t`. -/
theorem small_core (w : UInt64) (hwf : Finite w) (P E : ℝ) (hP0 : 1 / 2 ^ 30 ≤ P)
    (hP1 : P ≤ 87 / 100) (hE : |value w - P| ≤ E) (hEP4 : E ≤ P / 4)
    (hEu : E + u ≤ 1 / 1000)
    (hEP : 2 * E + P * u ≤ 47 / 16 * u * (P * (2 - P - 1 / 1000))) :
    F64SignedRounding.WithinSteps 3 (P / (2 - P))
      (Wasm.IEEE64.div w (Wasm.IEEE64.add (Wasm.IEEE64.negate w) Expm1Words.two)) := by
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hu0 : (0 : ℝ) < u := by rw [hu]; positivity
  have hEb := abs_le.mp hE
  set W := value w
  have hW0 : 0 < W := by
    have : (0 : ℝ) < 1 / 2 ^ 30 := by positivity
    linarith
  have hW1 : W < 11 / 10 := by linarith
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value w hwf
  have htwo : value Expm1Words.two = 2 := Expm1KernelInner.const_values.2.2.1
  have h2f : Finite Expm1Words.two := Expm1KernelInner.const_finite.2.2.1
  have hg : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
  have hds := F64NearestSum.add_half_spacing _ _ hnf h2f 1022 (by
    rw [hnv, htwo, hg, abs_lt]; constructor <;> linarith) (by norm_num)
  set d := Wasm.IEEE64.add (Wasm.IEEE64.negate w) Expm1Words.two
  have hdu : |value d - (2 - W)| ≤ u := by
    have h := hds.2
    rw [hnv, htwo] at h
    have : (2 : ℝ) ^ 1022 / 2 / 2 ^ 1074 = u := by rw [hu]; norm_num
    rw [this] at h
    rwa [show -W + 2 = 2 - W by ring] at h
  set D := value d
  have hdb := abs_le.mp hdu
  have hD0 : 0 < D := by linarith
  have hDlo : 2 - P - 1 / 1000 ≤ D := by linarith
  have hP2 : 0 < 2 - P := by linarith
  have hsw := sign_of_pos w hW0
  have hsd := sign_of_pos d hD0
  have hq0 : 1 / 2 ^ 1022 ≤ W / D := by
    rw [le_div_iff₀ hD0]
    have h1 : W ≥ 3 / 4 * (1 / 2 ^ 30) := by linarith
    have h2 : (1 : ℝ) / 2 ^ 1022 * D ≤ 1 / 2 ^ 1022 * 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    have h3 : (1 : ℝ) / 2 ^ 1022 * 3 ≤ 3 / 4 * (1 / 2 ^ 30) := by norm_num
    linarith
  have hq1 : W / D < 2 ^ 1022 := by
    rw [div_lt_iff₀ hD0]
    have : (1 : ℝ) ≤ 2 ^ 1022 := one_le_pow₀ (by norm_num)
    nlinarith
  have hc := F64NearestDiv.div_nearest w d hwf hds.1 hsw hsd hq0 hq1
  have hY0 : 0 < P / (2 - P) := by positivity
  refine F64NearestRelative.within_rel_of 3 (by norm_num) (by norm_num) (P / (2 - P)) (W / D) _
    ?_ ?_ hc ?_
  · rw [le_div_iff₀ hP2]
    have h1 : (1 : ℝ) / 2 ^ 1021 * (2 - P) ≤ 1 / 2 ^ 1021 * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (1 : ℝ) / 2 ^ 1021 * 2 ≤ 1 / 2 ^ 30 := by norm_num
    linarith
  · rw [div_lt_iff₀ hP2]
    have : (1 : ℝ) ≤ 2 ^ 1022 := one_le_pow₀ (by norm_num)
    nlinarith
  · have key : W / D - P / (2 - P) = (2 * (W - P) - P * (D - (2 - W))) / (D * (2 - P)) := by
      field_simp
      ring
    rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < D * (2 - P)),
      div_le_iff₀ (by positivity)]
    have h1 : |2 * (W - P) - P * (D - (2 - W))| ≤ 2 * E + P * u := by
      calc |2 * (W - P) - P * (D - (2 - W))| ≤ |2 * (W - P)| + |P * (D - (2 - W))| :=
            abs_sub _ _
        _ = 2 * |W - P| + P * |D - (2 - W)| := by
            rw [abs_mul, abs_mul, abs_two, abs_of_pos (by linarith : (0 : ℝ) < P)]
        _ ≤ 2 * E + P * u := by
            have := mul_le_mul_of_nonneg_left hdu (by linarith : (0 : ℝ) ≤ P)
            linarith
    have h2 : 47 / 16 * u * (P * (2 - P - 1 / 1000)) ≤ 47 / 16 * u * (P * D) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hDlo (by linarith)
    have h3 : ((3 : ℕ) - 1 / 16 : ℝ) * u * (P / (2 - P)) * (D * (2 - P)) =
        47 / 16 * u * (P * D) := by
      push_cast
      field_simp
      ring
    rw [h3]
    linarith

/-- The range without reduction, `2 abs(x) ≤ 0.3466`. -/
theorem small_a (A : ℝ) (w : UInt64) (hwf : Finite w) (S : ℝ) (hA : 1 / 2 ^ 28 ≤ A)
    (hA' : 2 * A ≤ 3466 / 10000) (hw1 : |value w - S| ≤ u * S)
    (hS : |S - (1 - Real.exp (-(2 * A)))| ≤ 56 / 100 * u * (2 * A) + 16 * η) :
    F64SignedRounding.WithinSteps 3 (Real.tanh A)
      (Wasm.IEEE64.div w (Wasm.IEEE64.add (Wasm.IEEE64.negate w) Expm1Words.two)) := by
  rw [tanh_small_form]
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hη : η ≤ 1 / 2 ^ 1000 := by rw [Expm1KernelInner.eta_value]; norm_num
  have hη0 : (0 : ℝ) ≤ η := by rw [Expm1KernelInner.eta_value]; positivity
  set P := 1 - Real.exp (-(2 * A))
  have he2 := Expm1KernelOuter.exp_second (-(2 * A)) (by
    rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have heb := abs_le.mp he2
  have hlow := Real.add_one_le_exp (-(2 * A))
  have hPlo : 74 / 100 * (2 * A) ≤ P := by nlinarith
  have hPhi : P ≤ 2 * A := by linarith
  have hSb := abs_le.mp hS
  have hw1b := abs_le.mp hw1
  rw [hu] at hSb hw1b hw1
  refine small_core w hwf P (1 / 2 ^ 53 * S + (56 / 100 * (1 / 2 ^ 53) * (2 * A) + 16 * η))
    ?_ ?_ ?_ ?_ ?_ ?_
  · have : (1 : ℝ) / 2 ^ 30 ≤ 74 / 100 * (2 * (1 / 2 ^ 28)) := by norm_num
    linarith
  · linarith
  · rw [abs_le]; constructor <;> linarith
  · have : 16 * η ≤ 1 / 2 ^ 990 := by linarith
    have h2 : (1 : ℝ) / 2 ^ 990 ≤ 1 / 2 ^ 40 * (1 / 2 ^ 28) := by norm_num
    nlinarith
  · rw [hu]
    have : 16 * η ≤ 1 / 2 ^ 990 := by linarith
    nlinarith
  · rw [hu]
    have : 16 * η ≤ 1 / 2 ^ 990 := by linarith
    have h2 : (1 : ℝ) / 2 ^ 990 ≤ 1 / 2 ^ 60 * (74 / 100 * (2 * (1 / 2 ^ 28))) := by norm_num
    have hP0 : (0 : ℝ) ≤ P := by linarith
    nlinarith [mul_nonneg hP0 (by linarith : (0 : ℝ) ≤ 3466 / 10000 - P)]

/-- The range of `k = -1`, `P` in `[0.29, 0.65]`. -/
theorem small_b (A : ℝ) (w : UInt64) (hwf : Finite w) (S : ℝ)
    (hP0 : 29 / 100 ≤ 1 - Real.exp (-(2 * A))) (hP1 : 1 - Real.exp (-(2 * A)) ≤ 65 / 100)
    (hw1 : |value w - S| ≤ u * S)
    (hS : |S - (1 - Real.exp (-(2 * A)))| ≤ 2451 / 10000 * u) :
    F64SignedRounding.WithinSteps 3 (Real.tanh A)
      (Wasm.IEEE64.div w (Wasm.IEEE64.add (Wasm.IEEE64.negate w) Expm1Words.two)) := by
  rw [tanh_small_form]
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  set P := 1 - Real.exp (-(2 * A))
  have hSb := abs_le.mp hS
  have hw1b := abs_le.mp hw1
  rw [hu] at hSb hw1b hw1
  refine small_core w hwf P (1 / 2 ^ 53 * S + 2451 / 10000 * (1 / 2 ^ 53)) (by linarith)
    (by linarith) ?_ ?_ ?_ ?_
  · rw [abs_le]; constructor <;> linarith
  · linarith
  · rw [hu]; linarith
  · rw [hu]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ P - 29 / 100)
      (by linarith : (0 : ℝ) ≤ 65 / 100 - P)]

/-- The range of `k ≤ -2`, `P` in `[0.64, 0.87]`. -/
theorem small_c (A : ℝ) (w : UInt64) (hwf : Finite w) (S : ℝ)
    (hP0 : 64 / 100 ≤ 1 - Real.exp (-(2 * A))) (hP1 : 1 - Real.exp (-(2 * A)) ≤ 87 / 100)
    (hw2 : |value w - S| ≤ u / 2)
    (hS : |S - (1 - Real.exp (-(2 * A)))| ≤ 3726 / 10000 * u) :
    F64SignedRounding.WithinSteps 3 (Real.tanh A)
      (Wasm.IEEE64.div w (Wasm.IEEE64.add (Wasm.IEEE64.negate w) Expm1Words.two)) := by
  rw [tanh_small_form]
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  set P := 1 - Real.exp (-(2 * A))
  have hSb := abs_le.mp hS
  have hw2b := abs_le.mp hw2
  rw [hu] at hSb hw2b
  refine small_core w hwf P (1 / 2 ^ 53 / 2 + 3726 / 10000 * (1 / 2 ^ 53)) (by linarith) hP1
    ?_ ?_ ?_ ?_
  · rw [abs_le]; constructor <;> linarith
  · linarith
  · rw [hu]; norm_num
  · rw [hu]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ P - 64 / 100)
      (by linarith : (0 : ℝ) ≤ 87 / 100 - P)]

#print axioms small_core
#print axioms small_a
#print axioms small_b
#print axioms small_c

end Verified.Examples.TanhSmall
