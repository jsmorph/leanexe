import Verified.Examples.Exp10Constants
import Verified.Examples.Exp2Evaluation

/-!
The polynomial of `Exp2.exp10Core`, `C0 r + C1 r ^ 2 + C2 r ^ 3 + C3 r ^ 4 + C4 r ^ 5`, against
`10 ^ r - 1 = exp (r log 10) - 1` on `|r| ≤ 1/850`, and its evaluation on words in the order of
the code: `t + (C0 + r C1 + r ^ 2 ((C2 + r C3) + r ^ 2 C4)) r`.  The polynomial's error is at most
`2 ^ -57` and the rounding's `2 ^ -58`.
-/

namespace Verified.Examples.Exp10Evaluation
open CodeLib.IEEE64
open LeanExe.ProofKit F64ErrorTrack Exp10Constants

set_option exponentiation.threshold 4096

/-- The polynomial with the coefficients' values. -/
noncomputable def polynomial (r : ℝ) : ℝ :=
  value e1 * r + value e2 * r ^ 2 + value e3 * r ^ 3 + value e4 * r ^ 4 + value e5 * r ^ 5

theorem polynomial_error (r : ℝ) (hr : |r| ≤ 1 / 850) :
    |Real.exp (r * Real.log 10) - 1 - polynomial r| ≤ 1 / 2 ^ 57 := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := coefficient_errors
  obtain ⟨hl, hh⟩ := log_ten_enclosure
  have hb := checked_reduction
  have hl' : (23 / 10 : ℝ) ≤ Real.log 10 := le_trans (by
    have := Exp2Approximation.cast_le hb.2.2.2.2.2.1
    push_cast at this
    exact this) hl
  have hh' : Real.log 10 ≤ 233 / 100 := hh.trans (by
    have := Exp2Approximation.cast_le hb.2.2.2.2.2.2.1
    push_cast at this
    exact this)
  set L := Real.log 10
  have hL0 : 0 ≤ L := by linarith
  set y := r * L
  have hy : |y| ≤ 1 / 364 := by
    rw [abs_mul, abs_of_nonneg hL0]
    calc
      _ ≤ 1 / 850 * (233 / 100) := mul_le_mul hr hh' hL0 (by norm_num)
      _ ≤ 1 / 364 := by norm_num
  have hb6 : |Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)| ≤
      |y| ^ 6 * (7 / 4320) := by
    have h := Real.exp_bound (x := y) (hy.trans (by norm_num)) (n := 6) (by norm_num)
    have hs : ∑ i ∈ Finset.range 6, y ^ i / (i.factorial : ℝ) =
        1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      norm_num
    have hc : ((Nat.succ 6 : Nat) : ℝ) / ((Nat.factorial 6 : Nat) * (6 : Nat)) = 7 / 4320 := by
      norm_num [Nat.factorial]
    rw [hs, hc] at h
    exact h
  have hE : |Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)| ≤
      1 / 2 ^ 60 := by
    have hrem : |y| ^ 6 * (7 / 4320) ≤ 1 / 2 ^ 60 := by
      calc
        _ ≤ (1 / 364 : ℝ) ^ 6 * (7 / 4320) := by gcongr
        _ ≤ 1 / 2 ^ 60 := by norm_num
    exact hb6.trans hrem
  have hid : Real.exp y - 1 - polynomial r =
      (Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)) -
        ((value e1 - L) * r + (value e2 - L ^ 2 / 2) * r ^ 2 + (value e3 - L ^ 3 / 6) * r ^ 3 +
          (value e4 - L ^ 4 / 24) * r ^ 4 + (value e5 - L ^ 5 / 120) * r ^ 5) := by
    simp only [polynomial, y]
    ring
  have term (d : ℝ) (n : Nat) (δ : ℝ) (hd : |d| ≤ δ) :
      |d * r ^ n| ≤ δ * (1 / 850) ^ n := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hd (pow_le_pow_left₀ (abs_nonneg r) hr n) (by positivity)
      ((abs_nonneg d).trans hd)
  have t1 := term _ 1 _ c1
  have t2 := term _ 2 _ c2
  have t3 := term _ 3 _ c3
  have t4 := term _ 4 _ c4
  have t5 := term _ 5 _ c5
  simp only [pow_one] at t1
  rw [hid]
  calc
    _ ≤ |Real.exp y - (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120)| +
        (|(value e1 - L) * r| + |(value e2 - L ^ 2 / 2) * r ^ 2| +
          |(value e3 - L ^ 3 / 6) * r ^ 3| + |(value e4 - L ^ 4 / 24) * r ^ 4| +
          |(value e5 - L ^ 5 / 120) * r ^ 5|) := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact abs_add_le _ _
    _ ≤ 1 / 2 ^ 60 + (1 / 2 ^ 51 * (1 / 850) + 1 / 2 ^ 44 * (1 / 850) ^ 2 +
          1 / 2 ^ 30 * (1 / 850) ^ 3 + 1 / 2 ^ 21 * (1 / 850) ^ 4 +
          1 / 2 ^ 12 * (1 / 850) ^ 5) := by
      gcongr
    _ ≤ 1 / 2 ^ 57 := by norm_num

/-- The polynomial evaluation of `Exp2.exp10Core` on the residual `r` and the tail `t`. -/
def evaluation (r t : UInt64) : UInt64 :=
  let r2 := Wasm.IEEE64.mul r r
  let p := Wasm.IEEE64.add e1 (Wasm.IEEE64.mul r e2)
  let y := Wasm.IEEE64.add (Wasm.IEEE64.add e3 (Wasm.IEEE64.mul r e4)) (Wasm.IEEE64.mul r2 e5)
  Wasm.IEEE64.add t (Wasm.IEEE64.mul (Wasm.IEEE64.add p (Wasm.IEEE64.mul r2 y)) r)

theorem evaluation_error (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 850) (ht : |value t| ≤ 1 / 2 ^ 53) :
    Finite (evaluation r t) ∧ |value (evaluation r t)| ≤ 1 / 64 ∧
      |value (evaluation r t) - (value t + polynomial (value r))| ≤ 1 / 2 ^ 58 := by
  obtain ⟨f1, f2, f3, f4, f5, -, -, -⟩ := coefficient_finite
  obtain ⟨b1, b2, b3, b4, b5, -, -, -⟩ := coefficient_bounds
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hm : multiplicationUnderflowEpsilon = 1 / 2 ^ 1075 := rfl
  set R := value r
  set T := value t
  have hR := approx_self r hrf
  have hT := approx_self t htf
  have hC1 := approx_self e1 f1
  have hC2 := approx_self e2 f2
  have hC3 := approx_self e3 f3
  have hC4 := approx_self e4 f4
  have hC5 := approx_self e5 f5
  have hR2 : |R * R| ≤ 1 / 2 ^ 19 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 850 * (1 / 850) := mul_le_mul hr hr (abs_nonneg _) (by norm_num)
      _ ≤ 1 / 2 ^ 19 := by norm_num
  have ar2 := (mul_approx hR hR (1 / 850) (1 / 850) hr hr (by norm_num)).mono
    (e' := 1 / 2 ^ 71) (by rw [hu, hm]; norm_num)
  have a2 := (mul_approx hR hC2 (1 / 850) (27 / 10) hr b2 (by norm_num)).mono
    (e' := 1 / 2 ^ 61) (by rw [hu, hm]; norm_num)
  have a4 := (mul_approx hR hC4 (1 / 850) (12 / 10) hr b4 (by norm_num)).mono
    (e' := 1 / 2 ^ 62) (by rw [hu, hm]; norm_num)
  have hRC2 : |R * value e2| ≤ 27 / 8500 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 850 * (27 / 10) := mul_le_mul hr b2 (abs_nonneg _) (by norm_num)
      _ = 27 / 8500 := by norm_num
  have hRC4 : |R * value e4| ≤ 12 / 8500 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 850 * (12 / 10) := mul_le_mul hr b4 (abs_nonneg _) (by norm_num)
      _ = 12 / 8500 := by norm_num
  have p := (add_approx hC1 a2 (5 / 2) (by
      have := abs_add_le (value e1) (R * value e2)
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 51) (by rw [hu]; norm_num)
  have hP : |value e1 + R * value e2| ≤ 5 / 2 := by
    have := abs_add_le (value e1) (R * value e2)
    linarith
  have s34 := (add_approx hC3 a4 (9 / 4) (by
      have := abs_add_le (value e3) (R * value e4)
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 51) (by rw [hu]; norm_num)
  have hS34 : |value e3 + R * value e4| ≤ 211 / 100 := by
    have := abs_add_le (value e3) (R * value e4)
    linarith
  have b5' := (mul_approx ar2 hC5 (1 / 2 ^ 19) (6 / 10) hR2 b5 (by norm_num)).mono
    (e' := 1 / 2 ^ 71) (by rw [hu, hm]; norm_num)
  have hB5 : |R * R * value e5| ≤ 1 / 2 ^ 19 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 19 * (6 / 10) := mul_le_mul hR2 b5 (abs_nonneg _) (by norm_num)
      _ ≤ 1 / 2 ^ 19 := by norm_num
  have s345 := (add_approx s34 b5' (9 / 4) (by
      have := abs_add_le (value e3 + R * value e4) (R * R * value e5)
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 50) (by rw [hu]; norm_num)
  have hS345 : |value e3 + R * value e4 + R * R * value e5| ≤ 9 / 4 := by
    have := abs_add_le (value e3 + R * value e4) (R * R * value e5)
    linarith
  have m := (mul_approx ar2 s345 (1 / 2 ^ 19) (9 / 4) hR2 hS345 (by norm_num)).mono
    (e' := 1 / 2 ^ 67) (by rw [hu, hm]; norm_num)
  have hM : |R * R * (value e3 + R * value e4 + R * R * value e5)| ≤ 1 / 2 ^ 17 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 2 ^ 19 * (9 / 4) := mul_le_mul hR2 hS345 (abs_nonneg _) (by norm_num)
      _ ≤ 1 / 2 ^ 17 := by norm_num
  have s := (add_approx p m (5 / 2 + 1 / 2 ^ 16) (by
      have := abs_add_le (value e1 + R * value e2)
        (R * R * (value e3 + R * value e4 + R * R * value e5))
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 50) (by rw [hu]; norm_num)
  have hS : |value e1 + R * value e2 + R * R * (value e3 + R * value e4 + R * R * value e5)| ≤
      5 / 2 + 1 / 2 ^ 16 := by
    have := abs_add_le (value e1 + R * value e2)
      (R * R * (value e3 + R * value e4 + R * R * value e5))
    linarith
  have t1 := (mul_approx s hR (5 / 2 + 1 / 2 ^ 16) (1 / 850) hS hr (by norm_num)).mono
    (e' := 1 / 2 ^ 59) (by rw [hu, hm]; norm_num)
  have hT1 : |(value e1 + R * value e2 + R * R * (value e3 + R * value e4 + R * R * value e5)) *
      R| ≤ 1 / 256 - 1 / 2 ^ 52 := by
    rw [abs_mul]
    calc
      _ ≤ (5 / 2 + 1 / 2 ^ 16) * (1 / 850) := mul_le_mul hS hr (abs_nonneg _) (by norm_num)
      _ ≤ 1 / 256 - 1 / 2 ^ 52 := by norm_num
  have y := (add_approx hT t1 (1 / 256) (by
      have := abs_add_le T
        ((value e1 + R * value e2 + R * R * (value e3 + R * value e4 + R * R * value e5)) * R)
      have h2 : (1 : ℝ) / 2 ^ 59 ≤ 1 / 2 ^ 53 := by norm_num
      linarith) (by norm_num)).mono (e' := 1 / 2 ^ 58) (by rw [hu]; norm_num)
  have hid : T + (value e1 + R * value e2 + R * R * (value e3 + R * value e4 + R * R * value e5)) *
      R = T + polynomial R := by
    simp only [polynomial]
    ring
  have y' : Approx (evaluation r t) (T + polynomial R) (1 / 2 ^ 58) := y.congr hid
  refine ⟨y'.1, ?_, y'.2⟩
  have hY : |T + polynomial R| ≤ 1 / 256 := by
    rw [← hid]
    have := abs_add_le T
      ((value e1 + R * value e2 + R * R * (value e3 + R * value e4 + R * R * value e5)) * R)
    have h2 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 2 ^ 52 := by norm_num
    linarith
  have := y'.abs_le hY
  linarith [show (1 : ℝ) / 256 + 1 / 2 ^ 58 ≤ 1 / 64 by norm_num]

/-- The evaluation against `t + 10 ^ r - 1`. -/
theorem evaluation_exp_error (r t : UInt64) (hrf : Finite r) (htf : Finite t)
    (hr : |value r| ≤ 1 / 850) (ht : |value t| ≤ 1 / 2 ^ 53) :
    |value (evaluation r t) - (value t + Real.exp (value r * Real.log 10) - 1)| ≤
      3 / 2 ^ 58 := by
  have he := (evaluation_error r t hrf htf hr ht).2.2
  have hp := polynomial_error (value r) hr
  calc
    _ = |(value (evaluation r t) - (value t + polynomial (value r))) -
        (Real.exp (value r * Real.log 10) - 1 - polynomial (value r))| := by
      congr 1
      ring
    _ ≤ _ := abs_sub _ _
    _ ≤ 1 / 2 ^ 58 + 1 / 2 ^ 57 := add_le_add he hp
    _ = 3 / 2 ^ 58 := by norm_num

#print axioms polynomial_error
#print axioms evaluation_error
#print axioms evaluation_exp_error

end Verified.Examples.Exp10Evaluation
