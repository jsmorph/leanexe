import LeanExe.ProofKit.TaylorRemainder
import Verified.Examples.Expm1Words

/-!
The approximation error of fdlibm's `expm1` kernel in exact arithmetic.  With `P` the polynomial
`1 + Q1 z + ... + Q5 z ^ 5` of `Tanh.expm1Kernel` and `z = r ^ 2 / 2`, the kernel computes
`t = 3 - P r / 2`, `e = z (P - t) / (6 - r t)`, and `r - (r e - z)`, which `kernelValue` states
without rounding.  `kernel_approx` bounds its distance from `exp r - 1` by `2 ^ -62 |r| ^ 3` for
`|r| ≤ 0.3466`.  The proof multiplies out the denominator `6 - r t`: the numerator of the error,
with the exponential replaced by its Taylor polynomial of degree 17, is `r ^ 3` times a polynomial
of degree 26 whose magnitude `PolyBound.check` bounds by `2 ^ -60`.  Its largest value on the
interval is about `2 ^ -61.74`.
-/

namespace Verified.Examples.Expm1KernelPoly
open LeanExe.ProofKit PolyBound TaylorRemainder CodeLib.IEEE64

/-- The product of two polynomials. -/
def mulP : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a :: p, q => addP (scaleP a q) (0 :: mulP p q)

theorem eval_mulP (p q : List ℚ) (x : ℝ) : eval (mulP p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mulP]
  | cons a p ih =>
    simp only [mulP, eval_addP, eval_scaleP, eval_cons, ih, Rat.cast_zero]
    ring

/-- The coefficients of `p (c X ^ 2)`. -/
def spread (c : ℚ) : List ℚ → List ℚ
  | [] => []
  | a :: p => a :: 0 :: scaleP c (spread c p)

theorem eval_spread (c : ℚ) (p : List ℚ) (x : ℝ) :
    eval (spread c p) x = eval p (c * x ^ 2) := by
  induction p with
  | nil => simp [spread]
  | cons a p ih =>
    simp only [spread, eval_cons, eval_scaleP, ih, Rat.cast_zero]
    ring

theorem eval_of_take (p : List ℚ) (h : p.take 3 = [0, 0, 0]) (x : ℝ) :
    eval p x = x ^ 3 * eval (p.drop 3) x := by
  match p, h with
  | a :: b :: c :: q, h =>
    simp only [List.take, List.cons.injEq] at h
    obtain ⟨rfl, rfl, rfl, -⟩ := h
    simp only [eval_cons, Rat.cast_zero, List.drop]
    ring

/-- `1 + Q1 z + ... + Q5 z ^ 5`. -/
def kernelP : List ℚ :=
  [1, ratOfWord Expm1Words.Q1, ratOfWord Expm1Words.Q2, ratOfWord Expm1Words.Q3,
    ratOfWord Expm1Words.Q4, ratOfWord Expm1Words.Q5]

/-- `P (r ^ 2 / 2)` as a polynomial in `r`. -/
def kernelPr : List ℚ := spread (1 / 2) kernelP

/-- The denominator `6 - r t = 6 - 3 r + P r ^ 2 / 2`. -/
def denominator : List ℚ := addP [6, -3] (mulP kernelPr [0, 0, 1 / 2])

/-- The numerator `z (P - t) = (r ^ 2 / 2) (P (1 + r / 2) - 3)`. -/
def numerator : List ℚ := mulP [0, 0, 1 / 2] (subP (mulP kernelPr [1, 1 / 2]) [3])

/-- `(T - 1 - r - r ^ 2 / 2) (6 - r t) + r z (P - t)`, with `T` the Taylor polynomial of
degree 17 of the exponential. -/
def errorNumerator : List ℚ :=
  addP (mulP (subP (expCoeffs 18) [1, 1, 1 / 2]) denominator) (0 :: numerator)

theorem error_low : errorNumerator.take 3 = [0, 0, 0] := by
  decide +kernel

theorem error_check :
    check (errorNumerator.drop 3) (-3466 / 10000) (3466 / 10000) (1 / 2 ^ 60) 16 = true := by
  decide +kernel

theorem denominator_check :
    check (subP denominator [6]) (-3466 / 10000) (3466 / 10000) (6 / 5) 4 = true := by
  decide +kernel

/-- `P z` in real arithmetic. -/
noncomputable def polyValue (z : ℝ) : ℝ := eval kernelP z

/-- The kernel's `e` in exact arithmetic. -/
noncomputable def eValue (r : ℝ) : ℝ :=
  r ^ 2 / 2 * (polyValue (r ^ 2 / 2) - (3 - polyValue (r ^ 2 / 2) * (r / 2))) /
    (6 - r * (3 - polyValue (r ^ 2 / 2) * (r / 2)))

/-- The kernel's result `r - (r e - r ^ 2 / 2)` in exact arithmetic. -/
noncomputable def kernelValue (r : ℝ) : ℝ := r - (r * eValue r - r ^ 2 / 2)

theorem denominator_eval (r : ℝ) :
    eval denominator r = 6 - r * (3 - polyValue (r ^ 2 / 2) * (r / 2)) := by
  simp only [denominator, eval_addP, eval_mulP, kernelPr, eval_spread, polyValue, eval_cons,
    eval_nil]
  push_cast
  ring_nf

theorem numerator_eval (r : ℝ) :
    eval numerator r =
      r ^ 2 / 2 * (polyValue (r ^ 2 / 2) - (3 - polyValue (r ^ 2 / 2) * (r / 2))) := by
  simp only [numerator, eval_subP, eval_mulP, kernelPr, eval_spread, polyValue, eval_cons,
    eval_nil]
  push_cast
  ring_nf

theorem denominator_lower (r : ℝ) (hr : |r| ≤ 3466 / 10000) :
    24 / 5 ≤ 6 - r * (3 - polyValue (r ^ 2 / 2) * (r / 2)) := by
  have hb := abs_le.mp hr
  have hc := check_sound _ _ _ _ _ denominator_check r (by push_cast; linarith)
    (by push_cast; linarith)
  rw [eval_subP, denominator_eval] at hc
  have hc' : |6 - r * (3 - polyValue (r ^ 2 / 2) * (r / 2)) - 6| ≤ 6 / 5 :=
    by simpa using hc.trans (le_of_eq (by norm_num))
  have := (abs_le.mp hc').1
  linarith

/-- The kernel's approximation error in exact arithmetic. -/
theorem kernel_approx (r : ℝ) (hr : |r| ≤ 3466 / 10000) :
    |Real.exp r - 1 - kernelValue r| ≤ |r| ^ 3 / 2 ^ 62 := by
  have hb := abs_le.mp hr
  set D := 6 - r * (3 - polyValue (r ^ 2 / 2) * (r / 2)) with hD
  set N := r ^ 2 / 2 * (polyValue (r ^ 2 / 2) - (3 - polyValue (r ^ 2 / 2) * (r / 2))) with hN
  have hDl : 24 / 5 ≤ D := denominator_lower r hr
  have hDp : 0 < D := by linarith
  set T := eval (expCoeffs 18) r with hT
  have hF : eval errorNumerator r = (T - 1 - r - r ^ 2 / 2) * D + r * N := by
    simp only [errorNumerator, eval_addP, eval_mulP, eval_subP, eval_cons, eval_nil,
      denominator_eval, numerator_eval, Rat.cast_zero, Rat.cast_one]
    push_cast
    ring
  have hG := check_sound _ _ _ _ _ error_check r (by push_cast; linarith) (by push_cast; linarith)
  have hG' : |eval (errorNumerator.drop 3) r| ≤ 1 / 2 ^ 60 := hG.trans (le_of_eq (by norm_num))
  have hFr : |eval errorNumerator r| ≤ |r| ^ 3 / 2 ^ 60 := by
    rw [eval_of_take _ error_low, abs_mul, abs_pow]
    calc |r| ^ 3 * |eval (errorNumerator.drop 3) r| ≤ |r| ^ 3 * (1 / 2 ^ 60) :=
          mul_le_mul_of_nonneg_left hG' (by positivity)
      _ = |r| ^ 3 / 2 ^ 60 := by ring
  have hr1 : |r| ≤ 1 := hr.trans (by norm_num)
  have hrem := exp_remainder r hr1 18 (by norm_num)
  have hrem' : |Real.exp r - T| ≤ |r| ^ 3 / 2 ^ 70 := by
    refine hrem.trans ?_
    have h15 : |r| ^ 15 ≤ (3466 / 10000) ^ 15 := pow_le_pow_left₀ (abs_nonneg r) hr 15
    have hc : (3466 / 10000 : ℝ) ^ 15 * ((18 + 1 : ℝ) / ((Nat.factorial 18 : ℕ) * (18 : ℕ))) ≤
        1 / 2 ^ 70 := by
      norm_num [Nat.factorial]
    calc |r| ^ 18 * ((18 + 1 : ℝ) / ((Nat.factorial 18 : ℕ) * (18 : ℕ))) =
        |r| ^ 3 * (|r| ^ 15 * ((18 + 1 : ℝ) / ((Nat.factorial 18 : ℕ) * (18 : ℕ)))) := by ring
      _ ≤ |r| ^ 3 * ((3466 / 10000 : ℝ) ^ 15 *
          ((18 + 1 : ℝ) / ((Nat.factorial 18 : ℕ) * (18 : ℕ)))) := by gcongr
      _ ≤ |r| ^ 3 * (1 / 2 ^ 70) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = |r| ^ 3 / 2 ^ 70 := by ring
  have hK : Real.exp r - 1 - kernelValue r =
      ((Real.exp r - 1 - r - r ^ 2 / 2) * D + r * N) / D := by
    simp only [kernelValue, eValue, ← hD, ← hN]
    field_simp
    ring
  have hsplit : (Real.exp r - 1 - r - r ^ 2 / 2) * D + r * N =
      eval errorNumerator r + (Real.exp r - T) * D := by
    rw [hF]
    ring
  rw [hK, hsplit, abs_div, abs_of_pos hDp, div_le_iff₀ hDp]
  have hD7 : D ≤ 36 / 5 := by
    have hc := check_sound _ _ _ _ _ denominator_check r (by push_cast; linarith)
      (by push_cast; linarith)
    rw [eval_subP, denominator_eval] at hc
    have hc' : |D - 6| ≤ 6 / 5 := by simpa [hD] using hc.trans (le_of_eq (by norm_num))
    linarith [(abs_le.mp hc').2]
  calc |eval errorNumerator r + (Real.exp r - T) * D| ≤
      |eval errorNumerator r| + |(Real.exp r - T) * D| := abs_add_le _ _
    _ = |eval errorNumerator r| + |Real.exp r - T| * D := by rw [abs_mul, abs_of_pos hDp]
    _ ≤ |r| ^ 3 / 2 ^ 60 + |r| ^ 3 / 2 ^ 70 * D := by gcongr
    _ ≤ |r| ^ 3 / 2 ^ 62 * D := by
        have h3 : 0 ≤ |r| ^ 3 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hDl h3, mul_le_mul_of_nonneg_left hD7 h3]

#print axioms error_low
#print axioms error_check
#print axioms denominator_check
#print axioms kernel_approx

end Verified.Examples.Expm1KernelPoly
