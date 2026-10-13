import Verified.Examples.BesselRecur
import LeanExe.ProofKit.BesselModulus
import Verified.Examples.BesselCombine

/-!
Upper bounds on the modulus `M_m(x)` for `m < x`, from an energy of the recurrence 10.6.1.  For a
real solution `f` of `f_(k+2) = λ_(k+1) f_(k+1) - f_k` with `λ_k = 2k/x`, the form
`E_k = f_(k+1)² + f_k² - λ_(k+1) f_(k+1) f_k` keeps its value when `λ` stays fixed through a step,
so `E_(k+1) = E_k - (2/x) f_(k+2) f_(k+1)`.  Since `-a b (2 + λ) ≤ a² + b² - λ a b`,
`E_(k+1) (x + k + 1) ≤ E_k (x + k + 2)` (`energy_step`), so `E_k (x + 1) ≤ E_0 (x + k + 1)`
(`energy_le`); and `E_k ≥ (1 - λ_(k+1)²/4) f_(k+1)²` (`eform_lower`).  Together,
`f_m² (x - m) ≤ (f_0² + f_1²) x` for `m < x` (`energy_bound`).  Applied to `J` and `Y`, with
`M₀², M₁² ≤ 1.3 · 2/(π x)` from `BesselModulus` for `x ≥ 2`, this gives
`(π x/2) M_m² (x - m) ≤ 2.6 x` (`modn_bound`), against `(π x/2) M_m² ≈ x/√(x² - m²)`.
-/

namespace Verified.Examples.BesselOrderEnergy
open Real BesselOrderN BesselRecur
open LeanExe.ProofKit.Bessel (J0 J1 Y0 Y1)

set_option exponentiation.threshold 2048

/-- The quadratic form `a² + b² - l a b`. -/
noncomputable def eform (l a b : ℝ) : ℝ := a ^ 2 + b ^ 2 - l * a * b

theorem eform_lower (l a b : ℝ) : (1 - l ^ 2 / 4) * a ^ 2 ≤ eform l a b := by
  unfold eform
  nlinarith [sq_nonneg (b - l * a / 2)]

theorem eform_cross (l a b : ℝ) : -(a * b) * (2 + l) ≤ eform l a b := by
  unfold eform
  nlinarith [sq_nonneg (a + b)]

theorem energy_step (x : ℝ) (hx : 0 < x) (f : ℕ → ℝ)
    (hf : ∀ k, f (k + 2) = lam x (k + 1) * f (k + 1) - f k) (k : ℕ) :
    eform (lam x (k + 2)) (f (k + 2)) (f (k + 1)) * (x + ((k : ℝ) + 1)) ≤
      eform (lam x (k + 1)) (f (k + 1)) (f k) * (x + ((k : ℝ) + 2)) := by
  have hinv : eform (lam x (k + 1)) (f (k + 2)) (f (k + 1)) =
      eform (lam x (k + 1)) (f (k + 1)) (f k) := by
    rw [hf k]; unfold eform; ring
  have hdiff : eform (lam x (k + 2)) (f (k + 2)) (f (k + 1)) =
      eform (lam x (k + 1)) (f (k + 2)) (f (k + 1)) - 2 / x * (f (k + 2) * f (k + 1)) := by
    unfold eform lam; push_cast <;> ring
  have hlam : 2 / x * (x + ((k : ℝ) + 1)) = 2 + lam x (k + 1) := by
    have hx' : x ≠ 0 := hx.ne'
    unfold lam; push_cast; field_simp <;> ring
  have hc := eform_cross (lam x (k + 1)) (f (k + 2)) (f (k + 1))
  rw [hdiff, ← hinv]
  have e : (eform (lam x (k + 1)) (f (k + 2)) (f (k + 1)) - 2 / x * (f (k + 2) * f (k + 1))) *
      (x + ((k : ℝ) + 1)) = eform (lam x (k + 1)) (f (k + 2)) (f (k + 1)) * (x + ((k : ℝ) + 1)) -
        f (k + 2) * f (k + 1) * (2 / x * (x + ((k : ℝ) + 1))) := by ring
  rw [e, hlam]
  linarith

theorem energy_le (x : ℝ) (hx : 0 < x) (f : ℕ → ℝ)
    (hf : ∀ k, f (k + 2) = lam x (k + 1) * f (k + 1) - f k) (k : ℕ) :
    eform (lam x (k + 1)) (f (k + 1)) (f k) * (x + 1) ≤
      eform (lam x 1) (f 1) (f 0) * (x + ((k : ℝ) + 1)) := by
  induction k with
  | zero => simp
  | succ m ih =>
    have hs := energy_step x hx f hf m
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : eform (lam x (m + 2)) (f (m + 2)) (f (m + 1)) * (x + 1) * (x + ((m : ℝ) + 1)) ≤
        eform (lam x (m + 1)) (f (m + 1)) (f m) * (x + 1) * (x + ((m : ℝ) + 2)) := by
      have := mul_le_mul_of_nonneg_right hs (show (0 : ℝ) ≤ x + 1 by linarith)
      linarith
    have h2 : eform (lam x (m + 1)) (f (m + 1)) (f m) * (x + 1) * (x + ((m : ℝ) + 2)) ≤
        eform (lam x 1) (f 1) (f 0) * (x + ((m : ℝ) + 1)) * (x + ((m : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h3 : eform (lam x (m + 2)) (f (m + 2)) (f (m + 1)) * (x + 1) * (x + ((m : ℝ) + 1)) ≤
        eform (lam x 1) (f 1) (f 0) * (x + ((m : ℝ) + 2)) * (x + ((m : ℝ) + 1)) := by
      linarith
    have h4 := le_of_mul_le_mul_right h3 (by linarith)
    push_cast
    rw [show (m : ℝ) + 1 + 1 = (m : ℝ) + 2 by ring]
    exact h4

/-- `f_m² (x - m) ≤ (f₀² + f₁²) x` for a solution of 10.6.1 and `m < x`. -/
theorem energy_bound (x : ℝ) (hx : 0 < x) (f : ℕ → ℝ)
    (hf : ∀ k, f (k + 2) = lam x (k + 1) * f (k + 1) - f k) (m : ℕ) (hm : (m : ℝ) < x) :
    f m ^ 2 * (x - m) ≤ (f 0 ^ 2 + f 1 ^ 2) * x := by
  rcases m with _ | k
  · simp only [Nat.cast_zero, sub_zero]
    nlinarith [mul_nonneg (sq_nonneg (f 1)) hx.le]
  · have hm' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := Nat.cast_succ k
    rw [hm'] at hm ⊢
    have hm0 : 0 < (k : ℝ) + 1 := by positivity
    have hx' : x ≠ 0 := hx.ne'
    have hE := energy_le x hx f hf k
    have hlow := eform_lower (lam x (k + 1)) (f (k + 1)) (f k)
    have hc : 1 - lam x (k + 1) ^ 2 / 4 = (x ^ 2 - ((k : ℝ) + 1) ^ 2) / x ^ 2 := by
      unfold lam; push_cast; field_simp <;> ring
    rw [hc] at hlow
    obtain ⟨E, hEdef⟩ : ∃ E, E = eform (lam x (k + 1)) (f (k + 1)) (f k) := ⟨_, rfl⟩
    obtain ⟨E0, hE0def⟩ : ∃ E0, E0 = eform (lam x 1) (f 1) (f 0) := ⟨_, rfl⟩
    rw [← hEdef, ← hE0def] at hE
    rw [← hEdef] at hlow
    have h1 : (x ^ 2 - ((k : ℝ) + 1) ^ 2) * f (k + 1) ^ 2 ≤ E * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hlow (sq_nonneg x)
      have e : (x ^ 2 - ((k : ℝ) + 1) ^ 2) / x ^ 2 * f (k + 1) ^ 2 * x ^ 2 =
          (x ^ 2 - ((k : ℝ) + 1) ^ 2) * f (k + 1) ^ 2 := by field_simp <;> ring
      linarith
    have hE0 : E0 * x ≤ (f 0 ^ 2 + f 1 ^ 2) * (x + 1) := by
      have e : E0 * x = (f 1 ^ 2 + f 0 ^ 2) * x - 2 * (f 1 * f 0) := by
        rw [hE0def]; unfold eform lam; push_cast; field_simp <;> ring
      rw [e]
      nlinarith [sq_nonneg (f 0 + f 1)]
    have h2 : (x ^ 2 - ((k : ℝ) + 1) ^ 2) * f (k + 1) ^ 2 * (x + 1) ≤
        E0 * (x + ((k : ℝ) + 1)) * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ x + 1 by linarith)
      have := mul_le_mul_of_nonneg_right hE (sq_nonneg x)
      linarith
    have h3 : E0 * (x + ((k : ℝ) + 1)) * x ^ 2 ≤
        (f 0 ^ 2 + f 1 ^ 2) * x * ((x + ((k : ℝ) + 1)) * (x + 1)) := by
      have := mul_le_mul_of_nonneg_right hE0
        (mul_nonneg hx.le (by linarith) : (0 : ℝ) ≤ x * (x + ((k : ℝ) + 1)))
      linarith
    have h4 : f (k + 1) ^ 2 * (x - ((k : ℝ) + 1)) * ((x + ((k : ℝ) + 1)) * (x + 1)) ≤
        (f 0 ^ 2 + f 1 ^ 2) * x * ((x + ((k : ℝ) + 1)) * (x + 1)) := by
      have e : f (k + 1) ^ 2 * (x - ((k : ℝ) + 1)) * ((x + ((k : ℝ) + 1)) * (x + 1)) =
          (x ^ 2 - ((k : ℝ) + 1) ^ 2) * f (k + 1) ^ 2 * (x + 1) := by ring
      linarith
    exact le_of_mul_le_mul_right h4 (mul_pos (by linarith) (by linarith))

theorem J_solution (x : ℝ) (hx : x ≠ 0) (k : ℕ) :
    Jn (k + 2) x = lam x (k + 1) * Jn (k + 1) x - Jn k x := by
  rw [Jn_recur k x hx]; unfold lam; push_cast <;> ring

theorem Y_solution (x : ℝ) (k : ℕ) : Yn x (k + 2) = lam x (k + 1) * Yn x (k + 1) - Yn x k := by
  rw [Yn_recur]; unfold lam; push_cast <;> ring

theorem modn_sq (x : ℝ) (m : ℕ) : modn x m ^ 2 = Jn m x ^ 2 + Yn x m ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `(π x/2) (M₀² + M₁²) ≤ 2.6` from 2 on. -/
theorem base_sum (x : ℝ) (hx : 2 ≤ x) :
    π * x / 2 * (modn x 0 ^ 2 + modn x 1 ^ 2) ≤ 13 / 5 := by
  have hx0 : 0 < x := by linarith
  obtain ⟨-, h0⟩ := LeanExe.ProofKit.BesselModulus.modulus0_large x hx
  obtain ⟨-, h1⟩ := LeanExe.ProofKit.BesselModulus.modulus1_large x hx
  rw [modn_sq, modn_sq, Jn_zero, Jn_one, Yn_zero, Yn_one]
  have hx' : x ≠ 0 := hx0.ne'
  have hpi : π ≠ 0 := pi_ne_zero
  have hpx : π * x / 2 * (2 / (π * x)) = 1 := by field_simp <;> ring
  have := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (show 0 ≤ π * x / 2 by positivity)
  calc _ ≤ π * x / 2 * (13 / 10 * (2 / (π * x)) + 13 / 10 * (2 / (π * x))) := this
    _ = 13 / 5 * (π * x / 2 * (2 / (π * x))) := by ring
    _ = 13 / 5 := by rw [hpx, mul_one]

/-- `(π x/2) M₀ M₁ ≤ 1.3` from 2 on. -/
theorem base_product (x : ℝ) (hx : 2 ≤ x) : π * x / 2 * (modn x 0 * modn x 1) ≤ 13 / 10 := by
  have hx0 : 0 < x := by linarith
  have h := base_sum x hx
  have hp : modn x 0 * modn x 1 ≤ (modn x 0 ^ 2 + modn x 1 ^ 2) / 2 := by
    nlinarith [sq_nonneg (modn x 0 - modn x 1)]
  have := mul_le_mul_of_nonneg_left hp (show 0 ≤ π * x / 2 by positivity)
  linarith

/-- `(π x/2) M_m² (x - m) ≤ 2.6 x` for `2 ≤ x` and `m < x`. -/
theorem modn_bound (x : ℝ) (hx : 2 ≤ x) (m : ℕ) (hm : (m : ℝ) < x) :
    π * x / 2 * modn x m ^ 2 * (x - m) ≤ 13 / 5 * x := by
  have hx0 : 0 < x := by linarith
  have hJ := energy_bound x hx0 (fun k => Jn k x) (J_solution x hx0.ne') m hm
  have hY := energy_bound x hx0 (Yn x) (Y_solution x) m hm
  have hs := base_sum x hx
  rw [modn_sq, modn_sq] at hs
  rw [modn_sq]
  have hsum : (Jn m x ^ 2 + Yn x m ^ 2) * (x - m) ≤
      (Jn 0 x ^ 2 + Yn x 0 ^ 2 + (Jn 1 x ^ 2 + Yn x 1 ^ 2)) * x := by
    linarith
  have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ π * x / 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hs hx0.le
  calc π * x / 2 * (Jn m x ^ 2 + Yn x m ^ 2) * (x - m) =
      π * x / 2 * ((Jn m x ^ 2 + Yn x m ^ 2) * (x - m)) := by ring
    _ ≤ π * x / 2 * ((Jn 0 x ^ 2 + Yn x 0 ^ 2 + (Jn 1 x ^ 2 + Yn x 1 ^ 2)) * x) := this
    _ = π * x / 2 * (Jn 0 x ^ 2 + Yn x 0 ^ 2 + (Jn 1 x ^ 2 + Yn x 1 ^ 2)) * x := by ring
    _ ≤ 13 / 5 * x := h2

/-- `M_m ≤ 0.92` for `4 ≤ x` and `2 m ≤ x`. -/
theorem modn_le (x : ℝ) (hx : 4 ≤ x) (m : ℕ) (hm : 2 * (m : ℝ) ≤ x) : modn x m ≤ 92 / 100 := by
  have hb := modn_bound x (by linarith) m (by linarith)
  have hx0 : 0 < x := by linarith
  have hpx : 314 / 100 * 4 ≤ π * x := by nlinarith [BesselCombine.pi_bounds.1]
  have h0 : 0 ≤ modn x m := Real.sqrt_nonneg _
  by_contra hc
  push Not at hc
  have hsq : (92 / 100 : ℝ) ^ 2 ≤ modn x m ^ 2 := by nlinarith
  have h1 : π * x / 2 * (92 / 100) ^ 2 * (x / 2) ≤ π * x / 2 * modn x m ^ 2 * (x - m) := by
    have hpx2 : 0 ≤ π * x / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hsq hpx2
    have := mul_le_mul this (show x / 2 ≤ x - m by linarith) (by positivity) (by positivity)
    linarith
  have e : π * x / 2 * (92 / 100) ^ 2 * (x / 2) = π * x * (x * (2116 / 10000)) := by ring
  have h2 := mul_le_mul_of_nonneg_right hpx (show 0 ≤ x * (2116 / 10000) by positivity)
  nlinarith

#print axioms energy_bound
#print axioms modn_bound
#print axioms base_product
#print axioms modn_le

end Verified.Examples.BesselOrderEnergy
