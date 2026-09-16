import Project.ExpSmall.Real
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Project.ExpSmall

theorem polynomial_lipschitz_two (x y : ℝ) (hx : |x| ≤ 2) (hy : |y| ≤ 2) :
    |polynomialReal x - polynomialReal y| ≤ 8 * |x-y| := by
  have hp (n : ℕ) : |x^n-y^n| ≤ |x-y| * n * (2:ℝ)^(n-1) := by
    apply (abs_pow_sub_pow_le x y n).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg x)) (max_le hx hy) _)
      (by positivity)
  have h1 := abs_le.mp (hp 1)
  have h2 := abs_le.mp (hp 2)
  have h3 := abs_le.mp (hp 3)
  have h4 := abs_le.mp (hp 4)
  have h5 := abs_le.mp (hp 5)
  have h6 := abs_le.mp (hp 6)
  norm_num at h1 h2 h3 h4 h5 h6
  apply abs_le.mpr
  constructor <;> dsimp [polynomialReal] <;> nlinarith [abs_nonneg (x-y)]

theorem polynomial_negative_remainder (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ polynomialReal (-t)-Real.exp (-t) ∧
    polynomialReal (-t)-Real.exp (-t) ≤ t^7/5040 := by
  by_cases hz : t = 0
  · subst t
    norm_num [polynomialReal]
  have hn : (0 : ℝ) ≠ -t := by
    intro h
    apply hz
    linarith
  have hd (k : Nat) : iteratedDerivWithin k Real.exp (Set.uIcc 0 (-t)) 0 = 1 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hn)
      Real.contDiff_exp.contDiffAt (by simp)]
    simp [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  have hp : taylorWithinEval Real.exp 6 (Set.uIcc 0 (-t)) 0 (-t) = polynomialReal (-t) := by
    rw [taylor_within_apply]
    simp_rw [hd]
    norm_num [Finset.sum_range_succ, Nat.factorial, polynomialReal]
    ring
  obtain ⟨s, hs, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.exp) (n := 6) hn Real.contDiff_exp.contDiffOn
  have hs0 : s ≤ 0 := by
    have h := hs.2
    change s < max 0 (-t) at h
    rw [max_eq_left (by linarith)] at h
    exact h.le
  rw [hp] at he
  norm_num [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Nat.factorial, neg_pow] at he
  have heq : polynomialReal (-t)-Real.exp (-t) = Real.exp s*t^7/5040 := by
    linarith
  rw [heq]
  constructor
  · positivity
  · have hse : Real.exp s ≤ 1 := by simpa using Real.exp_le_exp.mpr hs0
    calc
      Real.exp s*t^7/5040 ≤ 1*t^7/5040 := by gcongr
      _ = t^7/5040 := by ring

theorem polynomial_negative_bounds (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 2) :
    0 ≤ polynomialReal (-t) ∧ polynomialReal (-t) ≤ 1 := by
  have he := polynomial_negative_remainder t ht
  refine ⟨by linarith [Real.exp_pos (-t)], ?_⟩
  have h1 : 0 ≤ 1-t/2 := by linarith
  have h4 : 0 ≤ 4-t := by linarith
  have h6 : 0 ≤ 6-t := by linarith
  have hid : 1-polynomialReal (-t) =
      t*(1-t/2)+t^3*(4-t)/24+t^5*(6-t)/720 := by
    unfold polynomialReal
    ring
  have hp : 0 ≤ t*(1-t/2)+t^3*(4-t)/24+t^5*(6-t)/720 := by positivity
  rw [← hid] at hp
  linarith

theorem polynomial_weighted_bound (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 2) :
    t*polynomialReal (-t) ≤ 2/5 := by
  let s := t/2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : 0 ≤ 1-s := by dsimp [s]; linarith
  have hid : 2/5-t*polynomialReal (-t) =
      (2/5)*(1-s)^7+(4/5)*s*(1-s)^6+(2/5)*s^2*(1-s)^5+
      (2/3)*s^4*(1-s)^3+(16/15)*s^5*(1-s)^2+(2/3)*s^6*(1-s)+(4/45)*s^7 := by
    dsimp [s, polynomialReal]
    ring
  have hp : 0 ≤ (2/5)*(1-s)^7+(4/5)*s*(1-s)^6+(2/5)*s^2*(1-s)^5+
      (2/3)*s^4*(1-s)^3+(16/15)*s^5*(1-s)^2+(2/3)*s^6*(1-s)+(4/45)*s^7 := by
    positivity
  rw [← hid] at hp
  linarith

theorem polynomial_eighth_error (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 2) :
    |polynomialReal (-t)^8-Real.exp (-8*t)| ≤ 64/24609375 := by
  have hr := polynomial_negative_remainder t ht
  have hb := polynomial_negative_bounds t ht hu
  have hw := polynomial_weighted_bound t ht hu
  have he : Real.exp (-t) ≤ polynomialReal (-t) := by linarith [hr.1]
  have hd := abs_pow_sub_pow_le (a := polynomialReal (-t)) (b := Real.exp (-t)) (n := 8)
  rw [abs_of_nonneg hr.1, abs_of_nonneg hb.1, abs_of_pos (Real.exp_pos _), max_eq_left he] at hd
  norm_num at hd
  have hpow : Real.exp (-t)^8 = Real.exp (-8*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← hpow]
  calc
    _ ≤ (polynomialReal (-t)-Real.exp (-t))*8*polynomialReal (-t)^7 := hd
    _ ≤ (t^7/5040)*8*polynomialReal (-t)^7 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr.2 (by norm_num)) (pow_nonneg hb.1 _)
    _ = (8/5040)*(t*polynomialReal (-t))^7 := by ring
    _ ≤ (8/5040)*(2/5)^7 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀ (mul_nonneg ht hb.1) hw 7
    _ = 64/24609375 := by norm_num

#print axioms polynomial_eighth_error
end Project.ExpSmall
