import LeanExe.ProofKit.Bessel

/-!
The Bessel functions of integer order, which Mathlib lacks.  For `n ≥ 0`, `Jn n x` is the series
`(x/2) ^ n Σ (-1) ^ k z ^ k / (k! (n + k)!)` in `z = x²/4` (DLMF 10.2.2), and `Jn 0` and `Jn 1`
are ProofKit's `Bessel.J0` and `J1` (`Jn_zero`, `Jn_one`).  The series satisfies the recurrence
`J_(n+2) = (2 (n + 1)/x) J_(n+1) - J_n` (DLMF 10.6.1, `Jn_recur`), from the identity
`a_n k + a_(n+2) (k - 1) = (n + 1) a_(n+1) k` between the coefficients.  `Yn x n` is defined for
`x ≠ 0` from `Bessel.Y0` and `Y1` by the same recurrence; for `x > 0` it is DLMF's `Y_n`.  The
cross product `J_(n+1) Y_n - J_n Y_(n+1) = 2/(π x)` (DLMF 10.5.2) holds for every `n`
(`cross`), by induction from `Bessel.wronskian`.  `JZ` and `YZ` extend both to negative orders by
`J_(-n) = (-1) ^ n J_n` and `Y_(-n) = (-1) ^ n Y_n` (DLMF 10.4.1).
-/

namespace Verified.Examples.BesselOrderN
open Real LeanExe.ProofKit LeanExe.ProofKit.EntireSeries LeanExe.ProofKit.Bessel

/-- The coefficients `(-1) ^ k / (k! (n + k)!)` of `J_n` in `z = x²/4`. -/
noncomputable def an (n k : ℕ) : ℝ := (-1) ^ k / ((k.factorial : ℝ) * (n + k).factorial)

/-- The Bessel function of the first kind of order `n ≥ 0`. -/
noncomputable def Jn (n : ℕ) (x : ℝ) : ℝ := (x / 2) ^ n * psum (an n) (x ^ 2 / 4)

/-- The Bessel function of the second kind of order `n ≥ 0`, for `x > 0`. -/
noncomputable def Yn (x : ℝ) : ℕ → ℝ
  | 0 => Y0 x
  | 1 => Y1 x
  | n + 2 => 2 * (n + 1) / x * Yn x (n + 1) - Yn x n

/-- `J_N` for an integer order. -/
noncomputable def JZ (N : ℤ) (x : ℝ) : ℝ := (-1) ^ (if N < 0 then N.natAbs else 0) * Jn N.natAbs x

/-- `Y_N` for an integer order, for `x > 0`. -/
noncomputable def YZ (N : ℤ) (x : ℝ) : ℝ := (-1) ^ (if N < 0 then N.natAbs else 0) * Yn x N.natAbs

theorem abs_an (n k : ℕ) : |an n k| = 1 / ((k.factorial : ℝ) * (n + k).factorial) := by
  rw [an, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (k.factorial : ℝ) * (n + k).factorial)]

theorem entire_an (n : ℕ) : Entire (an n) := by
  refine entire_of_le_factorial 1 fun k => ?_
  rw [abs_an]
  have h1 := one_le_factorial' k
  have h2 := one_le_factorial' (n + k)
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem an_zero (k : ℕ) : an 0 k = a0 k := by
  simp only [an, a0, qa0, zero_add]
  push_cast
  ring

theorem an_one (k : ℕ) : an 1 k = a1 k := by
  simp only [an, a1, qa1]
  push_cast
  rw [add_comm 1 k]

theorem Jn_zero (x : ℝ) : Jn 0 x = J0 x := by
  rw [Jn, J0, pow_zero, one_mul]
  exact psum_congr an_zero _

theorem Jn_one (x : ℝ) : Jn 1 x = J1 x := by
  rw [Jn, J1, pow_one]
  congr 1
  exact psum_congr an_one _

/-- The coefficient identity behind the recurrence. -/
theorem an_identity (n k : ℕ) :
    an n (k + 1) + an (n + 2) k = (n + 1) * an (n + 1) (k + 1) := by
  simp only [an, Nat.factorial_succ, show n + (k + 1) = (n + k) + 1 by ring,
    show n + 2 + k = (n + k) + 1 + 1 by ring, show n + 1 + (k + 1) = (n + k) + 1 + 1 by ring]
  push_cast
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((n + k).factorial : ℝ) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp <;> ring

theorem an_identity_zero (n : ℕ) : an n 0 = (n + 1) * an (n + 1) 0 := by
  simp only [an, Nat.factorial_zero, add_zero, Nat.factorial_succ, pow_zero]
  push_cast
  have h2 : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp <;> ring

/-- `S_n + z S_(n+2) = (n + 1) S_(n+1)` for the series `S_m = psum (an m)`. -/
theorem series_recur (n : ℕ) (z : ℝ) :
    psum (an n) z + z * psum (an (n + 2)) z = (n + 1) * psum (an (n + 1)) z := by
  rw [psum_eq_zero_add (entire_an n) z, psum_eq_zero_add (entire_an (n + 1)) z, an_identity_zero n]
  have h := psum_add (entire_an n).shift (entire_an (n + 2)) z
  have h2 : psum (fun k => an n (k + 1) + an (n + 2) k) z =
      (n + 1) * psum (fun k => an (n + 1) (k + 1)) z := by
    rw [← psum_const_mul]
    exact psum_congr (fun k => an_identity n k) z
  have h3 : psum (fun k => an n (k + 1)) z + psum (an (n + 2)) z =
      (n + 1) * psum (fun k => an (n + 1) (k + 1)) z := by rw [← h, h2]
  linear_combination z * h3

/-- DLMF 10.6.1 for the series. -/
theorem Jn_recur (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    Jn (n + 2) x = 2 * (n + 1) / x * Jn (n + 1) x - Jn n x := by
  have h := series_recur n (x ^ 2 / 4)
  simp only [Jn]
  have e1 : 2 * (n + 1) / x * ((x / 2) ^ (n + 1) * psum (an (n + 1)) (x ^ 2 / 4)) =
      (n + 1) * ((x / 2) ^ n * psum (an (n + 1)) (x ^ 2 / 4)) := by
    field_simp <;> ring
  rw [e1]
  linear_combination (x / 2) ^ n * h

theorem Yn_recur (x : ℝ) (n : ℕ) : Yn x (n + 2) = 2 * (n + 1) / x * Yn x (n + 1) - Yn x n := rfl

/-- DLMF 10.5.2 for every order. -/
theorem cross (x : ℝ) (hx : x ≠ 0) :
    ∀ n : ℕ, Jn (n + 1) x * Yn x n - Jn n x * Yn x (n + 1) = 2 / (π * x)
  | 0 => by
    rw [Jn_one, Jn_zero]
    exact wronskian x hx
  | n + 1 => by
    have ih := cross x hx n
    show Jn (n + 2) x * Yn x (n + 1) - Jn (n + 1) x * Yn x (n + 2) = 2 / (π * x)
    rw [Jn_recur n x hx, Yn_recur]
    linear_combination ih

theorem Jn_neg (n : ℕ) (x : ℝ) : Jn n (-x) = (-1) ^ n * Jn n x := by
  unfold Jn
  rw [show -x / 2 = -(x / 2) by ring, show (-x) ^ 2 / 4 = x ^ 2 / 4 by ring, neg_pow]
  ring

theorem Jn_at_zero (n : ℕ) (hn : 1 ≤ n) : Jn n 0 = 0 := by
  simp only [Jn, zero_div]
  rw [zero_pow (by omega), zero_mul]

theorem JZ_natAbs (N : ℤ) (x : ℝ) : JZ N x ^ 2 = Jn N.natAbs x ^ 2 := by
  unfold JZ
  rw [mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow, one_mul]

theorem YZ_natAbs (N : ℤ) (x : ℝ) : YZ N x ^ 2 = Yn x N.natAbs ^ 2 := by
  unfold YZ
  rw [mul_pow, ← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow, one_mul]

#print axioms entire_an
#print axioms Jn_zero
#print axioms Jn_one
#print axioms series_recur
#print axioms Jn_recur
#print axioms cross
#print axioms Jn_neg

end Verified.Examples.BesselOrderN
