import Library.Numerics.Float64.Bessel.BesselOrderN

/-!
The propagation of errors through the recurrence 10.6.1.  A real sequence `f` with
`f (k + 2) = (2 (k + 1)/x) f (k + 1) - f k + δ k` differs from `J_n` (or `Y_n`) by
`(π x/2) [e₁ K₀(n) + e₀ K₁(n)] + Σ_(k < n - 1) δ_k (π x/2) (Y_(k+1) J_n - J_(k+1) Y_n)`
(`error_formula`), where `e₀` and `e₁` are the starting errors, `K₀(n) = Y₀ J_n - J₀ Y_n`, and
`K₁(n) = J₁ Y_n - Y₁ J_n`.  The kernel `kern m n = (π x/2)(Y_m J_n - J_m Y_n)` satisfies the
recurrence in `n`, vanishes at `n = m`, and equals 1 at `n = m + 1` by the cross product
(`BesselOrderN.cross`); Cauchy–Schwarz bounds it by `(π x/2) M_m M_n` (`kern_le`).
-/

namespace Library.Numerics.Float64.Bessel.BesselRecur
open Real Finset LeanExe.ProofKit.Bessel BesselOrderN

theorem Yn_zero (x : ℝ) : Yn x 0 = Y0 x := rfl

theorem Yn_one (x : ℝ) : Yn x 1 = Y1 x := rfl

/-- `λ_k = 2k/x`. -/
noncomputable def lam (x : ℝ) (k : ℕ) : ℝ := 2 * k / x

/-- The response at index `n` to a unit error at index `m + 1` with no error at `m`. -/
noncomputable def kern (x : ℝ) (m n : ℕ) : ℝ := π * x / 2 * (Yn x m * Jn n x - Jn m x * Yn x n)

/-- The modulus `M_n(x)`. -/
noncomputable def modn (x : ℝ) (n : ℕ) : ℝ := √(Jn n x ^ 2 + Yn x n ^ 2)

theorem kern_recur (x : ℝ) (hx : x ≠ 0) (m n : ℕ) :
    kern x m (n + 2) = lam x (n + 1) * kern x m (n + 1) - kern x m n := by
  simp only [kern, lam]
  rw [Jn_recur n x hx, Yn_recur]
  push_cast
  ring

theorem kern_self (x : ℝ) (m : ℕ) : kern x m m = 0 := by
  simp only [kern]; ring

theorem kern_succ (x : ℝ) (hx : x ≠ 0) (m : ℕ) : kern x m (m + 1) = 1 := by
  have h := cross x hx m
  have hpi : π ≠ 0 := pi_ne_zero
  simp only [kern]
  rw [show Yn x m * Jn (m + 1) x - Jn m x * Yn x (m + 1) = 2 / (π * x) by rw [← h]; ring]
  field_simp <;> ring

theorem kern_back (x : ℝ) (hx : x ≠ 0) (n : ℕ) : kern x (n + 1) n = -1 := by
  have h := cross x hx n
  have hpi : π ≠ 0 := pi_ne_zero
  simp only [kern]
  rw [show Yn x (n + 1) * Jn n x - Jn (n + 1) x * Yn x n = -(2 / (π * x)) by rw [← h]; ring]
  field_simp <;> ring

theorem kern_one_zero (x : ℝ) (hx : x ≠ 0) : kern x 1 0 = -1 := kern_back x hx 0

/-- The right side of the error formula. -/
noncomputable def resp (x e0 e1 : ℝ) (δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  e1 * kern x 0 n - e0 * kern x 1 n + ∑ k ∈ range (n - 1), δ k * kern x (k + 1) n

theorem resp_zero (x : ℝ) (hx : x ≠ 0) (e0 e1 : ℝ) (δ : ℕ → ℝ) : resp x e0 e1 δ 0 = e0 := by
  simp only [resp, kern_self, kern_one_zero x hx, Nat.zero_sub, range_zero, sum_empty]
  ring

theorem resp_one (x : ℝ) (hx : x ≠ 0) (e0 e1 : ℝ) (δ : ℕ → ℝ) : resp x e0 e1 δ 1 = e1 := by
  simp only [resp, kern_self, Nat.sub_self, range_zero, sum_empty]
  rw [kern_succ x hx 0]
  ring

theorem resp_recur (x : ℝ) (hx : x ≠ 0) (e0 e1 : ℝ) (δ : ℕ → ℝ) (n : ℕ) :
    resp x e0 e1 δ (n + 2) = lam x (n + 1) * resp x e0 e1 δ (n + 1) - resp x e0 e1 δ n + δ n := by
  have hsum : ∀ m, ∑ k ∈ range m, δ k * kern x (k + 1) (n + 2) =
      lam x (n + 1) * ∑ k ∈ range m, δ k * kern x (k + 1) (n + 1) -
        ∑ k ∈ range m, δ k * kern x (k + 1) n := by
    intro m
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [kern_recur x hx]
    ring
  have h1 : ∑ k ∈ range (n + 1), δ k * kern x (k + 1) (n + 1) =
      ∑ k ∈ range n, δ k * kern x (k + 1) (n + 1) := by
    rw [sum_range_succ, kern_self, mul_zero, add_zero]
  have h2 : ∑ k ∈ range (n + 1), δ k * kern x (k + 1) n =
      ∑ k ∈ range (n - 1), δ k * kern x (k + 1) n - δ n := by
    rw [sum_range_succ, kern_back x hx]
    cases n with
    | zero => simp
    | succ m =>
      rw [show m + 1 - 1 = m by omega, sum_range_succ, kern_self]
      ring
  simp only [resp, show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega]
  rw [hsum, h1, h2, kern_recur x hx 0, kern_recur x hx 1]
  ring

/-- The error of a perturbed recurrence. -/
theorem error_formula (x : ℝ) (hx : x ≠ 0) (e δ : ℕ → ℝ)
    (he : ∀ k, e (k + 2) = lam x (k + 1) * e (k + 1) - e k + δ k) :
    ∀ n, e n = resp x (e 0) (e 1) δ n := by
  have key : ∀ n, e n = resp x (e 0) (e 1) δ n ∧ e (n + 1) = resp x (e 0) (e 1) δ (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨(resp_zero x hx _ _ _).symm, (resp_one x hx _ _ _).symm⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      rw [he m, resp_recur x hx, ← ih.1, ← ih.2]
  exact fun n => (key n).1

/-- Cauchy–Schwarz for the kernel. -/
theorem kern_le (x : ℝ) (hx : 0 < x) (m n : ℕ) :
    |kern x m n| ≤ π * x / 2 * (modn x m * modn x n) := by
  simp only [kern, modn]
  rw [abs_mul, abs_of_pos (by positivity), ← Real.sqrt_mul (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (Yn x m * Yn x n + Jn m x * Jn n x)]

#print axioms kern_recur
#print axioms resp_recur
#print axioms error_formula
#print axioms kern_le

end Library.Numerics.Float64.Bessel.BesselRecur
