import Verified.Examples.TgammaDD
import LeanExe.ProofKit.PolyBound

/-!
`Tgamma.polyDDD`, the double-double Horner scheme, with an error bound.  The coefficients are the
double-doubles `c k = tab[o + 2k] + tab[o + 2k + 1]`, and the top coefficient receives the extra
term `l`.  `horner c N L x m` is the exact value after `m` steps, from `c (N - 1) + L` down to
`c 0 + x (⋯)`, so that `horner c N L x (N - 1) = Σ c k x ^ k + L x ^ (N - 1)` (`horner_eval`).
For `|x| ≤ 1`, each step adds at most `polyEps` to the error, and the low part of the state stays
below a cap `Λ` that the hypotheses fix (`polyDDD_spec`).
-/

namespace Verified.Examples.TgammaPoly
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD

set_option exponentiation.threshold 4096

theorem loop_zero {α : Type} (init : α) (f : UInt64 → α → α) : LeanExe.loop 0 init f = init := by
  simp [LeanExe.loop]

theorem loop_succ {α : Type} (m : ℕ) (hm : m + 1 < 2 ^ 64) (init : α) (f : UInt64 → α → α) :
    LeanExe.loop (UInt64.ofNat (m + 1)) init f =
      f (UInt64.ofNat m) (LeanExe.loop (UInt64.ofNat m) init f) := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  unfold LeanExe.loop
  rw [UInt64.toNat_ofNat_of_lt' (by omega), UInt64.toNat_ofNat_of_lt' (by omega), Nat.fold_succ]

/-- The exact Horner values: `horner c N L x 0 = c (N - 1) + L`, and each step multiplies by `x`
and adds the next lower coefficient. -/
noncomputable def horner (c : ℕ → ℝ) (N : ℕ) (L x : ℝ) : ℕ → ℝ
  | 0 => c (N - 1) + L
  | m + 1 => c (N - 2 - m) + x * horner c N L x m

theorem horner_eq (c : ℕ → ℝ) (N : ℕ) (L x : ℝ) (m : ℕ) (hm : m + 1 ≤ N) :
    horner c N L x m = (∑ k ∈ Finset.range (m + 1), c (N - 1 - m + k) * x ^ k) + L * x ^ m := by
  induction m with
  | zero => simp [horner]
  | succ m ih =>
    rw [horner, ih (by omega)]
    conv_rhs => rw [Finset.sum_range_succ']
    have h : ∀ k ∈ Finset.range (m + 1),
        c (N - 1 - (m + 1) + (k + 1)) * x ^ (k + 1) = x * (c (N - 1 - m + k) * x ^ k) := by
      intro k _
      rw [show N - 1 - (m + 1) + (k + 1) = N - 1 - m + k by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum, show N - 1 - (m + 1) + 0 = N - 2 - m by omega,
      pow_zero, mul_one, pow_succ]
    ring

/-- The last Horner value is the polynomial with the extra term. -/
theorem horner_eval (c : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N) (L x : ℝ) :
    horner c N L x (N - 1) = (∑ k ∈ Finset.range N, c k * x ^ k) + L * x ^ (N - 1) := by
  rw [horner_eq c N L x (N - 1) (by omega), show N - 1 + 1 = N by omega]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [show N - 1 - (N - 1) + k = k by omega]

/-- The Horner values are bounded by the sum of the absolute coefficients and `|L|` for
`|x| ≤ 1`. -/
theorem horner_bound (c : ℕ → ℝ) (N : ℕ) (L x : ℝ) (hx : |x| ≤ 1) (m : ℕ) (hm : m + 1 ≤ N) :
    |horner c N L x m| ≤ (∑ k ∈ Finset.range N, |c k|) + |L| := by
  rw [horner_eq c N L x m hm]
  have hxm : ∀ k : ℕ, |x| ^ k ≤ 1 := fun k => pow_le_one₀ (abs_nonneg _) hx
  calc |(∑ k ∈ Finset.range (m + 1), c (N - 1 - m + k) * x ^ k) + L * x ^ m|
      ≤ |∑ k ∈ Finset.range (m + 1), c (N - 1 - m + k) * x ^ k| + |L * x ^ m| := abs_add_le _ _
    _ ≤ (∑ k ∈ Finset.range (m + 1), |c (N - 1 - m + k)|) + |L| := by
      apply add_le_add
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (hxm k)
      · rw [abs_mul, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (hxm m)
    _ ≤ (∑ k ∈ Finset.range N, |c k|) + |L| := by
      gcongr
      have : ∑ k ∈ Finset.range (m + 1), |c (N - 1 - m + k)| =
          ∑ k ∈ Finset.Ico (N - 1 - m) N, |c k| := by
        rw [Finset.sum_Ico_eq_sum_range, show N - (N - 1 - m) = m + 1 by omega]
      rw [this]
      exact Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
        simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢; omega)
        (fun _ _ _ => abs_nonneg _)

#print axioms loop_succ
#print axioms horner_eval
#print axioms horner_bound

end Verified.Examples.TgammaPoly
