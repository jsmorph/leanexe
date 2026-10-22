import Library.Numerics.Float64.Tgamma.TgammaPolyDDD
import Library.Numerics.Float64.Tgamma.TgammaApprox

/-!
Facts about table words for the instances of the double-double lemmas: a finite word gives a finite
`Float.ofBits` with its exact rational value (`ofBits_finite`, `ofBits_value`), the coefficients
`cDD` are rationals of the words (`cDD_rat`), and the Horner values for `|x| ≤ X` are bounded by the
absolute coefficients weighted by powers of `X` (`horner_bound_pow`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaWords
open CodeLib.IEEE64 LeanExe.ProofKit TgammaPoly TgammaPolyDDD

set_option exponentiation.threshold 4096

theorem ofBits_bits (w : UInt64) (h : Wasm.IEEE64.isFinite w = true) : (Float.ofBits w).toBits = w := by
  rw [F64Bits.toBits_ofBits, not_nan_of_finite h]
  rfl

theorem ofBits_finite (w : UInt64) (h : Wasm.IEEE64.isFinite w = true) :
    Finite (Float.ofBits w).toBits := by
  rw [ofBits_bits w h]
  exact h

theorem ofBits_value (w : UInt64) (h : Wasm.IEEE64.isFinite w = true) :
    value (Float.ofBits w).toBits = (PolyBound.ratOfWord w : ℝ) := by
  rw [ofBits_bits w h, PolyBound.ratOfWord_cast]

theorem cDD_rat (tab : Array UInt64) (o : UInt64) (k : ℕ)
    (h1 : Wasm.IEEE64.isFinite tab[o.toNat + 2 * k]! = true)
    (h2 : Wasm.IEEE64.isFinite tab[o.toNat + 2 * k + 1]! = true) :
    cDD tab o k = ((PolyBound.ratOfWord tab[o.toNat + 2 * k]! +
      PolyBound.ratOfWord tab[o.toNat + 2 * k + 1]! : ℚ) : ℝ) := by
  rw [cDD, ofBits_value _ h1, ofBits_value _ h2]
  push_cast
  rfl

/-- The Horner values for `|x| ≤ X` against the weighted coefficients. -/
theorem horner_bound_pow (c : ℕ → ℝ) (N : ℕ) (L x X : ℝ) (hx : |x| ≤ X) (m : ℕ) (hm : m + 1 ≤ N) :
    |horner c N L x m| ≤
      (∑ k ∈ Finset.range (m + 1), |c (N - 1 - m + k)| * X ^ k) + |L| * X ^ m := by
  rw [horner_eq c N L x m hm]
  have hX0 : 0 ≤ X := (abs_nonneg _).trans hx
  have hxk : ∀ k : ℕ, |x| ^ k ≤ X ^ k := fun k => pow_le_pow_left₀ (abs_nonneg _) hx k
  calc |(∑ k ∈ Finset.range (m + 1), c (N - 1 - m + k) * x ^ k) + L * x ^ m|
      ≤ |∑ k ∈ Finset.range (m + 1), c (N - 1 - m + k) * x ^ k| + |L * x ^ m| := abs_add_le _ _
    _ ≤ (∑ k ∈ Finset.range (m + 1), |c (N - 1 - m + k)| * X ^ k) + |L| * X ^ m := by
      apply add_le_add
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hxk k) (abs_nonneg _)
      · rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hxk m) (abs_nonneg _)

theorem eval_append (l1 l2 : List ℚ) (x : ℝ) :
    PolyBound.eval (l1 ++ l2) x = PolyBound.eval l1 x + x ^ l1.length * PolyBound.eval l2 x := by
  induction l1 with
  | nil => simp [PolyBound.eval]
  | cons a l ih =>
    simp only [List.cons_append, PolyBound.eval, ih, List.length_cons, pow_succ]
    ring

theorem eval_map_range (f : ℕ → ℚ) (n : ℕ) (x : ℝ) :
    PolyBound.eval ((List.range n).map f) x = ∑ k ∈ Finset.range n, (f k : ℝ) * x ^ k := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, PolyBound.eval, ih,
      Finset.sum_range_succ', pow_zero, mul_one, Finset.mul_sum]
    simp only [Function.comp, pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem eval_coeffs (tab : Array UInt64) (o s n : ℕ) (x : ℝ) :
    PolyBound.eval (TgammaApprox.coeffs tab o s n) x =
      ∑ k ∈ Finset.range n, (TgammaApprox.q tab (o + s * k) : ℝ) * x ^ k :=
  eval_map_range _ n x

theorem eval_ddCoeffs (tab : Array UInt64) (o n : ℕ) (x : ℝ) :
    PolyBound.eval (TgammaApprox.ddCoeffs tab o n) x =
      ∑ k ∈ Finset.range n,
        ((TgammaApprox.q tab (o + 2 * k) + TgammaApprox.q tab (o + 2 * k + 1) : ℚ) : ℝ) * x ^ k :=
  eval_map_range _ n x

#print axioms ofBits_value
#print axioms cDD_rat
#print axioms horner_bound_pow
#print axioms eval_append
#print axioms eval_map_range

end Library.Numerics.Float64.Tgamma.TgammaWords
