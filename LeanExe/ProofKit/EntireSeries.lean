import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.Convex

/-!
Real power series `psum a z = ∑' k, a k * z ^ k` whose coefficients make `∑ |a k| R ^ k` converge
for every `R ≥ 0`, as the series of the Bessel functions do.  Such a series converges at every
`z`, has the derivative `psum (dcoef a) z` with `dcoef a k = (k + 1) a (k + 1)`
(`Entire.hasDerivAt`), and lies within `|a N| |z| ^ N / (1 - q)` of its partial sum of `N` terms
when `|a (k + 1)| |z| ≤ q |a k|` for `k ≥ N` (`Entire.abs_sub_partial_le`).  The derivative comes
from Mathlib's termwise differentiation of series on a ball, `hasDerivAt_tsum_of_isPreconnected`.
-/

namespace LeanExe.ProofKit.EntireSeries

open Finset

/-- The power series `∑ a k z ^ k`. -/
noncomputable def psum (a : ℕ → ℝ) (z : ℝ) : ℝ := ∑' k, a k * z ^ k

/-- `∑ |a k| R ^ k` converges for every `R ≥ 0`. -/
def Entire (a : ℕ → ℝ) : Prop := ∀ R : ℝ, 0 ≤ R → Summable fun k => |a k| * R ^ k

/-- The coefficients of the derivative. -/
def dcoef (a : ℕ → ℝ) (k : ℕ) : ℝ := (k + 1) * a (k + 1)

variable {a b : ℕ → ℝ}

theorem entire_of_le_factorial (B : ℝ) (h : ∀ k, |a k| ≤ B / k.factorial) : Entire a := by
  intro R hR
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((Real.summable_pow_div_factorial R).mul_left B)
  calc |a k| * R ^ k ≤ B / k.factorial * R ^ k := mul_le_mul_of_nonneg_right (h k) (by positivity)
    _ = B * (R ^ k / k.factorial) := by ring

theorem Entire.of_abs_le (ha : Entire a) (h : ∀ k, |b k| ≤ |a k|) : Entire b := fun R hR =>
  Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => mul_le_mul_of_nonneg_right (h k) (by positivity)) (ha R hR)

theorem Entire.add (ha : Entire a) (hb : Entire b) : Entire fun k => a k + b k := fun R hR =>
  Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity))
    ((ha R hR).add (hb R hR))

theorem Entire.const_mul (ha : Entire a) (c : ℝ) : Entire fun k => c * a k := fun R hR => by
  simpa [abs_mul, mul_assoc] using (ha R hR).mul_left |c|

theorem Entire.nat_mul (ha : Entire a) : Entire fun k => (k : ℝ) * a k := fun R hR => by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (ha (2 * R) (by positivity))
  have hk : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self.le
  rw [abs_mul, Nat.abs_cast, mul_pow]
  calc (k : ℝ) * |a k| * R ^ k = |a k| * ((k : ℝ) * R ^ k) := by ring
    _ ≤ |a k| * (2 ^ k * R ^ k) := by gcongr
    _ = |a k| * (2 ^ k * R ^ k) := rfl

theorem Entire.shift (ha : Entire a) : Entire fun k => a (k + 1) := fun R hR => by
  have hs := (summable_nat_add_iff 1).mpr (ha (R + 1) (by positivity))
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs
  have h1 : R ^ k ≤ (R + 1) ^ (k + 1) :=
    (pow_le_pow_left₀ hR (by linarith) k).trans (pow_le_pow_right₀ (by linarith) (by omega))
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem Entire.deriv (ha : Entire a) : Entire (dcoef a) := by
  have h := ha.nat_mul.shift
  refine h.of_abs_le fun k => ?_
  simp [EntireSeries.dcoef]

theorem Entire.summable (ha : Entire a) (z : ℝ) : Summable fun k => a k * z ^ k :=
  Summable.of_norm_bounded (ha |z| (abs_nonneg z))
    (fun k => le_of_eq (by rw [Real.norm_eq_abs, abs_mul, abs_pow]))

theorem psum_congr (h : ∀ k, a k = b k) (z : ℝ) : psum a z = psum b z := by
  simp only [psum, h]

theorem psum_neg (z : ℝ) : psum (fun k => -a k) z = -psum a z := by
  simp only [psum, neg_mul, tsum_neg]

theorem psum_const_mul (c z : ℝ) : psum (fun k => c * a k) z = c * psum a z := by
  simp only [psum, mul_assoc, tsum_mul_left]

theorem psum_add (ha : Entire a) (hb : Entire b) (z : ℝ) :
    psum (fun k => a k + b k) z = psum a z + psum b z := by
  simp only [psum, add_mul]
  exact (ha.summable z).tsum_add (hb.summable z)

theorem psum_zero (a : ℕ → ℝ) : psum a 0 = a 0 := by
  rw [psum, tsum_eq_single 0 (fun k hk => by simp [zero_pow hk])]
  simp

/-- The constant term and the rest. -/
theorem psum_eq_zero_add (ha : Entire a) (z : ℝ) :
    psum a z = a 0 + z * psum (fun k => a (k + 1)) z := by
  rw [psum, (ha.summable z).tsum_eq_zero_add, psum, ← tsum_mul_left]
  simp only [pow_zero, mul_one, pow_succ]
  congr 1
  exact tsum_congr fun k => by ring

theorem mul_psum_dcoef (ha : Entire a) (z : ℝ) :
    z * psum (dcoef a) z = psum (fun k => (k : ℝ) * a k) z := by
  rw [psum_eq_zero_add ha.nat_mul z]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  congr 1
  exact psum_congr (fun k => by simp [EntireSeries.dcoef]) z

theorem Entire.hasDerivAt (ha : Entire a) (z : ℝ) : HasDerivAt (psum a) (psum (dcoef a) z) z := by
  set R := |z| + 1 with hR
  have hR1 : 1 ≤ R := by have := abs_nonneg z; linarith
  have hu : Summable fun n : ℕ => |a n| * (2 * R) ^ n := ha (2 * R) (by positivity)
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Metric.ball (0 : ℝ) R →
      ‖a n * ((n : ℝ) * y ^ (n - 1))‖ ≤ |a n| * (2 * R) ^ n := by
    intro n y hy
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have hn : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self.le
    have hy' : |y| ^ (n - 1) ≤ R ^ n :=
      (pow_le_pow_left₀ (abs_nonneg y) hy.le _).trans (pow_le_pow_right₀ hR1 (Nat.sub_le n 1))
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hn hy' (by positivity) (by positivity))
      (abs_nonneg _)
  have hz : z ∈ Metric.ball (0 : ℝ) R := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    linarith
  have hderiv := hasDerivAt_tsum_of_isPreconnected (g := fun n y => a n * y ^ n)
    (g' := fun n y => a n * ((n : ℝ) * y ^ (n - 1))) hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) R).isPreconnected (fun n y _ => (hasDerivAt_pow n y).const_mul (a n))
    hbound (Metric.mem_ball_self (by linarith)) (ha.summable 0) hz
  have hsum : Summable fun n => a n * ((n : ℝ) * z ^ (n - 1)) :=
    Summable.of_norm_bounded hu (fun n => hbound n z hz)
  have heq : ∑' n, a n * ((n : ℝ) * z ^ (n - 1)) = psum (dcoef a) z := by
    rw [hsum.tsum_eq_zero_add, psum]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
    exact tsum_congr fun k => by simp only [EntireSeries.dcoef, Nat.cast_add, Nat.cast_one]; ring
  rw [← heq]
  exact hderiv

/-- The derivative of `x ↦ psum a (x ^ 2 / 4)`. -/
theorem Entire.hasDerivAt_sq (ha : Entire a) (x : ℝ) :
    HasDerivAt (fun x => psum a (x ^ 2 / 4)) (psum (dcoef a) (x ^ 2 / 4) * (x / 2)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 4) (x / 2) x := by
    refine ((hasDerivAt_pow 2 x).div_const 4).congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  exact (ha.hasDerivAt (x ^ 2 / 4)).comp x h1

theorem Entire.differentiable (ha : Entire a) : Differentiable ℝ (psum a) := fun z =>
  (ha.hasDerivAt z).differentiableAt

/-- The remainder after `N` terms, from a ratio bound `q` on the later coefficients. -/
theorem Entire.abs_sub_partial_le (ha : Entire a) (z : ℝ) (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : q < 1) (h : ∀ k, N ≤ k → |a (k + 1)| * |z| ≤ q * |a k|) :
    |psum a z - ∑ k ∈ range N, a k * z ^ k| ≤ |a N| * |z| ^ N / (1 - q) := by
  have hs := ha.summable z
  have htail : psum a z - ∑ k ∈ range N, a k * z ^ k = ∑' k, a (k + N) * z ^ (k + N) := by
    have := hs.sum_add_tsum_nat_add N
    unfold psum
    linarith
  have hterm : ∀ k, |a (k + N) * z ^ (k + N)| ≤ |a N| * |z| ^ N * q ^ k := by
    intro k
    induction k with
    | zero => simp [abs_mul, abs_pow]
    | succ k ih =>
      rw [abs_mul, abs_pow] at ih ⊢
      have hk := h (k + N) (by omega)
      rw [show k + 1 + N = (k + N) + 1 by ring, pow_succ, pow_succ]
      calc |a (k + N + 1)| * (|z| ^ (k + N) * |z|)
          = (|a (k + N + 1)| * |z|) * |z| ^ (k + N) := by ring
        _ ≤ (q * |a (k + N)|) * |z| ^ (k + N) := by gcongr
        _ = q * (|a (k + N)| * |z| ^ (k + N)) := by ring
        _ ≤ q * (|a N| * |z| ^ N * q ^ k) := by gcongr
        _ = |a N| * |z| ^ N * (q ^ k * q) := by ring
  have hg : Summable fun k => |a N| * |z| ^ N * q ^ k :=
    (summable_geometric_of_lt_one hq0 hq).mul_left _
  have habs : Summable fun k => |a (k + N) * z ^ (k + N)| :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hterm hg
  rw [htail]
  calc |∑' k, a (k + N) * z ^ (k + N)| ≤ ∑' k, |a (k + N) * z ^ (k + N)| := by
        have := norm_tsum_le_tsum_norm (f := fun k => a (k + N) * z ^ (k + N))
          (by simpa only [Real.norm_eq_abs] using habs)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' k, |a N| * |z| ^ N * q ^ k := Summable.tsum_le_tsum hterm habs hg
    _ = |a N| * |z| ^ N / (1 - q) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq, div_eq_mul_inv]

#print axioms Entire.hasDerivAt
#print axioms Entire.abs_sub_partial_le

end LeanExe.ProofKit.EntireSeries
