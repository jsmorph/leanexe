import LeanExe.ProofKit.EntireSeries
import LeanExe.ProofKit.TaylorRemainder
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
The Bessel functions `J₀`, `J₁`, `Y₀`, and `Y₁` of real argument, which Mathlib lacks, defined by
their power series in `z = x ^ 2 / 4` ([DLMF 10.2.2, 10.8.1, and 10.8.2](https://dlmf.nist.gov/10.8)):

* `J₀ x = Σ (-1) ^ k z ^ k / k! ^ 2` and `J₁ x = (x/2) Σ (-1) ^ k z ^ k / (k! (k + 1)!)`;
* `Y₀ x = (2/π) ((ln (x/2) + γ) J₀ x + Σ (-1) ^ (k + 1) H k z ^ k / k! ^ 2)`;
* `Y₁ x = (2/π) (ln (x/2) + γ) J₁ x - 2/(π x) - (x/(2π)) Σ (-1) ^ k (H k + H (k + 1)) z ^ k / (k! (k + 1)!)`,

with `γ = Real.eulerMascheroniConstant` and the harmonic numbers `H k = harmonic k`.  DLMF writes
the last series with `ψ (k + 1) + ψ (k + 2) = H k + H (k + 1) - 2 γ`, and its `γ` part is the
`γ` term of the definition here.  `Y₀` and `Y₁` are meant for `x > 0`.

The derivatives are `J₀' = -J₁`, `J₁' = J₀ - J₁/x`, `Y₀' = -Y₁`, and `Y₁' = Y₀ - Y₁/x`, so that
each function satisfies Bessel's equation of its order, and the Wronskian is
`J₁ Y₀ - J₀ Y₁ = 2/(π x)`.  All of them reduce to four identities between the coefficient
sequences, which `field_simp` and `ring` check for every `k`, and the Wronskian to the constancy of
an entire function of `z`.  For `|z| ≤ 1`, that is `|x| ≤ 2`, each series lies within twice its
first omitted term of its partial sum, whose rational coefficients `a0List`, `a1List`, `c0List`,
and `c1List` give as `PolyBound` polynomials.
-/

namespace LeanExe.ProofKit.Bessel

open Real Finset EntireSeries PolyBound

/-- `(-1) ^ k / k! ^ 2`, the coefficients of `J₀` in `z`. -/
def qa0 (k : ℕ) : ℚ := (-1) ^ k / (k.factorial : ℚ) ^ 2

/-- `(-1) ^ k / (k! (k + 1)!)`, the coefficients of `2 J₁ / x` in `z`. -/
def qa1 (k : ℕ) : ℚ := (-1) ^ k / ((k.factorial : ℚ) * (k + 1).factorial)

/-- `(-1) ^ (k + 1) H k / k! ^ 2`, the coefficients of the series in `Y₀`. -/
def qc0 (k : ℕ) : ℚ := (-1) ^ (k + 1) * harmonic k / (k.factorial : ℚ) ^ 2

/-- `(-1) ^ k (H k + H (k + 1)) / (k! (k + 1)!)`, the coefficients of the series in `Y₁`. -/
def qc1 (k : ℕ) : ℚ :=
  (-1) ^ k * (harmonic k + harmonic (k + 1)) / ((k.factorial : ℚ) * (k + 1).factorial)

noncomputable def a0 (k : ℕ) : ℝ := qa0 k
noncomputable def a1 (k : ℕ) : ℝ := qa1 k
noncomputable def c0 (k : ℕ) : ℝ := qc0 k
noncomputable def c1 (k : ℕ) : ℝ := qc1 k

/-- The Bessel function of the first kind of order 0. -/
noncomputable def J0 (x : ℝ) : ℝ := psum a0 (x ^ 2 / 4)

/-- The Bessel function of the first kind of order 1. -/
noncomputable def J1 (x : ℝ) : ℝ := x / 2 * psum a1 (x ^ 2 / 4)

/-- The Bessel function of the second kind of order 0, for `x > 0`. -/
noncomputable def Y0 (x : ℝ) : ℝ :=
  2 / π * ((log (x / 2) + eulerMascheroniConstant) * J0 x + psum c0 (x ^ 2 / 4))

/-- The Bessel function of the second kind of order 1, for `x > 0`. -/
noncomputable def Y1 (x : ℝ) : ℝ :=
  2 / π * (log (x / 2) + eulerMascheroniConstant) * J1 x - 2 / (π * x) -
    x / (2 * π) * psum c1 (x ^ 2 / 4)

theorem harmonic_nonneg' (n : ℕ) : (0 : ℚ) ≤ harmonic n := by
  induction n with
  | zero => simp
  | succ n ih => rw [harmonic_succ]; positivity

theorem harmonic_le_self (n : ℕ) : harmonic n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmonic_succ]
    push_cast
    have h : ((n : ℚ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)])
    linarith

theorem one_le_harmonic (n : ℕ) (hn : 1 ≤ n) : 1 ≤ harmonic n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [harmonic_succ]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have := ih h
      have : (0 : ℚ) ≤ (((n + 1 : ℕ) : ℚ))⁻¹ := by positivity
      linarith

theorem factorial_pos' (k : ℕ) : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k

theorem abs_a0 (k : ℕ) : |a0 k| = 1 / (k.factorial : ℝ) ^ 2 := by
  simp [a0, qa0, abs_div, abs_pow]

theorem abs_a1 (k : ℕ) : |a1 k| = 1 / ((k.factorial : ℝ) * (k + 1).factorial) := by
  simp [a1, qa1, abs_div, abs_mul, abs_pow]

theorem abs_c0 (k : ℕ) : |c0 k| = (harmonic k : ℝ) / (k.factorial : ℝ) ^ 2 := by
  have h : (0 : ℝ) ≤ (harmonic k : ℝ) := by exact_mod_cast harmonic_nonneg' k
  simp [c0, qc0, abs_div, abs_mul, abs_pow, abs_of_nonneg h]

theorem abs_c1 (k : ℕ) :
    |c1 k| = ((harmonic k : ℝ) + harmonic (k + 1)) / ((k.factorial : ℝ) * (k + 1).factorial) := by
  have h : (0 : ℝ) ≤ (harmonic k : ℝ) + harmonic (k + 1) := by
    have := harmonic_nonneg' k; have := harmonic_nonneg' (k + 1)
    exact_mod_cast (by linarith : (0 : ℚ) ≤ harmonic k + harmonic (k + 1))
  have hd : (0 : ℝ) ≤ (k.factorial : ℝ) * (k + 1).factorial := by positivity
  rw [c1, qc1]
  push_cast
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg h,
    abs_of_nonneg hd]

theorem one_le_factorial' (k : ℕ) : (1 : ℝ) ≤ k.factorial := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)

theorem entire_a0 : Entire a0 := by
  refine entire_of_le_factorial 1 fun k => ?_
  rw [abs_a0]
  have h1 := one_le_factorial' k
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem entire_a1 : Entire a1 := by
  refine entire_of_le_factorial 1 fun k => ?_
  rw [abs_a1]
  have h1 := one_le_factorial' k
  have h2 := one_le_factorial' (k + 1)
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem entire_c0 : Entire c0 := by
  refine entire_of_le_factorial 1 fun k => ?_
  rw [abs_c0]
  have h1 := one_le_factorial' k
  have hH : (harmonic k : ℝ) ≤ k.factorial := by
    have := harmonic_le_self k
    have h2 : (k : ℚ) ≤ k.factorial := by exact_mod_cast Nat.self_le_factorial k
    exact_mod_cast this.trans h2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem entire_c1 : Entire c1 := by
  refine entire_of_le_factorial 2 fun k => ?_
  rw [abs_c1]
  have h1 := one_le_factorial' k
  have hH : (harmonic k : ℝ) + harmonic (k + 1) ≤ 2 * (k + 1).factorial := by
    have e1 := harmonic_le_self k
    have e2 := harmonic_le_self (k + 1)
    have f1 : ((k + 1 : ℕ) : ℚ) ≤ (k + 1).factorial := by exact_mod_cast Nat.self_le_factorial (k + 1)
    have f0 : (k : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast (by linarith : harmonic k + harmonic (k + 1) ≤ 2 * ((k + 1).factorial : ℚ))
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [factorial_pos' (k + 1)]

/-! The four identities between the coefficients. -/

theorem qa0_deriv (k : ℕ) : ((k : ℚ) + 1) * qa0 (k + 1) = -qa1 k := by
  simp only [qa0, qa1, Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem qa1_identity (k : ℕ) : qa1 k + k * qa1 k = qa0 k := by
  simp only [qa0, qa1, Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem qc0_identity (k : ℕ) : qa0 (k + 1) + 2 * (((k + 1 : ℕ) : ℚ) * qc0 (k + 1)) = qc1 k := by
  simp only [qa0, qc0, qc1, Nat.factorial_succ, harmonic_succ]
  push_cast
  have : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

theorem qc1_identity (k : ℕ) : qc1 k + k * qc1 k = qa1 k - 2 * qc0 k := by
  simp only [qa1, qc0, qc1, Nat.factorial_succ, harmonic_succ]
  push_cast
  have : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-! The identities between the series. -/

theorem psum_dcoef_a0 (z : ℝ) : psum (dcoef a0) z = -psum a1 z := by
  rw [← psum_neg]
  refine psum_congr (fun k => ?_) z
  simp only [dcoef, a0, a1]
  exact_mod_cast qa0_deriv k

theorem a1_series (z : ℝ) : psum a1 z + z * psum (dcoef a1) z = psum a0 z := by
  rw [mul_psum_dcoef entire_a1, ← psum_add entire_a1 entire_a1.nat_mul]
  refine psum_congr (fun k => ?_) z
  simp only [a0, a1]
  exact_mod_cast qa1_identity k

theorem c0_series (z : ℝ) : psum a0 z + 2 * (z * psum (dcoef c0) z) = 1 + z * psum c1 z := by
  rw [mul_psum_dcoef entire_c0, ← psum_const_mul,
    ← psum_add entire_a0 (entire_c0.nat_mul.const_mul 2),
    psum_eq_zero_add (entire_a0.add (entire_c0.nat_mul.const_mul 2))]
  congr 1
  · simp [a0, qa0]
  · congr 1
    refine psum_congr (fun k => ?_) z
    simp only [a0, c0, c1]
    exact_mod_cast qc0_identity k

theorem c1_series (z : ℝ) : psum c1 z + z * psum (dcoef c1) z = psum a1 z - 2 * psum c0 z := by
  rw [mul_psum_dcoef entire_c1, ← psum_add entire_c1 entire_c1.nat_mul, ← psum_const_mul,
    sub_eq_add_neg, ← psum_neg, ← psum_add entire_a1 ((entire_c0.const_mul 2).of_abs_le
      (fun k => by rw [abs_neg]))]
  refine psum_congr (fun k => ?_) z
  simp only [a1, c0, c1]
  have := congrArg (fun q : ℚ => (q : ℝ)) (qc1_identity k)
  push_cast at this ⊢
  linarith

/-! Derivatives. -/

theorem hasDerivAt_J0 (x : ℝ) : HasDerivAt J0 (-J1 x) x := by
  refine (entire_a0.hasDerivAt_sq x).congr_deriv ?_
  rw [psum_dcoef_a0, J1]
  ring

theorem hasDerivAt_J1 (x : ℝ) : HasDerivAt J1 (J0 x - psum a1 (x ^ 2 / 4) / 2) x := by
  have h := (hasDerivAt_id' x |>.div_const 2).mul (entire_a1.hasDerivAt_sq x)
  refine h.congr_deriv ?_
  have e := a1_series (x ^ 2 / 4)
  rw [J0]
  linear_combination e

theorem hasDerivAt_J1' (x : ℝ) (hx : x ≠ 0) : HasDerivAt J1 (J0 x - J1 x / x) x := by
  refine (hasDerivAt_J1 x).congr_deriv ?_
  rw [J1]
  field_simp

theorem hasDerivAt_log_half (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => log (y / 2) + eulerMascheroniConstant) (1 / x) x := by
  have h := ((Real.hasDerivAt_log (div_ne_zero hx two_ne_zero)).comp x
    ((hasDerivAt_id' x).div_const 2)).add_const eulerMascheroniConstant
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_Y0 (x : ℝ) (hx : x ≠ 0) : HasDerivAt Y0 (-Y1 x) x := by
  have h := (((hasDerivAt_log_half x hx).mul (hasDerivAt_J0 x)).add
    (entire_c0.hasDerivAt_sq x)).const_mul (2 / π)
  refine h.congr_deriv ?_
  have e := c0_series (x ^ 2 / 4)
  have hpi : π ≠ 0 := pi_ne_zero
  have key : 2 / π * (1 / x * J0 x + (log (x / 2) + eulerMascheroniConstant) * -J1 x +
      psum (dcoef c0) (x ^ 2 / 4) * (x / 2)) - -Y1 x =
      2 / (π * x) * ((psum a0 (x ^ 2 / 4) + 2 * (x ^ 2 / 4 * psum (dcoef c0) (x ^ 2 / 4))) -
        (1 + x ^ 2 / 4 * psum c1 (x ^ 2 / 4))) := by
    rw [Y1, J0, J1]
    field_simp
    ring
  linear_combination key + 2 / (π * x) * e

theorem hasDerivAt_Y1 (x : ℝ) (hx : x ≠ 0) : HasDerivAt Y1 (Y0 x - Y1 x / x) x := by
  have h := ((((hasDerivAt_log_half x hx).mul (hasDerivAt_J1 x)).const_mul (2 / π)).sub
    ((hasDerivAt_inv hx).const_mul (2 / π))).sub
    (((hasDerivAt_id' x).mul (entire_c1.hasDerivAt_sq x)).const_mul (1 / (2 * π)))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · rw [Y1]
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  have e := c1_series (x ^ 2 / 4)
  have hpi : π ≠ 0 := pi_ne_zero
  have key : 2 / π * (1 / x * J1 x + (log (x / 2) + eulerMascheroniConstant) *
      (J0 x - psum a1 (x ^ 2 / 4) / 2)) - 2 / π * -(x ^ 2)⁻¹ -
      1 / (2 * π) * (1 * psum c1 (x ^ 2 / 4) + x * (psum (dcoef c1) (x ^ 2 / 4) * (x / 2))) -
      (Y0 x - Y1 x / x) =
      -(1 / π) * ((psum c1 (x ^ 2 / 4) + x ^ 2 / 4 * psum (dcoef c1) (x ^ 2 / 4)) -
        (psum a1 (x ^ 2 / 4) - 2 * psum c0 (x ^ 2 / 4))) := by
    rw [Y0, Y1, J1]
    field_simp
    ring
  linear_combination key - (1 / π) * e

/-! The Wronskian. -/

theorem wronskian_series (z : ℝ) :
    psum a0 z + 2 * z * psum a1 z * psum c0 z + z * psum a0 z * psum c1 z = 1 := by
  have hd : ∀ z, HasDerivAt
      (fun z => psum a0 z + 2 * z * psum a1 z * psum c0 z + z * psum a0 z * psum c1 z) 0 z := by
    intro z
    have hid := hasDerivAt_id' z
    have h := ((entire_a0.hasDerivAt z).add (((hid.const_mul 2).mul (entire_a1.hasDerivAt z)).mul
      (entire_c0.hasDerivAt z))).add ((hid.mul (entire_a0.hasDerivAt z)).mul
      (entire_c1.hasDerivAt z))
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply]
    have p1 := psum_dcoef_a0 z
    have p2 := a1_series z
    have p3 := c0_series z
    have p4 := c1_series z
    linear_combination (1 + z * psum c1 z) * p1 + 2 * psum c0 z * p2 + psum a1 z * p3 +
      psum a0 z * p4
  have hc := is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt) (fun z => (hd z).deriv) z 0
  rw [hc, psum_zero, psum_zero, psum_zero, psum_zero]
  simp [a0, qa0]

theorem wronskian (x : ℝ) (hx : x ≠ 0) : J1 x * Y0 x - J0 x * Y1 x = 2 / (π * x) := by
  have hw := wronskian_series (x ^ 2 / 4)
  have hpi : π ≠ 0 := pi_ne_zero
  have key : J1 x * Y0 x - J0 x * Y1 x - 2 / (π * x) =
      2 / (π * x) * ((psum a0 (x ^ 2 / 4) + 2 * (x ^ 2 / 4) * psum a1 (x ^ 2 / 4) *
        psum c0 (x ^ 2 / 4) + x ^ 2 / 4 * psum a0 (x ^ 2 / 4) * psum c1 (x ^ 2 / 4)) - 1) := by
    rw [Y0, Y1, J0, J1]
    field_simp
    ring
  rw [hw, sub_self, mul_zero, sub_eq_zero] at key
  exact key

/-! The even and odd parts of `Y₀` and `Y₁` that fdlibm approximates for `x < 2`. -/

theorem Y0_sub_log (x : ℝ) (hx : 0 < x) :
    Y0 x - 2 / π * log x * J0 x =
      2 / π * ((eulerMascheroniConstant - log 2) * psum a0 (x ^ 2 / 4) + psum c0 (x ^ 2 / 4)) := by
  rw [Y0, J0, Real.log_div hx.ne' two_ne_zero]
  ring

theorem Y1_sub_log (x : ℝ) (hx : 0 < x) :
    Y1 x - 2 / π * (log x * J1 x - 1 / x) =
      x / π * ((eulerMascheroniConstant - log 2) * psum a1 (x ^ 2 / 4) -
        psum c1 (x ^ 2 / 4) / 2) := by
  have hpi : π ≠ 0 := pi_ne_zero
  rw [Y1, J1, Real.log_div hx.ne' two_ne_zero]
  field_simp
  ring

/-! Partial sums and their remainders for `|z| ≤ 1`. -/

/-- The first `N` coefficients of `J₀`. -/
def a0List (N : ℕ) : List ℚ := (List.range N).map qa0
/-- The first `N` coefficients of `2 J₁ / x`. -/
def a1List (N : ℕ) : List ℚ := (List.range N).map qa1
/-- The first `N` coefficients of the series in `Y₀`. -/
def c0List (N : ℕ) : List ℚ := (List.range N).map qc0
/-- The first `N` coefficients of the series in `Y₁`. -/
def c1List (N : ℕ) : List ℚ := (List.range N).map qc1

theorem remainder_of_ratio {a : ℕ → ℝ} (ha : Entire a) (q : ℕ → ℚ) (hq : ∀ k, a k = q k)
    (hr : ∀ k, 1 ≤ k → |a (k + 1)| ≤ 1 / 2 * |a k|) (z : ℝ) (hz : |z| ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    |psum a z - eval ((List.range N).map q) z| ≤ 2 * |a N| * |z| ^ N := by
  have h := ha.abs_sub_partial_le z N (1 / 2) (by norm_num) (by norm_num) (fun k hk => by
    have := hr k (by omega)
    calc |a (k + 1)| * |z| ≤ |a (k + 1)| * 1 := by gcongr
      _ ≤ 1 / 2 * |a k| := by linarith)
  rw [TaylorRemainder.eval_map_range]
  simp only [← hq]
  calc _ ≤ |a N| * |z| ^ N / (1 - 1 / 2) := h
    _ = 2 * |a N| * |z| ^ N := by ring

theorem a0_ratio (k : ℕ) (hk : 1 ≤ k) : |a0 (k + 1)| ≤ 1 / 2 * |a0 k| := by
  rw [abs_a0, abs_a0, Nat.factorial_succ]
  push_cast
  have h1 := one_le_factorial' k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

theorem a1_ratio (k : ℕ) (hk : 1 ≤ k) : |a1 (k + 1)| ≤ 1 / 2 * |a1 k| := by
  rw [abs_a1, abs_a1, Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  push_cast
  have h1 := one_le_factorial' k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

theorem c0_ratio (k : ℕ) (hk : 1 ≤ k) : |c0 (k + 1)| ≤ 1 / 2 * |c0 k| := by
  rw [abs_c0, abs_c0, Nat.factorial_succ]
  push_cast
  have hF : (0 : ℝ) < (k.factorial : ℝ) := factorial_pos' k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hH : (1 : ℝ) ≤ harmonic k := by exact_mod_cast one_le_harmonic k hk
  have hH1 : ((harmonic (k + 1) : ℚ) : ℝ) ≤ 2 * harmonic k := by
    rw [harmonic_succ]
    push_cast
    have : ((k : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    linarith
  rw [div_le_iff₀ (by positivity)]
  have e : 1 / 2 * ((harmonic k : ℝ) / (k.factorial : ℝ) ^ 2) * (((k : ℝ) + 1) * k.factorial) ^ 2 =
      harmonic k * (((k : ℝ) + 1) ^ 2 / 2) := by
    field_simp
  rw [e]
  have h2 : (2 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 / 2 := by nlinarith
  nlinarith

theorem c1_ratio (k : ℕ) (hk : 1 ≤ k) : |c1 (k + 1)| ≤ 1 / 2 * |c1 k| := by
  rw [abs_c1, abs_c1]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hH : (1 : ℝ) ≤ harmonic k := by exact_mod_cast one_le_harmonic k hk
  have hH1 : (1 : ℝ) ≤ harmonic (k + 1) := by exact_mod_cast one_le_harmonic (k + 1) (by omega)
  have step : ∀ n : ℕ, (1 : ℝ) ≤ harmonic n → ((harmonic (n + 1) : ℚ) : ℝ) ≤ 2 * harmonic n := by
    intro n hn
    rw [harmonic_succ]
    push_cast
    have : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have s1 := step k hH
  have s2 := step (k + 1) hH1
  have hG : (0 : ℝ) < (k.factorial : ℝ) * (k + 1).factorial := by
    have := factorial_pos' k; have := factorial_pos' (k + 1); positivity
  have e : ((k + 1).factorial : ℝ) * ((k + 1 + 1).factorial : ℝ) =
      (((k : ℝ) + 1) * ((k : ℝ) + 2)) * ((k.factorial : ℝ) * (k + 1).factorial) := by
    rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]
    push_cast
    ring
  rw [e, div_le_iff₀ (by positivity)]
  have hN : (0 : ℝ) ≤ (harmonic k : ℝ) + harmonic (k + 1) := by linarith
  have e2 : 1 / 2 * (((harmonic k : ℝ) + harmonic (k + 1)) / ((k.factorial : ℝ) * (k + 1).factorial)) *
      ((((k : ℝ) + 1) * ((k : ℝ) + 2)) * ((k.factorial : ℝ) * (k + 1).factorial)) =
      ((harmonic k : ℝ) + harmonic (k + 1)) * (((k : ℝ) + 1) * ((k : ℝ) + 2) / 2) := by
    field_simp
  rw [e2]
  have h3 : (2 : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 := by nlinarith
  nlinarith

theorem a0_remainder (z : ℝ) (hz : |z| ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    |psum a0 z - eval (a0List N) z| ≤ 2 * |a0 N| * |z| ^ N :=
  remainder_of_ratio entire_a0 qa0 (fun _ => rfl) a0_ratio z hz N hN

theorem a1_remainder (z : ℝ) (hz : |z| ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    |psum a1 z - eval (a1List N) z| ≤ 2 * |a1 N| * |z| ^ N :=
  remainder_of_ratio entire_a1 qa1 (fun _ => rfl) a1_ratio z hz N hN

theorem c0_remainder (z : ℝ) (hz : |z| ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    |psum c0 z - eval (c0List N) z| ≤ 2 * |c0 N| * |z| ^ N :=
  remainder_of_ratio entire_c0 qc0 (fun _ => rfl) c0_ratio z hz N hN

theorem c1_remainder (z : ℝ) (hz : |z| ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    |psum c1 z - eval (c1List N) z| ≤ 2 * |c1 N| * |z| ^ N :=
  remainder_of_ratio entire_c1 qc1 (fun _ => rfl) c1_ratio z hz N hN

#print axioms hasDerivAt_J0
#print axioms hasDerivAt_J1'
#print axioms hasDerivAt_Y0
#print axioms hasDerivAt_Y1
#print axioms wronskian
#print axioms Y0_sub_log
#print axioms Y1_sub_log
#print axioms a0_remainder
#print axioms a1_remainder
#print axioms c0_remainder
#print axioms c1_remainder

end LeanExe.ProofKit.Bessel
