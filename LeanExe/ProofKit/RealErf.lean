import LeanExe.ProofKit.TaylorRemainder
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The error function `erf x = (2/√π) ∫₀ˣ exp (-t²) dt`, which Mathlib lacks, its complement
`erfc x = 1 - erf x`, and the scaled complement `erfcx x = exp (x²) erfc x`.  The results are
the ones the kernels of fdlibm's `s_erf.c` need: the derivatives, oddness, strict monotonicity,
the limits at infinity from the Gaussian integral, the power series with a remainder bound for
every `x`, the alternating asymptotic bounds of `erfc` for `x > 0`, the differential equation
`erfcx' = 2 x erfcx - 2/√π`, and a comparison of `erfcx` with a function that satisfies the
equation up to a bounded defect, from a known value at the right end of an interval of
nonnegative numbers.  The series bound rests on `exp_nonpos_remainder`, the Taylor remainder of
the exponential at a nonpositive argument, and each asymptotic bound on the sign of a derivative
and the limit at infinity.
-/

namespace LeanExe.ProofKit.RealErf
open Real Set Filter Topology Finset MeasureTheory PolyBound TaylorRemainder

/-- `2/√π`, the factor that makes `erf` tend to 1. -/
noncomputable def scale : ℝ := 2 / √π

/-- The error function. -/
noncomputable def erf (x : ℝ) : ℝ := scale * ∫ t in (0 : ℝ)..x, exp (-t ^ 2)

/-- The complementary error function. -/
noncomputable def erfc (x : ℝ) : ℝ := 1 - erf x

/-- The scaled complementary error function `exp (x²) erfc x`. -/
noncomputable def erfcx (x : ℝ) : ℝ := exp (x ^ 2) * erfc x

theorem scale_pos : 0 < scale := by
  have h : 0 < √π := Real.sqrt_pos.mpr pi_pos
  unfold scale
  positivity

/-- Dyadic bounds on `2/√π` from Mathlib's 20-digit bounds on `π`. -/
theorem scale_bounds :
    (333038747416263463341 / 2 ^ 68 : ℝ) ≤ scale ∧ scale ≤ 333038747416263463344 / 2 ^ 68 := by
  have hs : 0 < √π := Real.sqrt_pos.mpr pi_pos
  have hsq : √π ^ 2 = π := Real.sq_sqrt pi_pos.le
  have hlo := pi_gt_d20
  have hhi := pi_lt_d20
  unfold scale
  constructor
  · rw [le_div_iff₀ hs]
    have h1 : (333038747416263463341 / 2 ^ 68 : ℝ) ^ 2 * π ≤ 4 := by nlinarith
    nlinarith [sq_nonneg (333038747416263463341 / 2 ^ 68 * √π - 2)]
  · rw [div_le_iff₀ hs]
    have h1 : 4 ≤ (333038747416263463344 / 2 ^ 68 : ℝ) ^ 2 * π := by nlinarith
    nlinarith [sq_nonneg (333038747416263463344 / 2 ^ 68 * √π - 2)]

theorem continuous_gauss : Continuous fun t : ℝ => exp (-t ^ 2) := by fun_prop

theorem hasDerivAt_gauss (x : ℝ) :
    HasDerivAt (fun t => exp (-t ^ 2)) (-(2 * x) * exp (-x ^ 2)) x := by
  have h1 : HasDerivAt (fun t : ℝ => -t ^ 2) (-(2 * x)) x := by
    have h := (hasDerivAt_pow 2 x).neg
    refine h.congr_deriv ?_
    norm_num
  exact h1.exp.congr_deriv (by ring)

theorem hasDerivAt_exp_sq (x : ℝ) :
    HasDerivAt (fun t => exp (t ^ 2)) (2 * x * exp (x ^ 2)) x := by
  have h := (hasDerivAt_pow 2 x).exp
  refine h.congr_deriv ?_
  norm_num
  ring

theorem hasDerivAt_erf (x : ℝ) : HasDerivAt erf (scale * exp (-x ^ 2)) x :=
  ((continuous_gauss.integral_hasStrictDerivAt 0 x).hasDerivAt).const_mul scale

theorem hasDerivAt_erfc (x : ℝ) : HasDerivAt erfc (-(scale * exp (-x ^ 2))) x :=
  (hasDerivAt_erf x).const_sub 1

theorem erf_zero : erf 0 = 0 := by simp [erf]

theorem erfc_zero : erfc 0 = 1 := by simp [erfc, erf_zero]

theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  have hd : ∀ y, HasDerivAt (fun y => erf (-y) + erf y) 0 y := by
    intro y
    have h1 := (hasDerivAt_erf (-y)).comp y (hasDerivAt_neg y)
    have h2 := h1.add (hasDerivAt_erf y)
    refine h2.congr_deriv ?_
    rw [neg_sq]
    ring
  have hc := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv)
    x 0
  simp only [neg_zero, erf_zero, add_zero] at hc
  linarith

theorem erfc_neg (x : ℝ) : erfc (-x) = 2 - erfc x := by
  simp only [erfc, erf_neg]
  ring

theorem erf_strictMono : StrictMono erf :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_erf x).deriv]
    exact mul_pos scale_pos (exp_pos _)

theorem tendsto_erf : Tendsto erf atTop (𝓝 1) := by
  have hi : IntegrableOn (fun t : ℝ => exp (-t ^ 2)) (Ioi 0) := by
    have h := (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn (s := Ioi 0)
    simpa only [neg_mul, one_mul] using h
  have ht := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id
  have hv : ∫ t in Ioi (0 : ℝ), exp (-t ^ 2) = √π / 2 := by
    have h := integral_gaussian_Ioi 1
    simp only [neg_mul, one_mul, div_one] at h
    exact h
  rw [hv] at ht
  have h1 : scale * (√π / 2) = 1 := by
    have hs : √π ≠ 0 := (Real.sqrt_pos.mpr pi_pos).ne'
    unfold scale
    field_simp
  rw [← h1]
  exact ht.const_mul scale

theorem erf_lt_one (x : ℝ) : erf x < 1 :=
  lt_of_lt_of_le (erf_strictMono (lt_add_one x))
    (erf_strictMono.monotone.ge_of_tendsto tendsto_erf (x + 1))

theorem neg_one_lt_erf (x : ℝ) : -1 < erf x := by
  have h := erf_lt_one (-x)
  rw [erf_neg] at h
  linarith

theorem erfc_pos (x : ℝ) : 0 < erfc x := by
  have h := erf_lt_one x
  unfold erfc
  linarith

theorem erfc_lt_two (x : ℝ) : erfc x < 2 := by
  have h := neg_one_lt_erf x
  unfold erfc
  linarith

theorem tendsto_erfc : Tendsto erfc atTop (𝓝 0) := by
  have h := tendsto_erf.const_sub 1
  rw [sub_self] at h
  exact h

/-! ### The power series -/

/-- `Σ k < n, y ^ k / k!`, the Taylor polynomial of the exponential. -/
noncomputable def expTaylor (n : ℕ) (y : ℝ) : ℝ := ∑ k ∈ range n, y ^ k / (k.factorial : ℝ)

theorem hasDerivAt_expTaylor (n : ℕ) (y : ℝ) :
    HasDerivAt (expTaylor (n + 1)) (expTaylor n y) y := by
  induction n with
  | zero =>
    have h : expTaylor 1 = fun _ => (1 : ℝ) := by
      funext z
      simp [expTaylor]
    rw [h]
    simpa [expTaylor] using hasDerivAt_const y (1 : ℝ)
  | succ n ih =>
    have hp := (hasDerivAt_pow (n + 1) y).div_const ((n + 1).factorial : ℝ)
    have h := ih.add hp
    have he : expTaylor (n + 1 + 1) =
        fun z => expTaylor (n + 1) z + z ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      funext z
      simp only [expTaylor]
      rw [sum_range_succ]
    rw [he]
    refine h.congr_deriv ?_
    simp only [expTaylor]
    rw [sum_range_succ, Nat.add_sub_cancel, Nat.factorial_succ]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp

theorem expTaylor_zero (n : ℕ) : expTaylor (n + 1) 0 = 1 := by
  simp [expTaylor, sum_range_succ']

/-- The remainder of the exponential's Taylor polynomial at a nonpositive argument is at most
the first omitted term. -/
theorem exp_nonpos_remainder (n : ℕ) : ∀ {y : ℝ}, y ≤ 0 →
    |exp y - expTaylor n y| ≤ (-y) ^ n / (n.factorial : ℝ) := by
  induction n with
  | zero =>
    intro y hy
    simp only [expTaylor, range_zero, sum_empty, sub_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one]
    rw [abs_of_pos (exp_pos y)]
    exact exp_le_one_iff.mpr hy
  | succ n ih =>
    intro y hy
    have hf : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    have hg : ∀ z, HasDerivAt (fun z => exp z - expTaylor (n + 1) z)
        (exp z - expTaylor n z) z := fun z =>
      (hasDerivAt_exp z).sub (hasDerivAt_expTaylor n z)
    have hB : ∀ z, HasDerivAt (fun z => (-z) ^ (n + 1) / ((n + 1).factorial : ℝ))
        (-((-z) ^ n / (n.factorial : ℝ))) z := by
      intro z
      have h := ((hasDerivAt_neg z).pow (n + 1)).div_const ((n + 1).factorial : ℝ)
      refine h.congr_deriv ?_
      rw [Nat.add_sub_cancel, Nat.factorial_succ]
      have hn : (n.factorial : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
    have hmono (s : ℝ) (hs : s = 1 ∨ s = -1) :
        AntitoneOn (fun z => (-z) ^ (n + 1) / ((n + 1).factorial : ℝ) +
          s * (exp z - expTaylor (n + 1) z)) (Iic 0) := by
      have hd : ∀ z, HasDerivAt (fun z => (-z) ^ (n + 1) / ((n + 1).factorial : ℝ) +
          s * (exp z - expTaylor (n + 1) z))
          (-((-z) ^ n / (n.factorial : ℝ)) + s * (exp z - expTaylor n z)) z :=
        fun z => (hB z).add ((hg z).const_mul s)
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
      · exact fun z _ => (hd z).continuousAt.continuousWithinAt
      · exact fun z _ => (hd z).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [interior_Iic] at hz
        rw [(hd z).deriv]
        have h := ih (le_of_lt hz)
        rcases hs with hs | hs <;> rw [hs]
        · have := le_abs_self (exp z - expTaylor n z)
          linarith
        · have := neg_abs_le (exp z - expTaylor n z)
          linarith
    have h0 : (-(0 : ℝ)) ^ (n + 1) / ((n + 1).factorial : ℝ) = 0 := by simp
    have he0 : exp 0 - expTaylor (n + 1) 0 = 0 := by rw [expTaylor_zero, exp_zero, sub_self]
    have h1 := hmono 1 (Or.inl rfl) hy self_mem_Iic hy
    have h2 := hmono (-1) (Or.inr rfl) hy self_mem_Iic hy
    simp only [h0, he0, mul_zero, add_zero] at h1 h2
    rw [abs_le]
    constructor <;> linarith

/-- `Σ k < n, (-1) ^ k z ^ k / (k! (2 k + 1))`: `x * eval (erfCoeffs n) (x ^ 2)` is the partial
sum of `∫₀ˣ exp (-t²) dt`. -/
def erfCoeffs (n : ℕ) : List ℚ :=
  (List.range n).map fun k => (-1) ^ k / ((k.factorial * (2 * k + 1) : ℕ) : ℚ)

theorem erfPartial_eq (n : ℕ) (x : ℝ) :
    x * eval (erfCoeffs n) (x ^ 2) =
      ∑ k ∈ range n, (-1) ^ k * x ^ (2 * k + 1) / ((k.factorial * (2 * k + 1) : ℕ) : ℝ) := by
  rw [erfCoeffs, eval_map_range, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem hasDerivAt_erfPartial (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => x * eval (erfCoeffs n) (x ^ 2)) (expTaylor n (-x ^ 2)) x := by
  have he : (fun x : ℝ => x * eval (erfCoeffs n) (x ^ 2)) = fun x =>
      ∑ k ∈ range n, (-1) ^ k * x ^ (2 * k + 1) / ((k.factorial * (2 * k + 1) : ℕ) : ℝ) := by
    funext x
    exact erfPartial_eq n x
  rw [he]
  have hs := HasDerivAt.fun_sum (u := range n) (x := x)
    (A := fun k x => (-1) ^ k * x ^ (2 * k + 1) / ((k.factorial * (2 * k + 1) : ℕ) : ℝ))
    (A' := fun k => (-1) ^ k * (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k + 1 - 1)) /
      ((k.factorial * (2 * k + 1) : ℕ) : ℝ))
    (fun k _ => ((hasDerivAt_pow (2 * k + 1) x).const_mul _).div_const _)
  refine hs.congr_deriv ?_
  · simp only [expTaylor]
    refine sum_congr rfl fun k _ => ?_
    rw [Nat.add_sub_cancel]
    have hf : (k.factorial : ℝ) ≠ 0 := by positivity
    have ho : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at ho ⊢
    rw [neg_pow, pow_mul]
    field_simp
    rw [neg_pow (x ^ 2) k, one_pow, mul_one]

theorem erfPartial_neg (n : ℕ) (x : ℝ) :
    -x * eval (erfCoeffs n) ((-x) ^ 2) = -(x * eval (erfCoeffs n) (x ^ 2)) := by
  rw [neg_sq]
  ring

/-- The power series of `erf` with the remainder bound, for every `x`. -/
theorem erf_series (n : ℕ) (x : ℝ) :
    |erf x - scale * (x * eval (erfCoeffs n) (x ^ 2))| ≤
      scale * (|x| ^ (2 * n + 1) / ((n.factorial * (2 * n + 1) : ℕ) : ℝ)) := by
  have hpos : (0 : ℝ) < ((n.factorial * (2 * n + 1) : ℕ) : ℝ) := by positivity
  have hF : ∀ z, HasDerivAt (fun z => erf z - scale * (z * eval (erfCoeffs n) (z ^ 2)))
      (scale * (exp (-z ^ 2) - expTaylor n (-z ^ 2))) z := by
    intro z
    have h := (hasDerivAt_erf z).sub ((hasDerivAt_erfPartial n z).const_mul scale)
    refine h.congr_deriv ?_
    ring
  have hB : ∀ z, HasDerivAt (fun z => scale * (z ^ (2 * n + 1) /
      ((n.factorial * (2 * n + 1) : ℕ) : ℝ))) (scale * (z ^ (2 * n) / (n.factorial : ℝ))) z := by
    intro z
    have h := ((hasDerivAt_pow (2 * n + 1) z).div_const
      ((n.factorial * (2 * n + 1) : ℕ) : ℝ)).const_mul scale
    refine h.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have ho : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at ho ⊢
    field_simp
  have hmono (s : ℝ) (hs : s = 1 ∨ s = -1) :
      MonotoneOn (fun z => scale * (z ^ (2 * n + 1) / ((n.factorial * (2 * n + 1) : ℕ) : ℝ)) +
        s * (erf z - scale * (z * eval (erfCoeffs n) (z ^ 2)))) (Ici 0) := by
    have hd : ∀ z, HasDerivAt (fun z => scale * (z ^ (2 * n + 1) /
        ((n.factorial * (2 * n + 1) : ℕ) : ℝ)) +
        s * (erf z - scale * (z * eval (erfCoeffs n) (z ^ 2))))
        (scale * (z ^ (2 * n) / (n.factorial : ℝ)) +
          s * (scale * (exp (-z ^ 2) - expTaylor n (-z ^ 2)))) z :=
      fun z => (hB z).add ((hF z).const_mul s)
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun z _ => (hd z).continuousAt.continuousWithinAt
    · exact fun z _ => (hd z).differentiableAt.differentiableWithinAt
    · intro z _
      rw [(hd z).deriv]
      have h := exp_nonpos_remainder n (y := -z ^ 2) (by nlinarith [sq_nonneg z])
      rw [neg_neg, ← pow_mul] at h
      have hsc := scale_pos
      rcases hs with hs | hs <;> rw [hs]
      · have := neg_abs_le (exp (-z ^ 2) - expTaylor n (-z ^ 2))
        rw [show scale * (z ^ (2 * n) / (n.factorial : ℝ)) +
            1 * (scale * (exp (-z ^ 2) - expTaylor n (-z ^ 2))) =
            scale * (z ^ (2 * n) / (n.factorial : ℝ) + (exp (-z ^ 2) - expTaylor n (-z ^ 2)))
            by ring]
        exact mul_nonneg hsc.le (by linarith)
      · have := le_abs_self (exp (-z ^ 2) - expTaylor n (-z ^ 2))
        rw [show scale * (z ^ (2 * n) / (n.factorial : ℝ)) +
            -1 * (scale * (exp (-z ^ 2) - expTaylor n (-z ^ 2))) =
            scale * (z ^ (2 * n) / (n.factorial : ℝ) - (exp (-z ^ 2) - expTaylor n (-z ^ 2)))
            by ring]
        exact mul_nonneg hsc.le (by linarith)
  have hpart : ∀ z, 0 ≤ z → |erf z - scale * (z * eval (erfCoeffs n) (z ^ 2))| ≤
      scale * (z ^ (2 * n + 1) / ((n.factorial * (2 * n + 1) : ℕ) : ℝ)) := by
    intro z hz
    have h0 : erf 0 - scale * (0 * eval (erfCoeffs n) (0 ^ 2)) = 0 := by simp [erf_zero]
    have hb0 : scale * ((0 : ℝ) ^ (2 * n + 1) / ((n.factorial * (2 * n + 1) : ℕ) : ℝ)) = 0 := by
      simp
    have h1 := hmono 1 (Or.inl rfl) self_mem_Ici hz hz
    have h2 := hmono (-1) (Or.inr rfl) self_mem_Ici hz hz
    simp only [h0, hb0, mul_zero, add_zero] at h1 h2
    rw [abs_le]
    constructor <;> linarith
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact hpart x hx
  · have h := hpart (-x) (by linarith)
    rw [erf_neg, erfPartial_neg] at h
    rw [abs_of_neg hx]
    have he : -erf x - scale * -(x * eval (erfCoeffs n) (x ^ 2)) =
        -(erf x - scale * (x * eval (erfCoeffs n) (x ^ 2))) := by ring
    rwa [he, abs_neg] at h

/-! ### The asymptotic bounds -/

/-- The coefficients `(-1) ^ n (2 n - 1)!! / 2 ^ n` of the asymptotic series of `erfc`. -/
def asymCoeff : ℕ → ℚ
  | 0 => 1
  | n + 1 => -asymCoeff n * (2 * n + 1) / 2

theorem asymCoeff_sign (n : ℕ) : 0 ≤ (-1) ^ n * (asymCoeff n : ℝ) := by
  induction n with
  | zero => simp [asymCoeff]
  | succ n ih =>
    rw [asymCoeff]
    push_cast
    have h : (-1 : ℝ) ^ (n + 1) * (-(asymCoeff n : ℝ) * (2 * n + 1) / 2) =
        ((-1) ^ n * (asymCoeff n : ℝ)) * ((2 * n + 1) / 2) := by ring
    rw [h]
    exact mul_nonneg ih (by positivity)

/-- `Σ n < N, asymCoeff n x⁻¹ ^ (2 n + 1)`. -/
noncomputable def asymSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ range N, (asymCoeff n : ℝ) * x⁻¹ ^ (2 * n + 1)

/-- The partial sum `(1/√π) exp (-x²) Σ n < N, asymCoeff n x ^ (-2 n - 1)` of the asymptotic
series of `erfc x`. -/
noncomputable def asym (N : ℕ) (x : ℝ) : ℝ := scale / 2 * exp (-x ^ 2) * asymSum N x

theorem asymSum_eq (N : ℕ) (x : ℝ) :
    asymSum N x = x⁻¹ * eval ((List.range N).map asymCoeff) (x⁻¹ ^ 2) := by
  rw [asymSum, eval_map_range, mul_sum]
  refine sum_congr rfl fun n _ => ?_
  ring

theorem hasDerivAt_inv_pow (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x => x⁻¹ ^ k) (-(k * x⁻¹ ^ (k + 1))) x := by
  have h := (hasDerivAt_inv hx).pow k
  refine h.congr_deriv ?_
  rcases k with _ | k
  · simp
  · rw [Nat.add_sub_cancel, ← inv_pow]
    push_cast
    ring

theorem hasDerivAt_asym (N : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (asym N) (-(scale * exp (-x ^ 2)) +
      scale * (asymCoeff N : ℝ) * exp (-x ^ 2) * x⁻¹ ^ (2 * N)) x := by
  have hexp := hasDerivAt_gauss x
  induction N with
  | zero =>
    have h : asym 0 = fun _ => 0 := by
      funext z
      simp [asym, asymSum]
    rw [h]
    refine (hasDerivAt_const x (0 : ℝ)).congr_deriv ?_
    simp [asymCoeff]
  | succ N ih =>
    have he : asym (N + 1) = fun z => asym N z +
        scale / 2 * (asymCoeff N : ℝ) * (exp (-z ^ 2) * z⁻¹ ^ (2 * N + 1)) := by
      funext z
      simp only [asym, asymSum]
      rw [sum_range_succ]
      ring
    rw [he]
    have ht := (hexp.mul (hasDerivAt_inv_pow (2 * N + 1) hx)).const_mul
      (scale / 2 * (asymCoeff N : ℝ))
    refine (ih.add ht).congr_deriv ?_
    have hxi : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
    rw [asymCoeff]
    have h3 : x * x⁻¹ ^ (2 * N + 1) = x⁻¹ ^ (2 * N) := by
      rw [pow_succ]
      calc x * (x⁻¹ ^ (2 * N) * x⁻¹) = x⁻¹ ^ (2 * N) * (x * x⁻¹) := by ring
        _ = x⁻¹ ^ (2 * N) := by rw [hxi, mul_one]
    push_cast
    linear_combination (-(scale * (asymCoeff N : ℝ) * exp (-x ^ 2))) * h3

theorem tendsto_asym (N : ℕ) : Tendsto (asym N) atTop (𝓝 0) := by
  have he : Tendsto (fun x : ℝ => exp (-x ^ 2)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  have hp : Continuous fun u : ℝ => ∑ n ∈ range N, (asymCoeff n : ℝ) * u ^ (2 * n + 1) := by
    fun_prop
  have hs : Tendsto (asymSum N) atTop (𝓝 0) := by
    have h := (hp.tendsto 0).comp tendsto_inv_atTop_zero
    simp only [zero_pow (Nat.succ_ne_zero _), mul_zero, sum_const_zero] at h
    exact h
  have h := (he.const_mul (scale / 2)).mul hs
  simp only [mul_zero] at h
  exact h

/-- The alternating asymptotic bounds: for `x > 0`, `asym N x` is at most `erfc x` for even `N`
and at least `erfc x` for odd `N`. -/
theorem erfc_asym (N : ℕ) {x : ℝ} (hx : 0 < x) : 0 ≤ (-1) ^ N * (erfc x - asym N x) := by
  have hd : ∀ z, 0 < z → HasDerivAt (fun z => (-1) ^ N * (erfc z - asym N z))
      ((-1) ^ N * -(scale * (asymCoeff N : ℝ) * exp (-z ^ 2) * z⁻¹ ^ (2 * N))) z := by
    intro z hz
    have h := ((hasDerivAt_erfc z).sub (hasDerivAt_asym N hz.ne')).const_mul ((-1 : ℝ) ^ N)
    refine h.congr_deriv ?_
    ring
  have hanti : AntitoneOn (fun z => (-1) ^ N * (erfc z - asym N z)) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
    · rw [interior_Ioi]
      exact fun z hz => (hd z hz).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Ioi] at hz
      rw [(hd z hz).deriv]
      have hs := asymCoeff_sign N
      have hz' : 0 ≤ z⁻¹ ^ (2 * N) := pow_nonneg (inv_nonneg.mpr (le_of_lt hz)) _
      have h : (-1) ^ N * -(scale * (asymCoeff N : ℝ) * exp (-z ^ 2) * z⁻¹ ^ (2 * N)) =
          -(scale * ((-1) ^ N * (asymCoeff N : ℝ)) * exp (-z ^ 2) * z⁻¹ ^ (2 * N)) := by ring
      rw [h, neg_nonpos]
      exact mul_nonneg (mul_nonneg (mul_nonneg scale_pos.le hs) (exp_pos _).le) hz'
  have ht : Tendsto (fun z => (-1) ^ N * (erfc z - asym N z)) atTop (𝓝 0) := by
    have h := (tendsto_erfc.sub (tendsto_asym N)).const_mul ((-1 : ℝ) ^ N)
    simpa only [sub_zero, mul_zero] using h
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop x] with z hz
  exact hanti hx (lt_of_lt_of_le hx hz) hz

/-! ### The scaled complement and its differential equation -/

theorem hasDerivAt_erfcx (x : ℝ) : HasDerivAt erfcx (2 * x * erfcx x - scale) x := by
  have h := (hasDerivAt_exp_sq x).mul (hasDerivAt_erfc x)
  have hf : erfcx = fun x => exp (x ^ 2) * erfc x := rfl
  rw [hf]
  refine h.congr_deriv ?_
  have hx : exp (x ^ 2) * exp (-x ^ 2) = 1 := by rw [← exp_add]; simp
  linear_combination (-scale) * hx

theorem erfcx_pos (x : ℝ) : 0 < erfcx x := mul_pos (exp_pos _) (erfc_pos x)

theorem erfc_eq (x : ℝ) : erfc x = exp (-x ^ 2) * erfcx x := by
  rw [erfcx, ← mul_assoc, ← exp_add]
  simp

theorem erfc_strictAnti : StrictAnti erfc := fun _ _ h => by
  have := erf_strictMono h
  simp only [erfc]
  linarith

/-- The asymptotic bounds for `erfcx`: for `x > 0`, `(1/√π) asymSum N x` is at most `erfcx x`
for even `N` and at least `erfcx x` for odd `N`. -/
theorem erfcx_asym (N : ℕ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (-1) ^ N * (erfcx x - scale / 2 * asymSum N x) := by
  have h := erfc_asym N hx
  rw [erfc_eq, asym] at h
  have he : (-1) ^ N * (exp (-x ^ 2) * erfcx x - scale / 2 * exp (-x ^ 2) * asymSum N x) =
      exp (-x ^ 2) * ((-1) ^ N * (erfcx x - scale / 2 * asymSum N x)) := by ring
  rw [he] at h
  exact (mul_nonneg_iff_of_pos_left (exp_pos _)).mp h

/-- A function `p` with `|p' - 2 x p + 2/√π| ≤ η` on `[a, b]`, `0 ≤ a`, and `|erfcx b - p b| ≤ σ`
stays within `σ + η (b - x)` of `erfcx` on `[a, b]`.  Errors shrink toward smaller `x`, since the
equation's solutions grow like `exp (x²)`. -/
theorem erfcx_backward (p p' : ℝ → ℝ) {a b σ η : ℝ} (ha : 0 ≤ a)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (p' x) x)
    (hδ : ∀ x ∈ Icc a b, |p' x - 2 * x * p x + scale| ≤ η)
    (hb : |erfcx b - p b| ≤ σ) {x : ℝ} (hx : x ∈ Icc a b) :
    |erfcx x - p x| ≤ σ + η * (b - x) := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hδ x hx)
  set w := fun u => exp (-u ^ 2) * (erfcx u - p u) with hw
  have hexp := hasDerivAt_gauss
  have hwd : ∀ u ∈ Icc x b, HasDerivAt w
      (-(exp (-u ^ 2) * (p' u - 2 * u * p u + scale))) u := by
    intro u hu
    have hu' : u ∈ Icc a b := ⟨hx.1.trans hu.1, hu.2⟩
    have h := (hexp u).mul ((hasDerivAt_erfcx u).sub (hp u hu'))
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  have hbound : ∀ u ∈ Ico x b, ‖-(exp (-u ^ 2) * (p' u - 2 * u * p u + scale))‖ ≤
      exp (-x ^ 2) * η := by
    intro u hu
    have hu' : u ∈ Icc a b := ⟨hx.1.trans hu.1, hu.2.le⟩
    rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (exp_pos _)]
    have hx0 : 0 ≤ x := ha.trans hx.1
    have hle : exp (-u ^ 2) ≤ exp (-x ^ 2) := by
      apply exp_le_exp.mpr
      nlinarith [hu.1]
    exact mul_le_mul hle (hδ u hu') (abs_nonneg _) (exp_pos _).le
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun u hu => (hwd u hu).hasDerivWithinAt) hbound b ⟨hx.2, le_rfl⟩
  rw [Real.norm_eq_abs] at hmv
  have hwx : erfcx x - p x = exp (x ^ 2) * w x := by
    simp only [hw]
    rw [← mul_assoc, ← exp_add]
    simp
  have hwb : |w b| ≤ exp (-b ^ 2) * σ := by
    simp only [hw]
    rw [abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul_of_nonneg_left hb (exp_pos _).le
  have hwx' : |w x| ≤ exp (-b ^ 2) * σ + exp (-x ^ 2) * η * (b - x) := by
    have h := abs_sub_abs_le_abs_sub (w x) (w b)
    rw [abs_sub_comm] at hmv
    linarith
  rw [hwx, abs_mul, abs_of_pos (exp_pos _)]
  have hσ : 0 ≤ σ := (abs_nonneg _).trans hb
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hxb : exp (x ^ 2) * exp (-b ^ 2) ≤ 1 := by
    rw [← exp_add]
    apply exp_le_one_iff.mpr
    nlinarith [hx.2]
  have hxx : exp (x ^ 2) * exp (-x ^ 2) = 1 := by rw [← exp_add]; simp
  calc exp (x ^ 2) * |w x| ≤ exp (x ^ 2) * (exp (-b ^ 2) * σ + exp (-x ^ 2) * η * (b - x)) :=
        mul_le_mul_of_nonneg_left hwx' (exp_pos _).le
    _ = (exp (x ^ 2) * exp (-b ^ 2)) * σ + (exp (x ^ 2) * exp (-x ^ 2)) * η * (b - x) := by
        ring
    _ ≤ 1 * σ + 1 * η * (b - x) := by
        rw [hxx]
        have hbx : 0 ≤ b - x := by linarith [hx.2]
        nlinarith
    _ = σ + η * (b - x) := by ring

#print axioms scale_bounds
#print axioms hasDerivAt_erf
#print axioms erf_neg
#print axioms erf_strictMono
#print axioms tendsto_erf
#print axioms erf_lt_one
#print axioms erfc_pos
#print axioms exp_nonpos_remainder
#print axioms erf_series
#print axioms erfc_asym
#print axioms hasDerivAt_erfcx
#print axioms erfcx_backward
#print axioms erfc_eq
#print axioms erfcx_asym

end LeanExe.ProofKit.RealErf
