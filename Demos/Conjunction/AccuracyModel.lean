import Demos.Conjunction.Model
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IntermediateValue

/-!
The radius at a probability.  The probability `pc` of the disk of radius `R` about the origin is
zero at `R = 0`, does not change when the two axes are exchanged, and is continuous and strictly
increasing in `R` on `[0, ∞)` for a positive definite covariance.  `linearProb` is the probability
that a normal error on a line lies in `[-L, L]`, and it has the same properties for a positive
variance.  `root_between` turns two radii, one whose probability lies below `q` and one whose
probability is at least `q`, into the unique radius of probability `q` between them.
-/

namespace Demos.Conjunction.Model

open Real MeasureTheory Set LeanExe.ProofKit

theorem isCompact_disk (r : ℝ) (hr : 0 ≤ r) : IsCompact (disk r) := by
  have hclosed : IsClosed (disk r) :=
    isClosed_le (f := fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (g := fun _ => r ^ 2) (by fun_prop)
      continuous_const
  have hsub : disk r ⊆ Icc (-r) r ×ˢ Icc (-r) r := by
    intro p hp
    have hp' : p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2 := hp
    exact ⟨abs_le.mp (abs_le_of_sq_le_sq (by nlinarith [sq_nonneg p.2]) hr),
      abs_le.mp (abs_le_of_sq_le_sq (by nlinarith [sq_nonneg p.1]) hr)⟩
  exact IsCompact.of_isClosed_subset (isCompact_Icc.prod isCompact_Icc) hclosed hsub

theorem measurableSet_disk (r : ℝ) : MeasurableSet (disk r) :=
  (isClosed_le (f := fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (g := fun _ => r ^ 2) (by fun_prop)
    continuous_const).measurableSet

/-- The probability of the disk of radius zero is zero. -/
theorem pc_zero (m1 m2 c11 c12 c22 : ℝ) : pc m1 m2 c11 c12 c22 0 = 0 := by
  have hd : disk 0 ⊆ Icc 0 0 ×ˢ (univ : Set ℝ) := by
    intro p hp
    have hp' : p.1 ^ 2 + p.2 ^ 2 ≤ 0 ^ 2 := hp
    have h1 : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
    exact ⟨⟨h1.ge, h1.le⟩, mem_univ _⟩
  have h0 : (volume : Measure (ℝ × ℝ)) (disk 0) = 0 := by
    refine measure_mono_null hd ?_
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, sub_self, ENNReal.ofReal_zero,
      zero_mul]
  exact setIntegral_measure_zero _ h0

/-- The probability does not change when the two axes are exchanged. -/
theorem pc_swap (m1 m2 c11 c12 c22 r : ℝ) :
    pc m1 m2 c11 c12 c22 r = pc m2 m1 c22 c12 c11 r := by
  have hdens : ∀ p : ℝ × ℝ,
      density m2 m1 c22 c12 c11 p.swap = density m1 m2 c11 c12 c22 p := by
    intro p
    unfold density det
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring_nf
  have hdisk : ∀ p : ℝ × ℝ, p.swap ∈ disk r ↔ p ∈ disk r := by
    intro p
    show p.2 ^ 2 + p.1 ^ 2 ≤ r ^ 2 ↔ p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2
    rw [add_comm]
  have hind : ∀ p : ℝ × ℝ, (disk r).indicator (density m2 m1 c22 c12 c11) p.swap =
      (disk r).indicator (density m1 m2 c11 c12 c22) p := by
    intro p
    by_cases hp : p ∈ disk r
    · rw [indicator_of_mem ((hdisk p).mpr hp), indicator_of_mem hp, hdens]
    · rw [indicator_of_notMem (fun h => hp ((hdisk p).mp h)), indicator_of_notMem hp]
  unfold pc
  rw [← integral_indicator (measurableSet_disk r), ← integral_indicator (measurableSet_disk r),
    Measure.volume_eq_prod]
  calc ∫ p, (disk r).indicator (density m1 m2 c11 c12 c22) p ∂(volume.prod volume)
      = ∫ p, (disk r).indicator (density m2 m1 c22 c12 c11) p.swap ∂(volume.prod volume) :=
        congrArg (fun g : ℝ × ℝ → ℝ => ∫ p, g p ∂(volume.prod volume))
          (funext fun p => (hind p).symm)
    _ = ∫ p, (disk r).indicator (density m2 m1 c22 c12 c11) p ∂(volume.prod volume) :=
        integral_prod_swap _

/-- The density is positive for a positive definite covariance. -/
theorem density_pos (m1 m2 c11 c12 c22 : ℝ) (hd : 0 < det c11 c12 c22) (p : ℝ × ℝ) :
    0 < density m1 m2 c11 c12 c22 p := by
  unfold density
  have : 0 < 2 * π * √(det c11 c12 c22) :=
    mul_pos (mul_pos two_pos pi_pos) (Real.sqrt_pos.mpr hd)
  positivity

/-- For a positive definite covariance, the probability strictly increases with the radius. -/
theorem pc_strictMonoOn (m1 m2 c11 c12 c22 : ℝ) (hd : 0 < det c11 c12 c22) :
    StrictMonoOn (pc m1 m2 c11 c12 c22) (Ici 0) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := ha
  have hb0 : 0 ≤ b := hb
  have hsub : disk a ⊆ disk b := by
    intro p hp
    have hp' : p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2 := hp
    show p.1 ^ 2 + p.2 ^ 2 ≤ b ^ 2
    nlinarith
  have hint : IntegrableOn (density m1 m2 c11 c12 c22) (disk b) :=
    (continuous_density m1 m2 c11 c12 c22).continuousOn.integrableOn_compact
      (isCompact_disk b hb0)
  have hdiff := setIntegral_sdiff₀ (measurableSet_disk a).nullMeasurableSet hint hsub
  set c := (a + b) / 2
  set δ := (b - a) / 4
  have hδ : 0 < δ := by simp only [δ]; linarith
  have hbox : Ioo (c - δ) (c + δ) ×ˢ Ioo (-δ) δ ⊆
      Function.support (density m1 m2 c11 c12 c22) ∩ (disk b \ disk a) := by
    rintro ⟨x, y⟩ ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
    refine ⟨(density_pos m1 m2 c11 c12 c22 hd _).ne', ?_, ?_⟩
    · show x ^ 2 + y ^ 2 ≤ b ^ 2
      have hy : y ^ 2 ≤ δ ^ 2 := by nlinarith
      have hx0 : 0 < x := by simp only [c, δ] at hx1; linarith
      have hx : x ^ 2 ≤ (c + δ) ^ 2 := by nlinarith
      simp only [c, δ] at hx hy
      nlinarith
    · intro hm
      have hm' : x ^ 2 + y ^ 2 ≤ a ^ 2 := hm
      have hx : a < x := by simp only [c, δ] at hx1; linarith
      nlinarith [sq_nonneg y]
  have hvol : 0 < (volume : Measure (ℝ × ℝ))
      (Function.support (density m1 m2 c11 c12 c22) ∩ (disk b \ disk a)) := by
    refine lt_of_lt_of_le ?_ (measure_mono hbox)
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (by linarith)).ne'
      (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hpos : 0 < ∫ p in disk b \ disk a, density m1 m2 c11 c12 c22 p :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => (density_pos m1 m2 c11 c12 c22 hd p).le)
      (hint.mono_set sdiff_subset)).mpr hvol
  unfold pc
  linarith

theorem continuous_core_uncurry (m1 m2 c11 c12 c22 : ℝ) :
    Continuous (Function.uncurry (core m1 m2 c11 c12 c22)) := by
  show Continuous fun q : ℝ × ℝ => core m1 m2 c11 c12 c22 q.1 q.2
  unfold core condMean
  exact Continuous.mul (by fun_prop)
    (Continuous.add (continuous_erf.comp (by fun_prop)) (continuous_erf.comp (by fun_prop)))

/-- For a positive definite covariance, the probability is continuous in the radius. -/
theorem pc_continuousOn (m1 m2 c11 c12 c22 : ℝ) (hc : 0 < c11) (hd : 0 < det c11 c12 c22) :
    ContinuousOn (pc m1 m2 c11 c12 c22) (Ici 0) := by
  have hf := continuous_core_uncurry m1 m2 c11 c12 c22
  have hG : Continuous fun R : ℝ => (2 * √(2 * π * c11))⁻¹ *
      ((∫ x in (0 : ℝ)..R, core m1 m2 c11 c12 c22 R x) -
        ∫ x in (0 : ℝ)..(-R), core m1 m2 c11 c12 c22 R x) :=
    continuous_const.mul
      ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf
          continuous_id).sub
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf
          continuous_neg))
  refine hG.continuousOn.congr fun R hR => ?_
  have hi : ∀ a b : ℝ, IntervalIntegrable (core m1 m2 c11 c12 c22 R) volume a b := fun a b =>
    (continuous_core m1 m2 c11 c12 c22 R).intervalIntegrable a b
  show pc m1 m2 c11 c12 c22 R = (2 * √(2 * π * c11))⁻¹ *
    ((∫ x in (0 : ℝ)..R, core m1 m2 c11 c12 c22 R x) -
      ∫ x in (0 : ℝ)..(-R), core m1 m2 c11 c12 c22 R x)
  rw [pc_eq m1 m2 c11 c12 c22 R hc hd hR, intervalIntegral.integral_interval_sub_left (hi _ _)
    (hi _ _)]

/-- The normal density of mean `b` and variance `v` on the line. -/
noncomputable def lineDensity (b v x : ℝ) : ℝ :=
  (√(2 * π * v))⁻¹ * exp (-(x - b) ^ 2 / (2 * v))

/-- The probability that a normal error of mean `b` and variance `v` lies in `[-L, L]`. -/
noncomputable def linearProb (b v L : ℝ) : ℝ :=
  ∫ x in Icc (-L) L, lineDensity b v x

/-- The probability of `[-L, L]` as a sum of two error-function values. -/
theorem linearProb_eq (b v L : ℝ) (hv : 0 < v) (hL : 0 ≤ L) :
    linearProb b v L =
      1 / 2 * (RealErf.erf ((L - b) / (√v * √2)) + RealErf.erf ((L + b) / (√v * √2))) := by
  have hpos : 0 < √(2 * π * v) := Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos pi_pos) hv)
  have hneg : (-L - b) / (√v * √2) = -((L + b) / (√v * √2)) := by ring
  unfold linearProb lineDensity
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (neg_le_self hL),
    intervalIntegral.integral_const_mul, gauss_window b v (-L) L hv, hneg, RealErf.erf_neg]
  field_simp
  ring

theorem linearProb_zero (b v : ℝ) : linearProb b v 0 = 0 := by
  unfold linearProb
  exact setIntegral_measure_zero _ (by rw [Real.volume_Icc, neg_zero, sub_self,
    ENNReal.ofReal_zero])

/-- For a positive variance, the probability strictly increases with the half-width. -/
theorem linearProb_strictMonoOn (b v : ℝ) (hv : 0 < v) :
    StrictMonoOn (linearProb b v) (Ici 0) := by
  intro L1 h1 L2 h2 h
  have hk : 0 < √v * √2 := mul_pos (Real.sqrt_pos.mpr hv) (Real.sqrt_pos.mpr two_pos)
  rw [linearProb_eq b v L1 hv h1, linearProb_eq b v L2 hv h2]
  have e1 := RealErf.erf_strictMono (div_lt_div_of_pos_right (by linarith : L1 - b < L2 - b) hk)
  have e2 := RealErf.erf_strictMono (div_lt_div_of_pos_right (by linarith : L1 + b < L2 + b) hk)
  linarith

/-- For a positive variance, the probability is continuous in the half-width. -/
theorem linearProb_continuousOn (b v : ℝ) (hv : 0 < v) :
    ContinuousOn (linearProb b v) (Ici 0) := by
  have hG : Continuous fun L : ℝ =>
      1 / 2 * (RealErf.erf ((L - b) / (√v * √2)) + RealErf.erf ((L + b) / (√v * √2))) :=
    continuous_const.mul
      ((continuous_erf.comp (by fun_prop)).add (continuous_erf.comp (by fun_prop)))
  exact hG.continuousOn.congr fun L hL => linearProb_eq b v L hv hL

/-- A function continuous and strictly increasing on `[0, ∞)`, below `q` at `a ≥ 0` and at least
`q` at `c ≥ 0`, takes the value `q` at exactly one point of `[0, ∞)`, which lies in `(a, c]`. -/
theorem root_between {P : ℝ → ℝ} (hm : StrictMonoOn P (Ici 0)) (hcont : ContinuousOn P (Ici 0))
    {a c q : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hpa : P a < q) (hpc : q ≤ P c) :
    (∃! R, 0 ≤ R ∧ P R = q) ∧ ∀ R, 0 ≤ R → P R = q → a < R ∧ R ≤ c := by
  have hac : a < c := by
    by_contra h
    have := hm.monotoneOn hc ha (not_lt.mp h)
    linarith
  obtain ⟨R, hR, hPR⟩ := intermediate_value_Icc hac.le
    (hcont.mono fun x hx => le_trans ha hx.1) ⟨hpa.le, hpc⟩
  have bounds : ∀ R, 0 ≤ R → P R = q → a < R ∧ R ≤ c := by
    intro R h0 hR
    constructor
    · by_contra h
      have := hm.monotoneOn h0 ha (not_lt.mp h)
      linarith
    · by_contra h
      have := hm hc h0 (not_le.mp h)
      linarith
  refine ⟨⟨R, ⟨ha.trans hR.1, hPR⟩, fun R' hR' => ?_⟩, bounds⟩
  exact hm.injOn hR'.1 (ha.trans hR.1) (hR'.2.trans hPR.symm)

/-- `[lo, hi]` holds the radius of probability `q` under `P`: `0 ≤ lo ≤ hi`, exactly one `R ≥ 0`
has `P R = q`, and that `R` lies in `[lo, hi]`. -/
def RadiusIn (P : ℝ → ℝ) (q lo hi : ℝ) : Prop :=
  0 ≤ lo ∧ lo ≤ hi ∧ (∃! R, 0 ≤ R ∧ P R = q) ∧ ∀ R, 0 ≤ R → P R = q → lo ≤ R ∧ R ≤ hi

theorem radiusIn_of {P : ℝ → ℝ} (hm : StrictMonoOn P (Ici 0)) (hcont : ContinuousOn P (Ici 0))
    {a c q : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hpa : P a < q) (hpc : q ≤ P c) :
    RadiusIn P q a c := by
  obtain ⟨hu, hb⟩ := root_between hm hcont ha hc hpa hpc
  obtain ⟨R, hR, -⟩ := id hu
  obtain ⟨h1, h2⟩ := hb R hR.1 hR.2
  exact ⟨ha, (h1.trans_le h2).le, hu, fun R h0 hR => ⟨(hb R h0 hR).1.le, (hb R h0 hR).2⟩⟩

#print axioms pc_zero
#print axioms pc_swap
#print axioms pc_strictMonoOn
#print axioms pc_continuousOn
#print axioms linearProb_eq
#print axioms linearProb_zero
#print axioms linearProb_strictMonoOn
#print axioms linearProb_continuousOn
#print axioms root_between
#print axioms radiusIn_of

end Demos.Conjunction.Model
