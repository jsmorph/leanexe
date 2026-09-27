import Project.EulerRusanov.StencilNumerical

/-!
# Robust admissibility of the decoded Euler stencil

The preceding numerical module bounds the exact-real assembly of three frozen
artifact flux words against the exact stencil at the decoded binary64 inputs.
This module composes that result with the separately proved `0.1` input bias,
obtains simple componentwise bounds against the rational Sod reference, and
uses explicit slack to prove that both assembled conservative cells remain in
the open Euler admissible set.

No update operation in this module executes in WebAssembly.  It certifies the
real interpretation of the already frozen flux words; direct floating-point
update execution remains a separate artifact.
-/

namespace Project.EulerRusanov.StencilAdmissibility

open Project.EulerRusanov.RealConservative
open Project.EulerRusanov.RealStencil
open Project.EulerRusanov.StencilNumerical

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-! ## Coarse rational-reference bounds -/

noncomputable def rationalQuarterLeft : Vec3 :=
  ![(207 : ℝ) / 256, 9 / 80, 257 / 128]

noncomputable def rationalQuarterRight : Vec3 :=
  ![(81 : ℝ) / 256, 9 / 80, 95 / 128]

/-- Readable common bounds against the rational Sod reference.  They include
both the certified flux error and the exact binary64 input bias. -/
noncomputable def rationalQuarterErrorBudget : Vec3 :=
  ![5 * CodeLib.Numerical.Kernels.f64Epsilon,
    8 * CodeLib.Numerical.Kernels.f64Epsilon,
    13 * CodeLib.Numerical.Kernels.f64Epsilon]

private theorem left_density_error :
    |(decodedTransmissiveStep (1 / 4)).1 0 - (207 : ℝ) / 256| ≤
      5 * CodeLib.Numerical.Kernels.f64Epsilon := by
  have h := decodedQuarterStep_error.1 (0 : Fin 3)
  rw [decodedExactQuarterStep_exact, sodQuarterErrorBudget_exact] at h
  exact h

private theorem left_momentum_error :
    |(decodedTransmissiveStep (1 / 4)).1 1 - (9 : ℝ) / 80| ≤
      8 * CodeLib.Numerical.Kernels.f64Epsilon := by
  have h := decodedQuarterStep_error.1 (1 : Fin 3)
  rw [decodedExactQuarterStep_exact, sodQuarterErrorBudget_exact] at h
  have hmain :
      |(decodedTransmissiveStep (1 / 4)).1 1 -
          ((9 : ℝ) / 80 - tenthRepresentationError / 8)| ≤
        7 * CodeLib.Numerical.Kernels.f64Epsilon := by
    simpa using h
  rw [show
    (decodedTransmissiveStep (1 / 4)).1 1 - (9 : ℝ) / 80 =
      ((decodedTransmissiveStep (1 / 4)).1 1 -
        ((9 : ℝ) / 80 - tenthRepresentationError / 8)) -
          tenthRepresentationError / 8 by ring]
  calc
    |((decodedTransmissiveStep (1 / 4)).1 1 -
          ((9 : ℝ) / 80 - tenthRepresentationError / 8)) -
        tenthRepresentationError / 8| ≤
        |(decodedTransmissiveStep (1 / 4)).1 1 -
          ((9 : ℝ) / 80 - tenthRepresentationError / 8)| +
          |tenthRepresentationError / 8| := by
            simpa [sub_eq_add_neg] using
              (abs_add_le
                ((decodedTransmissiveStep (1 / 4)).1 1 -
                  ((9 : ℝ) / 80 - tenthRepresentationError / 8))
                (-(tenthRepresentationError / 8)))
    _ ≤ 7 * CodeLib.Numerical.Kernels.f64Epsilon +
          |tenthRepresentationError / 8| :=
        add_le_add hmain (le_refl _)
    _ ≤ 8 * CodeLib.Numerical.Kernels.f64Epsilon := by
      norm_num [tenthRepresentationError,
        CodeLib.Numerical.Kernels.f64Epsilon]

private theorem left_energy_error :
    |(decodedTransmissiveStep (1 / 4)).1 2 - (257 : ℝ) / 128| ≤
      13 * CodeLib.Numerical.Kernels.f64Epsilon := by
  have h := decodedQuarterStep_error.1 (2 : Fin 3)
  rw [decodedExactQuarterStep_exact, sodQuarterErrorBudget_exact] at h
  have hmain :
      |(decodedTransmissiveStep (1 / 4)).1 2 -
          ((257 : ℝ) / 128 + 35 * tenthRepresentationError / 64)| ≤
        (25 / 2 : ℝ) * CodeLib.Numerical.Kernels.f64Epsilon := by
    simpa using h
  rw [show
    (decodedTransmissiveStep (1 / 4)).1 2 - (257 : ℝ) / 128 =
      ((decodedTransmissiveStep (1 / 4)).1 2 -
        ((257 : ℝ) / 128 + 35 * tenthRepresentationError / 64)) +
          35 * tenthRepresentationError / 64 by ring]
  calc
    |((decodedTransmissiveStep (1 / 4)).1 2 -
          ((257 : ℝ) / 128 + 35 * tenthRepresentationError / 64)) +
        35 * tenthRepresentationError / 64| ≤
        |(decodedTransmissiveStep (1 / 4)).1 2 -
          ((257 : ℝ) / 128 + 35 * tenthRepresentationError / 64)| +
          |35 * tenthRepresentationError / 64| := abs_add_le _ _
    _ ≤ (25 / 2 : ℝ) * CodeLib.Numerical.Kernels.f64Epsilon +
          |35 * tenthRepresentationError / 64| :=
        add_le_add hmain (le_refl _)
    _ ≤ 13 * CodeLib.Numerical.Kernels.f64Epsilon := by
      norm_num [tenthRepresentationError,
        CodeLib.Numerical.Kernels.f64Epsilon]

private theorem right_density_error :
    |(decodedTransmissiveStep (1 / 4)).2 0 - (81 : ℝ) / 256| ≤
      5 * CodeLib.Numerical.Kernels.f64Epsilon := by
  have h := decodedQuarterStep_error.2 (0 : Fin 3)
  rw [decodedExactQuarterStep_exact, sodQuarterErrorBudget_exact] at h
  exact h

private theorem right_momentum_error :
    |(decodedTransmissiveStep (1 / 4)).2 1 - (9 : ℝ) / 80| ≤
      8 * CodeLib.Numerical.Kernels.f64Epsilon := by
  have h := decodedQuarterStep_error.2 (1 : Fin 3)
  rw [decodedExactQuarterStep_exact, sodQuarterErrorBudget_exact] at h
  have hmain :
      |(decodedTransmissiveStep (1 / 4)).2 1 -
          ((9 : ℝ) / 80 - tenthRepresentationError / 8)| ≤
        7 * CodeLib.Numerical.Kernels.f64Epsilon := by
    simpa using h
  rw [show
    (decodedTransmissiveStep (1 / 4)).2 1 - (9 : ℝ) / 80 =
      ((decodedTransmissiveStep (1 / 4)).2 1 -
        ((9 : ℝ) / 80 - tenthRepresentationError / 8)) -
          tenthRepresentationError / 8 by ring]
  calc
    |((decodedTransmissiveStep (1 / 4)).2 1 -
          ((9 : ℝ) / 80 - tenthRepresentationError / 8)) -
        tenthRepresentationError / 8| ≤
        |(decodedTransmissiveStep (1 / 4)).2 1 -
          ((9 : ℝ) / 80 - tenthRepresentationError / 8)| +
          |tenthRepresentationError / 8| := by
            simpa [sub_eq_add_neg] using
              (abs_add_le
                ((decodedTransmissiveStep (1 / 4)).2 1 -
                  ((9 : ℝ) / 80 - tenthRepresentationError / 8))
                (-(tenthRepresentationError / 8)))
    _ ≤ 7 * CodeLib.Numerical.Kernels.f64Epsilon +
          |tenthRepresentationError / 8| :=
        add_le_add hmain (le_refl _)
    _ ≤ 8 * CodeLib.Numerical.Kernels.f64Epsilon := by
      norm_num [tenthRepresentationError,
        CodeLib.Numerical.Kernels.f64Epsilon]

private theorem right_energy_error :
    |(decodedTransmissiveStep (1 / 4)).2 2 - (95 : ℝ) / 128| ≤
      13 * CodeLib.Numerical.Kernels.f64Epsilon := by
  have h := decodedQuarterStep_error.2 (2 : Fin 3)
  rw [decodedExactQuarterStep_exact, sodQuarterErrorBudget_exact] at h
  have hmain :
      |(decodedTransmissiveStep (1 / 4)).2 2 -
          ((95 : ℝ) / 128 + 125 * tenthRepresentationError / 64)| ≤
        (25 / 2 : ℝ) * CodeLib.Numerical.Kernels.f64Epsilon := by
    simpa using h
  rw [show
    (decodedTransmissiveStep (1 / 4)).2 2 - (95 : ℝ) / 128 =
      ((decodedTransmissiveStep (1 / 4)).2 2 -
        ((95 : ℝ) / 128 + 125 * tenthRepresentationError / 64)) +
          125 * tenthRepresentationError / 64 by ring]
  calc
    |((decodedTransmissiveStep (1 / 4)).2 2 -
          ((95 : ℝ) / 128 + 125 * tenthRepresentationError / 64)) +
        125 * tenthRepresentationError / 64| ≤
        |(decodedTransmissiveStep (1 / 4)).2 2 -
          ((95 : ℝ) / 128 + 125 * tenthRepresentationError / 64)| +
          |125 * tenthRepresentationError / 64| := abs_add_le _ _
    _ ≤ (25 / 2 : ℝ) * CodeLib.Numerical.Kernels.f64Epsilon +
          |125 * tenthRepresentationError / 64| :=
        add_le_add hmain (le_refl _)
    _ ≤ 13 * CodeLib.Numerical.Kernels.f64Epsilon := by
      norm_num [tenthRepresentationError,
        CodeLib.Numerical.Kernels.f64Epsilon]

/-- Both assembled cells satisfy common componentwise bounds against the
rational `p = 1/10` Sod quarter-step. -/
theorem decodedQuarterStep_rational_error :
    ComponentwiseError
        (decodedTransmissiveStep (1 / 4)).1
        rationalQuarterLeft rationalQuarterErrorBudget ∧
      ComponentwiseError
        (decodedTransmissiveStep (1 / 4)).2
        rationalQuarterRight rationalQuarterErrorBudget := by
  constructor
  · intro i
    fin_cases i
    · exact left_density_error
    · exact left_momentum_error
    · exact left_energy_error
  · intro i
    fin_cases i
    · exact right_density_error
    · exact right_momentum_error
    · exact right_energy_error

/-! ## Robust open-set margins -/

private theorem robust_admissible
    (U : Vec3)
    (hdensity : (5 : ℝ) / 16 < U 0)
    (hmomentum : |U 1| < (1 : ℝ) / 8)
    (henergy : (1 : ℝ) / 2 < U 2) :
    (19 : ℝ) / 40 < internalEnergy U ∧
      (19 : ℝ) / 100 < pressure U ∧ Admissible U := by
  have hmomentumSq : U 1 ^ 2 < (1 : ℝ) / 64 := by
    have hpositiveSum : 0 < (1 : ℝ) / 8 + |U 1| := by
      nlinarith [abs_nonneg (U 1)]
    have hproduct :
        0 < ((1 : ℝ) / 8 - |U 1|) * ((1 : ℝ) / 8 + |U 1|) :=
      mul_pos (sub_pos.mpr hmomentum) hpositiveSum
    nlinarith [sq_abs (U 1)]
  have hdenominator : 0 < 2 * U 0 := by linarith
  have hkinetic : U 1 ^ 2 / (2 * U 0) < (1 : ℝ) / 40 := by
    apply (div_lt_iff₀ hdenominator).2
    nlinarith
  have hinternal : (19 : ℝ) / 40 < internalEnergy U := by
    change (19 : ℝ) / 40 < U 2 - U 1 ^ 2 / (2 * U 0)
    linarith
  have hpressure : (19 : ℝ) / 100 < pressure U := by
    change (19 : ℝ) / 100 < ((2 : ℝ) / 5) * internalEnergy U
    nlinarith
  refine ⟨hinternal, hpressure, ?_⟩
  refine ⟨?_, ?_⟩
  · change 0 < U 0
    linarith
  · exact lt_trans (by norm_num) hpressure

private theorem momentum_abs_lt_of_error
    (U : Vec3)
    (herror : |U 1 - (9 : ℝ) / 80| ≤
      8 * CodeLib.Numerical.Kernels.f64Epsilon) :
    |U 1| < (1 : ℝ) / 8 := by
  calc
    |U 1| = |(U 1 - (9 : ℝ) / 80) + (9 : ℝ) / 80| := by ring_nf
    _ ≤ |U 1 - (9 : ℝ) / 80| + |(9 : ℝ) / 80| := abs_add_le _ _
    _ ≤ 8 * CodeLib.Numerical.Kernels.f64Epsilon + |(9 : ℝ) / 80| :=
      add_le_add herror (le_refl _)
    _ < (1 : ℝ) / 8 := by
      norm_num [CodeLib.Numerical.Kernels.f64Epsilon]

private theorem density_gt_of_error
    (U : Vec3) (reference : ℝ)
    (href : (81 : ℝ) / 256 ≤ reference)
    (herror : |U 0 - reference| ≤
      5 * CodeLib.Numerical.Kernels.f64Epsilon) :
    (5 : ℝ) / 16 < U 0 := by
  have hlower := (abs_le.mp herror).1
  norm_num [CodeLib.Numerical.Kernels.f64Epsilon] at hlower ⊢
  linarith

private theorem energy_gt_of_error
    (U : Vec3) (reference : ℝ)
    (href : (95 : ℝ) / 128 ≤ reference)
    (herror : |U 2 - reference| ≤
      13 * CodeLib.Numerical.Kernels.f64Epsilon) :
    (1 : ℝ) / 2 < U 2 := by
  have hlower := (abs_le.mp herror).1
  norm_num [CodeLib.Numerical.Kernels.f64Epsilon] at hlower ⊢
  linarith

/-- The left assembled cell has explicit density, momentum, energy, internal
energy, and pressure slack, and is therefore admissible. -/
theorem decodedQuarterStep_left_margins :
    (5 : ℝ) / 16 < density (decodedTransmissiveStep (1 / 4)).1 ∧
      |momentum (decodedTransmissiveStep (1 / 4)).1| < (1 : ℝ) / 8 ∧
      (1 : ℝ) / 2 < totalEnergy (decodedTransmissiveStep (1 / 4)).1 ∧
      (19 : ℝ) / 40 < internalEnergy (decodedTransmissiveStep (1 / 4)).1 ∧
      (19 : ℝ) / 100 < pressure (decodedTransmissiveStep (1 / 4)).1 := by
  have herror := decodedQuarterStep_rational_error.1
  have hrho := density_gt_of_error
    (decodedTransmissiveStep (1 / 4)).1 ((207 : ℝ) / 256)
    (by norm_num) (herror 0)
  have hm := momentum_abs_lt_of_error
    (decodedTransmissiveStep (1 / 4)).1 (herror 1)
  have hE := energy_gt_of_error
    (decodedTransmissiveStep (1 / 4)).1 ((257 : ℝ) / 128)
    (by norm_num) (herror 2)
  have hrobust := robust_admissible
    (decodedTransmissiveStep (1 / 4)).1 hrho hm hE
  exact ⟨hrho, hm, hE, hrobust.1, hrobust.2.1⟩

/-- The right assembled cell has the same explicit open-set margins. -/
theorem decodedQuarterStep_right_margins :
    (5 : ℝ) / 16 < density (decodedTransmissiveStep (1 / 4)).2 ∧
      |momentum (decodedTransmissiveStep (1 / 4)).2| < (1 : ℝ) / 8 ∧
      (1 : ℝ) / 2 < totalEnergy (decodedTransmissiveStep (1 / 4)).2 ∧
      (19 : ℝ) / 40 < internalEnergy (decodedTransmissiveStep (1 / 4)).2 ∧
      (19 : ℝ) / 100 < pressure (decodedTransmissiveStep (1 / 4)).2 := by
  have herror := decodedQuarterStep_rational_error.2
  have hrho := density_gt_of_error
    (decodedTransmissiveStep (1 / 4)).2 ((81 : ℝ) / 256)
    (by norm_num) (herror 0)
  have hm := momentum_abs_lt_of_error
    (decodedTransmissiveStep (1 / 4)).2 (herror 1)
  have hE := energy_gt_of_error
    (decodedTransmissiveStep (1 / 4)).2 ((95 : ℝ) / 128)
    (by norm_num) (herror 2)
  have hrobust := robust_admissible
    (decodedTransmissiveStep (1 / 4)).2 hrho hm hE
  exact ⟨hrho, hm, hE, hrobust.1, hrobust.2.1⟩

/-- Both exact-real cells assembled from the three frozen artifact flux rows
remain in the open Euler admissible set. -/
theorem decodedQuarterStep_admissible :
    Admissible (decodedTransmissiveStep (1 / 4)).1 ∧
      Admissible (decodedTransmissiveStep (1 / 4)).2 := by
  constructor
  · exact (robust_admissible _
      decodedQuarterStep_left_margins.1
      decodedQuarterStep_left_margins.2.1
      decodedQuarterStep_left_margins.2.2.1).2.2
  · exact (robust_admissible _
      decodedQuarterStep_right_margins.1
      decodedQuarterStep_right_margins.2.1
      decodedQuarterStep_right_margins.2.2.1).2.2

#print axioms decodedQuarterStep_rational_error
#print axioms decodedQuarterStep_left_margins
#print axioms decodedQuarterStep_right_margins
#print axioms decodedQuarterStep_admissible

end Project.EulerRusanov.StencilAdmissibility
