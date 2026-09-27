import Project.EulerRusanov.Bounds
import Project.EulerRusanov.ScaledRoundoff
import CodeLib.Numerical.ErrorComposition
import CodeLib.Numerical.Kernels

/-!
# Numerical contract for the guarded Euler--Rusanov bit model

This file proves the numerical part of the case independently of WebAssembly
execution.  All arithmetic words are interpreted by Talos's pure binary64
model.  The raw-word guard is discharged by `Bounds`; every rounded addition
and multiplication is discharged by the scale-aware lemmas in
`ScaledRoundoff`.

The final energy addition deserves special mention.  Bounding its mean and
dissipation operands independently is too weak: `29/16 + 147/64 > 4`.  The
proof instead uses the correlation between energy and energy flux.  If

`E = (5/2)p + (1/2)rho*u^2` and `H = E + p`,

then the guarded domain gives `p <= (2/5)E` and hence
`|H*u| <= (7/10)E`.  This bounds the *combined* exact Rusanov energy flux by
`1029/320 < 13/4`; the accumulated operand error then leaves strict room
below four for the last modeled addition.
-/

namespace Project.EulerRusanov.Numerical

open Wasm
open Project.EulerRusanov

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

private noncomputable def epsilon : ℝ :=
  CodeLib.Numerical.Kernels.f64Epsilon

/-! ## A small scale-aware error-composition interface -/

/-- A finite binary64 word approximating an exact real target.  Both the
represented value and the target carry explicit magnitude bounds; keeping
the two bounds separate is what makes all overflow premises auditable. -/
private structure Approx
    (bits : UInt64) (target error valueBound targetBound : ℝ) : Prop where
  finite : CodeLib.IEEE64.Finite bits
  error_le : |CodeLib.IEEE64.value bits - target| ≤ error
  value_abs : |CodeLib.IEEE64.value bits| ≤ valueBound
  target_abs : |target| ≤ targetBound

private theorem Approx.exact (bits : UInt64) (bound : ℝ)
    (hfinite : CodeLib.IEEE64.Finite bits)
    (hbound : |CodeLib.IEEE64.value bits| ≤ bound) :
    Approx bits (CodeLib.IEEE64.value bits) 0 bound bound := by
  exact ⟨hfinite, by simp, hbound, hbound⟩

/-- Replace algebraically generated budgets by simpler outward-rounded
rational budgets.  The value bound is re-established from target headroom,
so this lemma can also sharpen the crude sum/product magnitude bound. -/
private theorem Approx.normalize
    (h : Approx bits target error valueBound targetBound)
    (newError newValueBound newTargetBound : ℝ)
    (herror : error ≤ newError)
    (htarget : targetBound ≤ newTargetBound)
    (hheadroom : newTargetBound + newError ≤ newValueBound) :
    Approx bits target newError newValueBound newTargetBound := by
  refine ⟨h.finite, h.error_le.trans herror, ?_, h.target_abs.trans htarget⟩
  rw [show CodeLib.IEEE64.value bits =
      (CodeLib.IEEE64.value bits - target) + target by ring]
  calc
    |(CodeLib.IEEE64.value bits - target) + target| ≤
        |CodeLib.IEEE64.value bits - target| + |target| := abs_add_le _ _
    _ ≤ newError + newTargetBound :=
      add_le_add (h.error_le.trans herror) (h.target_abs.trans htarget)
    _ = newTargetBound + newError := add_comm _ _
    _ ≤ newValueBound := hheadroom

/-- Version of `normalize` with an independently established target bound.
This is essential for state differences: interval information is sharper
than the triangle inequality on the two state magnitudes. -/
private theorem Approx.withBounds
    (h : Approx bits target error valueBound targetBound)
    (newError newValueBound newTargetBound : ℝ)
    (herror : error ≤ newError)
    (htarget : |target| ≤ newTargetBound)
    (hheadroom : newTargetBound + newError ≤ newValueBound) :
    Approx bits target newError newValueBound newTargetBound := by
  refine ⟨h.finite, h.error_le.trans herror, ?_, htarget⟩
  rw [show CodeLib.IEEE64.value bits =
      (CodeLib.IEEE64.value bits - target) + target by ring]
  calc
    |(CodeLib.IEEE64.value bits - target) + target| ≤
        |CodeLib.IEEE64.value bits - target| + |target| := abs_add_le _ _
    _ ≤ newError + newTargetBound :=
      add_le_add (h.error_le.trans herror) htarget
    _ = newTargetBound + newError := add_comm _ _
    _ ≤ newValueBound := hheadroom

private theorem approx_add
    (ha : Approx a exactA errorA valueBoundA targetBoundA)
    (hb : Approx b exactB errorB valueBoundB targetBoundB)
    (hrange : valueBoundA + valueBoundB < 4) :
    Approx (IEEE64.add a b) (exactA + exactB)
      (epsilon + errorA + errorB)
      (epsilon + valueBoundA + valueBoundB)
      (targetBoundA + targetBoundB) := by
  have hsum : |CodeLib.IEEE64.value a + CodeLib.IEEE64.value b| < (4 : ℝ) := by
    calc
      |CodeLib.IEEE64.value a + CodeLib.IEEE64.value b| ≤
          |CodeLib.IEEE64.value a| + |CodeLib.IEEE64.value b| :=
        abs_add_le _ _
      _ ≤ valueBoundA + valueBoundB := add_le_add ha.value_abs hb.value_abs
      _ < 4 := hrange
  have hround :=
    ScaledRoundoff.add_real_error_of_exact_sum_lt_four a b
      ha.finite hb.finite hsum
  have hroundError :
      |CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)| ≤ epsilon := by
    simpa [epsilon, CodeLib.Numerical.Kernels.f64Epsilon,
      CodeLib.IEEE64.arithmeticEpsilon] using hround.2
  have hinputs := CodeLib.Numerical.sum_perturbations ha.error_le hb.error_le
  refine ⟨hround.1, ?_, ?_, ?_⟩
  · rw [show CodeLib.IEEE64.value (IEEE64.add a b) - (exactA + exactB) =
        (CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)) +
        ((CodeLib.IEEE64.value a + CodeLib.IEEE64.value b) -
          (exactA + exactB)) by ring]
    calc
      |(CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)) +
        ((CodeLib.IEEE64.value a + CodeLib.IEEE64.value b) -
          (exactA + exactB))| ≤
          |CodeLib.IEEE64.value (IEEE64.add a b) -
            (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)| +
          |(CodeLib.IEEE64.value a + CodeLib.IEEE64.value b) -
            (exactA + exactB)| := abs_add_le _ _
      _ ≤ epsilon + (errorA + errorB) :=
        add_le_add hroundError hinputs
      _ = epsilon + errorA + errorB := by ring
  · rw [show CodeLib.IEEE64.value (IEEE64.add a b) =
        (CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)) +
        (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b) by ring]
    calc
      |(CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)) +
        (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)| ≤
          |CodeLib.IEEE64.value (IEEE64.add a b) -
            (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)| +
          |CodeLib.IEEE64.value a + CodeLib.IEEE64.value b| :=
        abs_add_le _ _
      _ ≤ epsilon + (valueBoundA + valueBoundB) :=
        add_le_add hroundError
          ((abs_add_le _ _).trans (add_le_add ha.value_abs hb.value_abs))
      _ = epsilon + valueBoundA + valueBoundB := by ring
  · exact (abs_add_le _ _).trans (add_le_add ha.target_abs hb.target_abs)

/-- Addition variant with a directly proved exact rounded-operand range.
This is used for the energy jump and for the correlated final energy add. -/
private theorem approx_add_of_sum_lt_four
    (ha : Approx a exactA errorA valueBoundA targetBoundA)
    (hb : Approx b exactB errorB valueBoundB targetBoundB)
    (hrange : |CodeLib.IEEE64.value a + CodeLib.IEEE64.value b| < (4 : ℝ)) :
    Approx (IEEE64.add a b) (exactA + exactB)
      (epsilon + errorA + errorB)
      (epsilon + valueBoundA + valueBoundB)
      (targetBoundA + targetBoundB) := by
  have hround :=
    ScaledRoundoff.add_real_error_of_exact_sum_lt_four a b
      ha.finite hb.finite hrange
  have hroundError :
      |CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)| ≤ epsilon := by
    simpa [epsilon, CodeLib.Numerical.Kernels.f64Epsilon,
      CodeLib.IEEE64.arithmeticEpsilon] using hround.2
  have hinputs := CodeLib.Numerical.sum_perturbations ha.error_le hb.error_le
  refine ⟨hround.1, ?_, ?_, ?_⟩
  · rw [show CodeLib.IEEE64.value (IEEE64.add a b) - (exactA + exactB) =
        (CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)) +
        ((CodeLib.IEEE64.value a + CodeLib.IEEE64.value b) -
          (exactA + exactB)) by ring]
    calc
      |(CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)) +
        ((CodeLib.IEEE64.value a + CodeLib.IEEE64.value b) -
          (exactA + exactB))| ≤
          |CodeLib.IEEE64.value (IEEE64.add a b) -
            (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)| +
          |(CodeLib.IEEE64.value a + CodeLib.IEEE64.value b) -
            (exactA + exactB)| := abs_add_le _ _
      _ ≤ epsilon + (errorA + errorB) := add_le_add hroundError hinputs
      _ = epsilon + errorA + errorB := by ring
  · rw [show CodeLib.IEEE64.value (IEEE64.add a b) =
        (CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)) +
        (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b) by ring]
    calc
      |(CodeLib.IEEE64.value (IEEE64.add a b) -
          (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)) +
        (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)| ≤
          |CodeLib.IEEE64.value (IEEE64.add a b) -
            (CodeLib.IEEE64.value a + CodeLib.IEEE64.value b)| +
          |CodeLib.IEEE64.value a + CodeLib.IEEE64.value b| :=
        abs_add_le _ _
      _ ≤ epsilon + (valueBoundA + valueBoundB) :=
        add_le_add hroundError
          ((abs_add_le _ _).trans (add_le_add ha.value_abs hb.value_abs))
      _ = epsilon + valueBoundA + valueBoundB := by ring
  · exact (abs_add_le _ _).trans (add_le_add ha.target_abs hb.target_abs)

private theorem approx_mul
    (ha : Approx a exactA errorA valueBoundA targetBoundA)
    (hb : Approx b exactB errorB valueBoundB targetBoundB)
    (hrange : valueBoundA * valueBoundB < 2) :
    Approx (IEEE64.mul a b) (exactA * exactB)
      (epsilon +
        (errorA * errorB + errorA * targetBoundB + targetBoundA * errorB))
      (epsilon + valueBoundA * valueBoundB)
      (targetBoundA * targetBoundB) := by
  have hvalueBoundANonnegative : 0 ≤ valueBoundA :=
    (abs_nonneg _).trans ha.value_abs
  have hvalueBoundBNonnegative : 0 ≤ valueBoundB :=
    (abs_nonneg _).trans hb.value_abs
  have hproduct :
      |CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| < (2 : ℝ) := by
    rw [abs_mul]
    exact (mul_le_mul ha.value_abs hb.value_abs (abs_nonneg _)
      hvalueBoundANonnegative).trans_lt hrange
  have hround :=
    ScaledRoundoff.mul_real_error_of_exact_product_lt_two a b
      ha.finite hb.finite hproduct
  have hroundError :
      |CodeLib.IEEE64.value (IEEE64.mul a b) -
          CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| ≤ epsilon := by
    simpa [epsilon, CodeLib.Numerical.Kernels.f64Epsilon,
      CodeLib.IEEE64.multiplicationEpsilon] using hround.2
  have hinputs := CodeLib.Numerical.product_perturbations
    ha.error_le hb.error_le ha.target_abs hb.target_abs
  refine ⟨hround.1, ?_, ?_, ?_⟩
  · rw [show CodeLib.IEEE64.value (IEEE64.mul a b) - exactA * exactB =
        (CodeLib.IEEE64.value (IEEE64.mul a b) -
          CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) +
        (CodeLib.IEEE64.value a * CodeLib.IEEE64.value b -
          exactA * exactB) by ring]
    exact (abs_add_le _ _).trans (add_le_add hroundError hinputs)
  · rw [show CodeLib.IEEE64.value (IEEE64.mul a b) =
        (CodeLib.IEEE64.value (IEEE64.mul a b) -
          CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) +
        CodeLib.IEEE64.value a * CodeLib.IEEE64.value b by ring]
    calc
      |(CodeLib.IEEE64.value (IEEE64.mul a b) -
          CodeLib.IEEE64.value a * CodeLib.IEEE64.value b) +
        CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| ≤
          |CodeLib.IEEE64.value (IEEE64.mul a b) -
            CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| +
          |CodeLib.IEEE64.value a * CodeLib.IEEE64.value b| :=
        abs_add_le _ _
      _ ≤ epsilon + valueBoundA * valueBoundB := by
        rw [abs_mul]
        exact add_le_add hroundError
          (mul_le_mul ha.value_abs hb.value_abs (abs_nonneg _)
            hvalueBoundANonnegative)
  · rw [abs_mul]
    have htargetBoundANonnegative : 0 ≤ targetBoundA :=
      (abs_nonneg _).trans ha.target_abs
    exact mul_le_mul ha.target_abs hb.target_abs (abs_nonneg _)
      htargetBoundANonnegative

private theorem approx_negate
    (h : Approx bits target error valueBound targetBound) :
    Approx (Model.negateBits bits) (-target) error valueBound targetBound := by
  have hneg := ScaledRoundoff.negateBits_real_spec bits h.finite
  refine ⟨hneg.1, ?_, ?_, ?_⟩
  · rw [hneg.2, show -CodeLib.IEEE64.value bits - -target =
        -(CodeLib.IEEE64.value bits - target) by ring, abs_neg]
    exact h.error_le
  · rw [hneg.2, abs_neg]
    exact h.value_abs
  · rw [abs_neg]
    exact h.target_abs

private theorem difference_perturbations
    (ha : Approx a exactA errorA valueBoundA targetBoundA)
    (hb : Approx b exactB errorB valueBoundB targetBoundB) :
    |(CodeLib.IEEE64.value a - CodeLib.IEEE64.value b) -
        (exactA - exactB)| ≤ errorA + errorB := by
  have hbneg :
      |-CodeLib.IEEE64.value b - -exactB| ≤ errorB := by
    rw [show -CodeLib.IEEE64.value b - -exactB =
      -(CodeLib.IEEE64.value b - exactB) by ring, abs_neg]
    exact hb.error_le
  simpa [sub_eq_add_neg] using
    (CodeLib.Numerical.sum_perturbations ha.error_le hbneg)

/-! ## Exact dyadic constants -/

private theorem half_approx :
    Approx Model.halfBits ((1 : ℝ) / 2) 0 (1 / 2) (1 / 2) := by
  have hbits : Model.halfBits = IEEE64.encodeFinite false 1022 0 := by
    norm_num [Model.halfBits, IEEE64.encodeFinite]
    rfl
  rw [hbits]
  have hfinite :
      CodeLib.IEEE64.Finite (IEEE64.encodeFinite false 1022 0) :=
    CodeLib.IEEE64.finite_encodeFinite false 1022 0 (by norm_num) (by norm_num)
  have hvalue :
      CodeLib.IEEE64.value (IEEE64.encodeFinite false 1022 0) =
        (1 : ℝ) / 2 := by
    rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1022 0
        (by norm_num) (by norm_num)]
    norm_num [pow_succ]
  exact ⟨hfinite, by rw [hvalue]; norm_num,
    by rw [hvalue]; norm_num, by norm_num⟩

private theorem quarter_approx :
    Approx Model.quarterBits ((1 : ℝ) / 4) 0 (1 / 4) (1 / 4) := by
  have hbits : Model.quarterBits = IEEE64.encodeFinite false 1021 0 := by
    norm_num [Model.quarterBits, IEEE64.encodeFinite]
    rfl
  rw [hbits]
  have hfinite :
      CodeLib.IEEE64.Finite (IEEE64.encodeFinite false 1021 0) :=
    CodeLib.IEEE64.finite_encodeFinite false 1021 0 (by norm_num) (by norm_num)
  have hvalue :
      CodeLib.IEEE64.value (IEEE64.encodeFinite false 1021 0) =
        (1 : ℝ) / 4 := by
    rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1021 0
        (by norm_num) (by norm_num)]
    norm_num [pow_succ]
  exact ⟨hfinite, by rw [hvalue]; norm_num,
    by rw [hvalue]; norm_num, by norm_num⟩

private theorem eighth_approx :
    Approx Model.eighthBits ((1 : ℝ) / 8) 0 (1 / 8) (1 / 8) := by
  have hbits : Model.eighthBits = IEEE64.encodeFinite false 1020 0 := by
    norm_num [Model.eighthBits, IEEE64.encodeFinite]
    rfl
  rw [hbits]
  have hfinite :
      CodeLib.IEEE64.Finite (IEEE64.encodeFinite false 1020 0) :=
    CodeLib.IEEE64.finite_encodeFinite false 1020 0 (by norm_num) (by norm_num)
  have hvalue :
      CodeLib.IEEE64.value (IEEE64.encodeFinite false 1020 0) =
        (1 : ℝ) / 8 := by
    rw [CodeLib.IEEE64.value,
      CodeLib.IEEE64.scaledValue_encodeFinite false 1020 0
        (by norm_num) (by norm_num)]
    norm_num [pow_succ]
  exact ⟨hfinite, by rw [hvalue]; norm_num,
    by rw [hvalue]; norm_num, by norm_num⟩

/-! ## Per-state exact quantities and bounds -/

private noncomputable def massReal (rho u : UInt64) : ℝ :=
  CodeLib.IEEE64.value rho * CodeLib.IEEE64.value u

private noncomputable def kineticReal (rho u : UInt64) : ℝ :=
  massReal rho u * CodeLib.IEEE64.value u

private noncomputable def energyReal (rho u p : UInt64) : ℝ :=
  (5 / 2 : ℝ) * CodeLib.IEEE64.value p + (1 / 2) * kineticReal rho u

private noncomputable def enthalpyReal (rho u p : UInt64) : ℝ :=
  (7 / 2 : ℝ) * CodeLib.IEEE64.value p + (1 / 2) * kineticReal rho u

private noncomputable def momentumFluxReal (rho u p : UInt64) : ℝ :=
  kineticReal rho u + CodeLib.IEEE64.value p

private noncomputable def energyFluxReal (rho u p : UInt64) : ℝ :=
  enthalpyReal rho u p * CodeLib.IEEE64.value u

private structure SideRealBounds (rho u p : UInt64) : Prop where
  massAbs : |massReal rho u| ≤ 1 / 2
  kineticNonnegative : 0 ≤ kineticReal rho u
  kineticUpper : kineticReal rho u ≤ 1 / 4
  energyNonnegative : 0 ≤ energyReal rho u p
  energyUpper : energyReal rho u p ≤ 21 / 8
  enthalpyNonnegative : 0 ≤ enthalpyReal rho u p
  enthalpyUpper : enthalpyReal rho u p ≤ 29 / 8
  momentumFluxAbs : |momentumFluxReal rho u p| ≤ 5 / 4
  energyFluxAbs : |energyFluxReal rho u p| ≤ 29 / 16
  pressureLeTwoFifthsEnergy :
    CodeLib.IEEE64.value p ≤ (2 / 5 : ℝ) * energyReal rho u p
  energyFluxRelative :
    |energyFluxReal rho u p| ≤ (7 / 10 : ℝ) * energyReal rho u p

private theorem side_real_bounds
    (h : Bounds.StateBounds rho u p) : SideRealBounds rho u p := by
  let r := CodeLib.IEEE64.value rho
  let v := CodeLib.IEEE64.value u
  let pressure := CodeLib.IEEE64.value p
  have hrNonnegative : 0 ≤ r := by dsimp [r]; linarith [h.densityLower]
  have hpNonnegative : 0 ≤ pressure := by
    dsimp [pressure]
    linarith [h.pressureLower]
  have hpUpper : pressure ≤ 1 := by
    dsimp [pressure]
    exact h.pressureLeDensity.trans h.densityUpper
  have hvBounds : -(1 / 2 : ℝ) ≤ v ∧ v ≤ 1 / 2 := by
    dsimp [v]
    exact abs_le.mp h.velocityAbs
  have hvSquaredNonnegative : 0 ≤ v * v := mul_self_nonneg v
  have hvSquaredUpper : v * v ≤ (1 / 4 : ℝ) := by nlinarith
  have hkineticNonnegative' : 0 ≤ r * (v * v) :=
    mul_nonneg hrNonnegative hvSquaredNonnegative
  have hkineticUpper' : r * (v * v) ≤ (1 / 4 : ℝ) := by
    calc
      r * (v * v) ≤ 1 * (1 / 4 : ℝ) :=
        mul_le_mul h.densityUpper hvSquaredUpper hvSquaredNonnegative
          (by norm_num)
      _ = 1 / 4 := by ring
  have hkineticEq : kineticReal rho u = r * (v * v) := by
    simp only [kineticReal, massReal, r, v]
    ring
  have hkineticUpper : kineticReal rho u ≤ (1 / 4 : ℝ) := by
    rw [hkineticEq]
    exact hkineticUpper'
  have hkineticNonnegative : 0 ≤ kineticReal rho u := by
    rw [hkineticEq]
    exact hkineticNonnegative'
  have hmassAbs : |massReal rho u| ≤ (1 / 2 : ℝ) := by
    rw [massReal, abs_mul]
    calc
      |CodeLib.IEEE64.value rho| * |CodeLib.IEEE64.value u| ≤
          1 * (1 / 2 : ℝ) :=
        mul_le_mul h.densityAbs h.velocityAbs (abs_nonneg _) (by norm_num)
      _ = 1 / 2 := by ring
  have henergyNonnegative : 0 ≤ energyReal rho u p := by
    dsimp [energyReal]
    nlinarith
  have henergyUpper : energyReal rho u p ≤ (21 / 8 : ℝ) := by
    dsimp [energyReal]
    nlinarith
  have henthalpyNonnegative : 0 ≤ enthalpyReal rho u p := by
    dsimp [enthalpyReal]
    nlinarith
  have henthalpyUpper : enthalpyReal rho u p ≤ (29 / 8 : ℝ) := by
    dsimp [enthalpyReal]
    nlinarith
  have hmomentumNonnegative : 0 ≤ momentumFluxReal rho u p := by
    dsimp [momentumFluxReal]
    linarith
  have hmomentumUpper : momentumFluxReal rho u p ≤ (5 / 4 : ℝ) := by
    dsimp [momentumFluxReal]
    nlinarith
  have hpEnergy : CodeLib.IEEE64.value p ≤
      (2 / 5 : ℝ) * energyReal rho u p := by
    dsimp [energyReal]
    nlinarith
  have henergyFluxRelative : |energyFluxReal rho u p| ≤
      (7 / 10 : ℝ) * energyReal rho u p := by
    rw [energyFluxReal, abs_mul, abs_of_nonneg henthalpyNonnegative]
    calc
      enthalpyReal rho u p * |CodeLib.IEEE64.value u| ≤
          enthalpyReal rho u p * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left h.velocityAbs henthalpyNonnegative
      _ ≤ (7 / 10 : ℝ) * energyReal rho u p := by
        have henthalpyIdentity : enthalpyReal rho u p =
            energyReal rho u p + CodeLib.IEEE64.value p := by
          simp only [enthalpyReal, energyReal]
          ring
        rw [henthalpyIdentity]
        nlinarith
  have henergyFluxAbs : |energyFluxReal rho u p| ≤ (29 / 16 : ℝ) := by
    rw [energyFluxReal, abs_mul, abs_of_nonneg henthalpyNonnegative]
    calc
      enthalpyReal rho u p * |CodeLib.IEEE64.value u| ≤
          enthalpyReal rho u p * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left h.velocityAbs henthalpyNonnegative
      _ ≤ (29 / 8 : ℝ) * (1 / 2) :=
        mul_le_mul_of_nonneg_right henthalpyUpper (by norm_num)
      _ = 29 / 16 := by ring
  exact
    { massAbs := hmassAbs
      kineticNonnegative := hkineticNonnegative
      kineticUpper := hkineticUpper
      energyNonnegative := henergyNonnegative
      energyUpper := henergyUpper
      enthalpyNonnegative := henthalpyNonnegative
      enthalpyUpper := henthalpyUpper
      momentumFluxAbs := by rw [abs_of_nonneg hmomentumNonnegative]; exact hmomentumUpper
      energyFluxAbs := henergyFluxAbs
      pressureLeTwoFifthsEnergy := hpEnergy
      energyFluxRelative := henergyFluxRelative }

/-! ## The eleven operations for one Euler state -/

private structure SideApprox (rho u p : UInt64) : Prop where
  mass : Approx (Model.sideBits rho u p).mass
    (massReal rho u) epsilon (3 / 4) (1 / 2)
  energy : Approx (Model.sideBits rho u p).energy
    (energyReal rho u p) (6 * epsilon) (11 / 4) (21 / 8)
  momentumFlux : Approx (Model.sideBits rho u p).momentumFlux
    (momentumFluxReal rho u p) (3 * epsilon) (21 / 16) (5 / 4)
  energyFlux : Approx (Model.sideBits rho u p).energyFlux
    (energyFluxReal rho u p) (5 * epsilon) (15 / 8) (29 / 16)

private theorem side_approx (h : Bounds.StateBounds rho u p) :
    SideApprox rho u p := by
  have hrho : Approx rho (CodeLib.IEEE64.value rho) 0 1 1 :=
    Approx.exact rho 1 h.densityFinite h.densityAbs
  have hu : Approx u (CodeLib.IEEE64.value u) 0 (1 / 2) (1 / 2) :=
    Approx.exact u (1 / 2) h.velocityFinite h.velocityAbs
  have hp : Approx p (CodeLib.IEEE64.value p) 0 1 1 :=
    Approx.exact p 1 h.pressureFinite h.pressureAbs
  have hmassRaw := approx_mul hrho hu (by norm_num)
  have hmass : Approx (IEEE64.mul rho u) (massReal rho u)
      epsilon (3 / 4) (1 / 2) := by
    simpa [massReal] using hmassRaw.normalize epsilon (3 / 4) (1 / 2)
      (by simp) (by norm_num) (by norm_num [epsilon,
        CodeLib.Numerical.Kernels.f64Epsilon])
  have hvelocitySquaredMassRaw := approx_mul hmass hu (by norm_num)
  have hvelocitySquaredMass :
      Approx (IEEE64.mul (IEEE64.mul rho u) u) (kineticReal rho u)
        (2 * epsilon) (1 / 2) (1 / 4) := by
    simpa [kineticReal, massReal] using
      hvelocitySquaredMassRaw.normalize (2 * epsilon) (1 / 2) (1 / 4)
        (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
        (by norm_num)
        (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hhalfKineticRaw := approx_mul half_approx hvelocitySquaredMass (by norm_num)
  have hhalfKinetic :
      Approx (IEEE64.mul Model.halfBits
          (IEEE64.mul (IEEE64.mul rho u) u))
        ((1 / 2 : ℝ) * kineticReal rho u)
        (2 * epsilon) (3 / 16) (1 / 8) := by
    exact hhalfKineticRaw.normalize (2 * epsilon) (3 / 16) (1 / 8)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
      (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hhalfPressureRaw := approx_mul half_approx hp (by norm_num)
  have hhalfPressure :
      Approx (IEEE64.mul Model.halfBits p)
        ((1 / 2 : ℝ) * CodeLib.IEEE64.value p)
        epsilon (9 / 16) (1 / 2) := by
    exact hhalfPressureRaw.normalize epsilon (9 / 16) (1 / 2)
      (by simp) (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have htwoPressureRaw := approx_add hp hp (by norm_num)
  have htwoPressure :
      Approx (IEEE64.add p p)
        (CodeLib.IEEE64.value p + CodeLib.IEEE64.value p)
        epsilon (33 / 16) 2 := by
    exact htwoPressureRaw.normalize epsilon (33 / 16) 2
      (by ring_nf; exact le_rfl) (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have henergyPressureRaw := approx_add htwoPressure hhalfPressure (by norm_num)
  have henergyPressure :
      Approx (IEEE64.add (IEEE64.add p p) (IEEE64.mul Model.halfBits p))
        ((CodeLib.IEEE64.value p + CodeLib.IEEE64.value p) +
          (1 / 2 : ℝ) * CodeLib.IEEE64.value p)
        (3 * epsilon) (21 / 8) (5 / 2) := by
    exact henergyPressureRaw.normalize (3 * epsilon) (21 / 8) (5 / 2)
      (by ring_nf; exact le_rfl) (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have henergyRaw := approx_add henergyPressure hhalfKinetic (by norm_num)
  have henergy :
      Approx
        (IEEE64.add
          (IEEE64.add (IEEE64.add p p) (IEEE64.mul Model.halfBits p))
          (IEEE64.mul Model.halfBits (IEEE64.mul (IEEE64.mul rho u) u)))
        (energyReal rho u p) (6 * epsilon) (11 / 4) (21 / 8) := by
    have hnormalized := henergyRaw.normalize
      (6 * epsilon) (11 / 4) (21 / 8)
      (by ring_nf; exact le_rfl)
      (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
    have htarget :
        (((CodeLib.IEEE64.value p + CodeLib.IEEE64.value p) +
            (1 / 2 : ℝ) * CodeLib.IEEE64.value p) +
          (1 / 2) * kineticReal rho u) = energyReal rho u p := by
      simp only [energyReal]
      ring
    rw [← htarget]
    exact hnormalized
  have henthalpyPressureRaw := approx_add henergyPressure hp (by norm_num)
  have henthalpyPressure :
      Approx
        (IEEE64.add
          (IEEE64.add (IEEE64.add p p) (IEEE64.mul Model.halfBits p)) p)
        (((CodeLib.IEEE64.value p + CodeLib.IEEE64.value p) +
            (1 / 2 : ℝ) * CodeLib.IEEE64.value p) +
          CodeLib.IEEE64.value p)
        (4 * epsilon) (29 / 8) (7 / 2) := by
    exact henthalpyPressureRaw.normalize (4 * epsilon) (29 / 8) (7 / 2)
      (by ring_nf; exact le_rfl) (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have henthalpyRaw := approx_add henthalpyPressure hhalfKinetic (by norm_num)
  have henthalpy :
      Approx
        (IEEE64.add
          (IEEE64.add
            (IEEE64.add (IEEE64.add p p) (IEEE64.mul Model.halfBits p)) p)
          (IEEE64.mul Model.halfBits (IEEE64.mul (IEEE64.mul rho u) u)))
        (enthalpyReal rho u p) (7 * epsilon) (59 / 16) (29 / 8) := by
    have hnormalized := henthalpyRaw.normalize
      (7 * epsilon) (59 / 16) (29 / 8)
      (by ring_nf; exact le_rfl)
      (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
    have htarget :
        ((((CodeLib.IEEE64.value p + CodeLib.IEEE64.value p) +
            (1 / 2 : ℝ) * CodeLib.IEEE64.value p) +
          CodeLib.IEEE64.value p) + (1 / 2) * kineticReal rho u) =
            enthalpyReal rho u p := by
      simp only [enthalpyReal]
      ring
    rw [← htarget]
    exact hnormalized
  have hmomentumFluxRaw := approx_add hvelocitySquaredMass hp (by norm_num)
  have hmomentumFlux :
      Approx (IEEE64.add (IEEE64.mul (IEEE64.mul rho u) u) p)
        (momentumFluxReal rho u p) (3 * epsilon) (21 / 16) (5 / 4) := by
    have hnormalized := hmomentumFluxRaw.normalize
      (3 * epsilon) (21 / 16) (5 / 4)
      (by ring_nf; exact le_rfl)
      (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
    simpa only [momentumFluxReal] using hnormalized
  have henergyFluxRaw := approx_mul henthalpy hu (by norm_num)
  have henergyFlux :
      Approx
        (IEEE64.mul
          (IEEE64.add
            (IEEE64.add
              (IEEE64.add (IEEE64.add p p) (IEEE64.mul Model.halfBits p)) p)
            (IEEE64.mul Model.halfBits (IEEE64.mul (IEEE64.mul rho u) u))) u)
        (energyFluxReal rho u p) (5 * epsilon) (15 / 8) (29 / 16) := by
    have hnormalized := henergyFluxRaw.normalize
      (5 * epsilon) (15 / 8) (29 / 16)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
      (by norm_num)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
    simpa only [energyFluxReal] using hnormalized
  exact
    { mass := by simpa [Model.sideBits] using hmass
      energy := by simpa [Model.sideBits] using henergy
      momentumFlux := by simpa [Model.sideBits] using hmomentumFlux
      energyFlux := by simpa [Model.sideBits] using henergyFlux }

/-! ## Reusable mean, jump, and dyadic-dissipation certificates -/

private theorem mean_approx
    (hleft : Approx left exactLeft errorLeft valueBoundLeft targetBoundLeft)
    (hright : Approx right exactRight errorRight valueBoundRight targetBoundRight)
    (hsumRange : valueBoundLeft + valueBoundRight < 4)
    (hproductRange :
      (epsilon + valueBoundLeft + valueBoundRight) * (1 / 2) < 2) :
    Approx (Model.meanBits left right)
      ((1 / 2 : ℝ) * (exactLeft + exactRight))
      (epsilon + (1 / 2) * (epsilon + errorLeft + errorRight))
      (epsilon + (1 / 2) * (epsilon + valueBoundLeft + valueBoundRight))
      ((1 / 2) * (targetBoundLeft + targetBoundRight)) := by
  have hsum := approx_add hleft hright hsumRange
  have hproduct := approx_mul half_approx hsum (by
    simpa [mul_comm] using hproductRange)
  simpa [Model.meanBits] using hproduct

private theorem jump_approx
    (hleft : Approx left exactLeft errorLeft valueBoundLeft targetBoundLeft)
    (hright : Approx right exactRight errorRight valueBoundRight targetBoundRight)
    (hrange :
      |CodeLib.IEEE64.value left - CodeLib.IEEE64.value right| < (4 : ℝ)) :
    Approx (Model.jumpBits left right) (exactLeft - exactRight)
      (epsilon + errorLeft + errorRight)
      (epsilon + valueBoundLeft + valueBoundRight)
      (targetBoundLeft + targetBoundRight) := by
  have hneg := approx_negate hright
  have hrange' :
      |CodeLib.IEEE64.value left +
          CodeLib.IEEE64.value (Model.negateBits right)| < (4 : ℝ) := by
    rw [ScaledRoundoff.value_negateBits]
    simpa [sub_eq_add_neg] using hrange
  have hsum := approx_add_of_sum_lt_four hleft hneg hrange'
  simpa [Model.jumpBits, sub_eq_add_neg] using hsum

/-- The exact dyadic association in `dissipationBits` contributes five local
rounding units in addition to `7/8` of its input error.  The hypotheses are
the largest jump bounds used below (the energy jump), so one proof serves all
three components. -/
private theorem dissipation_approx
    (hjump : Approx jump exactJump jumpError jumpValueBound jumpTargetBound)
    (hvalue : jumpValueBound ≤ (11 / 4 : ℝ))
    (_htarget : jumpTargetBound ≤ (21 / 8 : ℝ)) :
    Approx (Model.dissipationBits jump)
      ((7 / 8 : ℝ) * exactJump)
      (5 * epsilon + (7 / 8) * jumpError)
      ((7 / 8) * jumpTargetBound +
        (5 * epsilon + (7 / 8) * jumpError))
      ((7 / 8) * jumpTargetBound) := by
  have hhalf := approx_mul half_approx hjump (by
    have hjumpNonnegative : 0 ≤ jumpValueBound :=
      (abs_nonneg _).trans hjump.value_abs
    nlinarith)
  have hquarter := approx_mul quarter_approx hjump (by
    have hjumpNonnegative : 0 ≤ jumpValueBound :=
      (abs_nonneg _).trans hjump.value_abs
    nlinarith)
  have heighth := approx_mul eighth_approx hjump (by
    have hjumpNonnegative : 0 ≤ jumpValueBound :=
      (abs_nonneg _).trans hjump.value_abs
    nlinarith)
  have hhalfQuarter := approx_add hhalf hquarter (by
    norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon]
    nlinarith [hvalue])
  have hall := approx_add hhalfQuarter heighth (by
    norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon]
    nlinarith [hvalue])
  have hnormalized := hall.normalize
    (5 * epsilon + (7 / 8) * jumpError)
    ((7 / 8) * jumpTargetBound +
      (5 * epsilon + (7 / 8) * jumpError))
    ((7 / 8) * jumpTargetBound)
    (by ring_nf; exact le_rfl)
    (by ring_nf; exact le_rfl)
    (by ring_nf; exact le_rfl)
  have htarget :
      (((1 / 2 : ℝ) * exactJump + (1 / 4) * exactJump) +
        (1 / 8) * exactJump) = (7 / 8) * exactJump := by
    ring
  rw [← htarget]
  simpa only [Model.dissipationBits] using hnormalized

/-! ## Exact component targets and the correlated energy bound -/

private noncomputable def massRusanovReal
    (rhoL uL rhoR uR : UInt64) : ℝ :=
  (1 / 2 : ℝ) * (massReal rhoL uL + massReal rhoR uR) +
    (7 / 8 : ℝ) *
      (CodeLib.IEEE64.value rhoL - CodeLib.IEEE64.value rhoR)

private noncomputable def momentumRusanovReal
    (rhoL uL pL rhoR uR pR : UInt64) : ℝ :=
  (1 / 2 : ℝ) *
      (momentumFluxReal rhoL uL pL + momentumFluxReal rhoR uR pR) +
    (7 / 8 : ℝ) * (massReal rhoL uL - massReal rhoR uR)

private noncomputable def energyRusanovReal
    (rhoL uL pL rhoR uR pR : UInt64) : ℝ :=
  (1 / 2 : ℝ) *
      (energyFluxReal rhoL uL pL + energyFluxReal rhoR uR pR) +
    (7 / 8 : ℝ) *
      (energyReal rhoL uL pL - energyReal rhoR uR pR)

private theorem density_difference_abs
    (hleft : Bounds.StateBounds rhoL uL pL)
    (hright : Bounds.StateBounds rhoR uR pR) :
    |CodeLib.IEEE64.value rhoL - CodeLib.IEEE64.value rhoR| ≤
      (7 / 8 : ℝ) := by
  rw [abs_le]
  constructor <;> linarith [hleft.densityLower, hleft.densityUpper,
    hright.densityLower, hright.densityUpper]

private theorem mass_difference_abs
    (hleft : SideRealBounds rhoL uL pL)
    (hright : SideRealBounds rhoR uR pR) :
    |massReal rhoL uL - massReal rhoR uR| ≤ (1 : ℝ) := by
  rw [show massReal rhoL uL - massReal rhoR uR =
      massReal rhoL uL + -massReal rhoR uR by ring]
  calc
    |massReal rhoL uL + -massReal rhoR uR| ≤
        |massReal rhoL uL| + |-massReal rhoR uR| := abs_add_le _ _
    _ = |massReal rhoL uL| + |massReal rhoR uR| := by rw [abs_neg]
    _ ≤ (1 / 2 : ℝ) + 1 / 2 := add_le_add hleft.massAbs hright.massAbs
    _ = 1 := by ring

private theorem energy_difference_abs
    (hleft : SideRealBounds rhoL uL pL)
    (hright : SideRealBounds rhoR uR pR) :
    |energyReal rhoL uL pL - energyReal rhoR uR pR| ≤
      (21 / 8 : ℝ) := by
  rw [abs_le]
  constructor <;> linarith [hleft.energyNonnegative, hleft.energyUpper,
    hright.energyNonnegative, hright.energyUpper]

/-- Correlated exact headroom for the final energy component.  The looser
independent estimates for its two summands do not prove the required
binary64-addition range. -/
private theorem energy_rusanov_abs
    (hleft : SideRealBounds rhoL uL pL)
    (hright : SideRealBounds rhoR uR pR) :
    |energyRusanovReal rhoL uL pL rhoR uR pR| ≤
      (1029 / 320 : ℝ) := by
  let eL := energyReal rhoL uL pL
  let eR := energyReal rhoR uR pR
  let fL := energyFluxReal rhoL uL pL
  let fR := energyFluxReal rhoR uR pR
  have heL0 : 0 ≤ eL := hleft.energyNonnegative
  have heR0 : 0 ≤ eR := hright.energyNonnegative
  have heLU : eL ≤ (21 / 8 : ℝ) := hleft.energyUpper
  have heRU : eR ≤ (21 / 8 : ℝ) := hright.energyUpper
  have hfL : |fL| ≤ (7 / 10 : ℝ) * eL := hleft.energyFluxRelative
  have hfR : |fR| ≤ (7 / 10 : ℝ) * eR := hright.energyFluxRelative
  have htriangle :
      |(1 / 2 : ℝ) * (fL + fR) + (7 / 8) * (eL - eR)| ≤
        (7 / 20 : ℝ) * (eL + eR) + (7 / 8) * |eL - eR| := by
    calc
      |(1 / 2 : ℝ) * (fL + fR) + (7 / 8) * (eL - eR)| ≤
          |(1 / 2 : ℝ) * (fL + fR)| +
            |(7 / 8 : ℝ) * (eL - eR)| := abs_add_le _ _
      _ = (1 / 2 : ℝ) * |fL + fR| + (7 / 8) * |eL - eR| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (|fL| + |fR|) +
          (7 / 8) * |eL - eR| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (abs_add_le fL fR) (by norm_num))
          (le_refl _)
      _ ≤ (1 / 2 : ℝ) *
            ((7 / 10) * eL + (7 / 10) * eR) +
          (7 / 8) * |eL - eR| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add hfL hfR) (by norm_num))
          (le_refl _)
      _ = (7 / 20 : ℝ) * (eL + eR) + (7 / 8) * |eL - eR| := by ring
  have hscalar :
      (7 / 20 : ℝ) * (eL + eR) + (7 / 8) * |eL - eR| ≤
        1029 / 320 := by
    by_cases horder : eL ≤ eR
    · rw [abs_of_nonpos (sub_nonpos.mpr horder)]
      nlinarith
    · have horder' : eR ≤ eL := (lt_of_not_ge horder).le
      rw [abs_of_nonneg (sub_nonneg.mpr horder')]
      nlinarith
  simpa [energyRusanovReal, eL, eR, fL, fR] using htriangle.trans hscalar

/-! ## Three rounded Rusanov components -/

private theorem mass_component_approx
    (hleft : Bounds.StateBounds rhoL uL pL)
    (hright : Bounds.StateBounds rhoR uR pR) :
    Approx
      (Model.rusanovComponentBits
        (Model.sideBits rhoL uL pL).mass
        (Model.sideBits rhoR uR pR).mass rhoL rhoR)
      (massRusanovReal rhoL uL rhoR uR)
      (10 * epsilon) (21 / 16) (81 / 64) := by
  have hsL := side_approx hleft
  have hsR := side_approx hright
  have hrhoL : Approx rhoL (CodeLib.IEEE64.value rhoL) 0 1 1 :=
    Approx.exact rhoL 1 hleft.densityFinite hleft.densityAbs
  have hrhoR : Approx rhoR (CodeLib.IEEE64.value rhoR) 0 1 1 :=
    Approx.exact rhoR 1 hright.densityFinite hright.densityAbs
  have hmeanRaw := mean_approx hsL.mass hsR.mass
    (by norm_num)
    (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hmean :
      Approx
        (Model.meanBits (Model.sideBits rhoL uL pL).mass
          (Model.sideBits rhoR uR pR).mass)
        ((1 / 2 : ℝ) * (massReal rhoL uL + massReal rhoR uR))
        (3 * epsilon) (5 / 8) (1 / 2) := by
    exact hmeanRaw.normalize (3 * epsilon) (5 / 8) (1 / 2)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
      (by ring_nf; exact le_rfl)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hjumpRange :
      |CodeLib.IEEE64.value rhoL - CodeLib.IEEE64.value rhoR| < (4 : ℝ) :=
    (density_difference_abs hleft hright).trans_lt (by norm_num)
  have hjumpRaw := jump_approx hrhoL hrhoR hjumpRange
  have hjump :
      Approx (Model.jumpBits rhoL rhoR)
        (CodeLib.IEEE64.value rhoL - CodeLib.IEEE64.value rhoR)
        epsilon 1 (7 / 8) := by
    exact hjumpRaw.withBounds epsilon 1 (7 / 8)
      (by ring_nf; exact le_rfl) (density_difference_abs hleft hright)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hdissRaw := dissipation_approx hjump (by norm_num) (by norm_num)
  have hdiss :
      Approx (Model.dissipationBits (Model.jumpBits rhoL rhoR))
        ((7 / 8 : ℝ) *
          (CodeLib.IEEE64.value rhoL - CodeLib.IEEE64.value rhoR))
        (6 * epsilon) (13 / 16) (49 / 64) := by
    exact hdissRaw.normalize (6 * epsilon) (13 / 16) (49 / 64)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
      (by ring_nf; exact le_rfl)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hresultRaw := approx_add hmean hdiss (by norm_num)
  have hresult := hresultRaw.normalize
    (10 * epsilon) (21 / 16) (81 / 64)
    (by ring_nf; exact le_rfl) (by ring_nf; exact le_rfl)
    (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  simpa [Model.rusanovComponentBits, massRusanovReal] using hresult

private theorem momentum_component_approx
    (hleft : Bounds.StateBounds rhoL uL pL)
    (hright : Bounds.StateBounds rhoR uR pR) :
    Approx
      (Model.rusanovComponentBits
        (Model.sideBits rhoL uL pL).momentumFlux
        (Model.sideBits rhoR uR pR).momentumFlux
        (Model.sideBits rhoL uL pL).mass
        (Model.sideBits rhoR uR pR).mass)
      (momentumRusanovReal rhoL uL pL rhoR uR pR)
      (14 * epsilon) (35 / 16) (17 / 8) := by
  have hsL := side_approx hleft
  have hsR := side_approx hright
  have hrealL := side_real_bounds hleft
  have hrealR := side_real_bounds hright
  have hmeanRaw := mean_approx hsL.momentumFlux hsR.momentumFlux
    (by norm_num)
    (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hmean :
      Approx
        (Model.meanBits (Model.sideBits rhoL uL pL).momentumFlux
          (Model.sideBits rhoR uR pR).momentumFlux)
        ((1 / 2 : ℝ) *
          (momentumFluxReal rhoL uL pL + momentumFluxReal rhoR uR pR))
        (5 * epsilon) (41 / 32) (5 / 4) := by
    exact hmeanRaw.normalize (5 * epsilon) (41 / 32) (5 / 4)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
      (by ring_nf; exact le_rfl)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hjumpRange :
      |CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).mass -
          CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).mass| < (4 : ℝ) := by
    calc
      |CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).mass -
          CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).mass| ≤
          |CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).mass| +
          |CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).mass| := by
        simpa [sub_eq_add_neg] using
          (abs_add_le
            (CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).mass)
            (-CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).mass))
      _ ≤ (3 / 4 : ℝ) + 3 / 4 :=
        add_le_add hsL.mass.value_abs hsR.mass.value_abs
      _ < 4 := by norm_num
  have hjumpRaw := jump_approx hsL.mass hsR.mass hjumpRange
  have hjump :
      Approx
        (Model.jumpBits (Model.sideBits rhoL uL pL).mass
          (Model.sideBits rhoR uR pR).mass)
        (massReal rhoL uL - massReal rhoR uR)
        (3 * epsilon) (17 / 16) 1 := by
    exact hjumpRaw.withBounds (3 * epsilon) (17 / 16) 1
      (by ring_nf; exact le_rfl) (mass_difference_abs hrealL hrealR)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hdissRaw := dissipation_approx hjump (by norm_num) (by norm_num)
  have hdiss :
      Approx
        (Model.dissipationBits
          (Model.jumpBits (Model.sideBits rhoL uL pL).mass
            (Model.sideBits rhoR uR pR).mass))
        ((7 / 8 : ℝ) * (massReal rhoL uL - massReal rhoR uR))
        (8 * epsilon) (29 / 32) (7 / 8) := by
    exact hdissRaw.normalize (8 * epsilon) (29 / 32) (7 / 8)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
      (by ring_nf; exact le_rfl)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hresultRaw := approx_add hmean hdiss (by norm_num)
  have hresult := hresultRaw.normalize
    (14 * epsilon) (35 / 16) (17 / 8)
    (by ring_nf; exact le_rfl) (by ring_nf; exact le_rfl)
    (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  simpa [Model.rusanovComponentBits, momentumRusanovReal] using hresult

private theorem energy_component_approx
    (hleft : Bounds.StateBounds rhoL uL pL)
    (hright : Bounds.StateBounds rhoR uR pR) :
    Approx
      (Model.rusanovComponentBits
        (Model.sideBits rhoL uL pL).energyFlux
        (Model.sideBits rhoR uR pR).energyFlux
        (Model.sideBits rhoL uL pL).energy
        (Model.sideBits rhoR uR pR).energy)
      (energyRusanovReal rhoL uL pL rhoR uR pR)
      (25 * epsilon) (13 / 4) (1029 / 320) := by
  have hsL := side_approx hleft
  have hsR := side_approx hright
  have hrealL := side_real_bounds hleft
  have hrealR := side_real_bounds hright
  have hmeanRaw := mean_approx hsL.energyFlux hsR.energyFlux
    (by norm_num)
    (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hmean :
      Approx
        (Model.meanBits (Model.sideBits rhoL uL pL).energyFlux
          (Model.sideBits rhoR uR pR).energyFlux)
        ((1 / 2 : ℝ) *
          (energyFluxReal rhoL uL pL + energyFluxReal rhoR uR pR))
        (7 * epsilon) (117 / 64) (29 / 16) := by
    exact hmeanRaw.normalize (7 * epsilon) (117 / 64) (29 / 16)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
      (by ring_nf; exact le_rfl)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have henergyDifference := energy_difference_abs hrealL hrealR
  have hjumpInputError :
      |(CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).energy -
          CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).energy) -
        (energyReal rhoL uL pL - energyReal rhoR uR pR)| ≤
          12 * epsilon := by
    have hraw := difference_perturbations hsL.energy hsR.energy
    calc
      _ ≤ 6 * epsilon + 6 * epsilon := hraw
      _ = 12 * epsilon := by ring
  have hjumpRange :
      |CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).energy -
          CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).energy| < (4 : ℝ) := by
    rw [show CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).energy -
          CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).energy =
        ((CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).energy -
            CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).energy) -
          (energyReal rhoL uL pL - energyReal rhoR uR pR)) +
        (energyReal rhoL uL pL - energyReal rhoR uR pR) by ring]
    calc
      |((CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).energy -
          CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).energy) -
        (energyReal rhoL uL pL - energyReal rhoR uR pR)) +
        (energyReal rhoL uL pL - energyReal rhoR uR pR)| ≤
          |(CodeLib.IEEE64.value (Model.sideBits rhoL uL pL).energy -
              CodeLib.IEEE64.value (Model.sideBits rhoR uR pR).energy) -
            (energyReal rhoL uL pL - energyReal rhoR uR pR)| +
          |energyReal rhoL uL pL - energyReal rhoR uR pR| := abs_add_le _ _
      _ ≤ 12 * epsilon + 21 / 8 := add_le_add hjumpInputError henergyDifference
      _ < 4 := by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon]
  have hjumpRaw := jump_approx hsL.energy hsR.energy hjumpRange
  have hjump :
      Approx
        (Model.jumpBits (Model.sideBits rhoL uL pL).energy
          (Model.sideBits rhoR uR pR).energy)
        (energyReal rhoL uL pL - energyReal rhoR uR pR)
        (13 * epsilon) (11 / 4) (21 / 8) := by
    exact hjumpRaw.withBounds (13 * epsilon) (11 / 4) (21 / 8)
      (by ring_nf; exact le_rfl) henergyDifference
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have hdissRaw := dissipation_approx hjump (by norm_num) (by norm_num)
  have hdiss :
      Approx
        (Model.dissipationBits
          (Model.jumpBits (Model.sideBits rhoL uL pL).energy
            (Model.sideBits rhoR uR pR).energy))
        ((7 / 8 : ℝ) *
          (energyReal rhoL uL pL - energyReal rhoR uR pR))
        (17 * epsilon) (37 / 16) (147 / 64) := by
    exact hdissRaw.normalize (17 * epsilon) (37 / 16) (147 / 64)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
      (by ring_nf; exact le_rfl)
      (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  have htarget := energy_rusanov_abs hrealL hrealR
  have hfinalInputs :
      |(CodeLib.IEEE64.value
          (Model.meanBits (Model.sideBits rhoL uL pL).energyFlux
            (Model.sideBits rhoR uR pR).energyFlux) +
        CodeLib.IEEE64.value
          (Model.dissipationBits
            (Model.jumpBits (Model.sideBits rhoL uL pL).energy
              (Model.sideBits rhoR uR pR).energy))) -
        energyRusanovReal rhoL uL pL rhoR uR pR| ≤
          24 * epsilon := by
    have hsum := CodeLib.Numerical.sum_perturbations hmean.error_le hdiss.error_le
    rw [energyRusanovReal]
    calc
      _ ≤ 7 * epsilon + 17 * epsilon := hsum
      _ = 24 * epsilon := by ring
  have hfinalRange :
      |CodeLib.IEEE64.value
          (Model.meanBits (Model.sideBits rhoL uL pL).energyFlux
            (Model.sideBits rhoR uR pR).energyFlux) +
        CodeLib.IEEE64.value
          (Model.dissipationBits
            (Model.jumpBits (Model.sideBits rhoL uL pL).energy
              (Model.sideBits rhoR uR pR).energy))| < (4 : ℝ) := by
    rw [show CodeLib.IEEE64.value
          (Model.meanBits (Model.sideBits rhoL uL pL).energyFlux
            (Model.sideBits rhoR uR pR).energyFlux) +
        CodeLib.IEEE64.value
          (Model.dissipationBits
            (Model.jumpBits (Model.sideBits rhoL uL pL).energy
              (Model.sideBits rhoR uR pR).energy)) =
      ((CodeLib.IEEE64.value
          (Model.meanBits (Model.sideBits rhoL uL pL).energyFlux
            (Model.sideBits rhoR uR pR).energyFlux) +
        CodeLib.IEEE64.value
          (Model.dissipationBits
            (Model.jumpBits (Model.sideBits rhoL uL pL).energy
              (Model.sideBits rhoR uR pR).energy))) -
        energyRusanovReal rhoL uL pL rhoR uR pR) +
      energyRusanovReal rhoL uL pL rhoR uR pR by ring]
    calc
      |((CodeLib.IEEE64.value
          (Model.meanBits (Model.sideBits rhoL uL pL).energyFlux
            (Model.sideBits rhoR uR pR).energyFlux) +
        CodeLib.IEEE64.value
          (Model.dissipationBits
            (Model.jumpBits (Model.sideBits rhoL uL pL).energy
              (Model.sideBits rhoR uR pR).energy))) -
        energyRusanovReal rhoL uL pL rhoR uR pR) +
        energyRusanovReal rhoL uL pL rhoR uR pR| ≤
          |(CodeLib.IEEE64.value
              (Model.meanBits (Model.sideBits rhoL uL pL).energyFlux
                (Model.sideBits rhoR uR pR).energyFlux) +
            CodeLib.IEEE64.value
              (Model.dissipationBits
                (Model.jumpBits (Model.sideBits rhoL uL pL).energy
                  (Model.sideBits rhoR uR pR).energy))) -
            energyRusanovReal rhoL uL pL rhoR uR pR| +
          |energyRusanovReal rhoL uL pL rhoR uR pR| := abs_add_le _ _
      _ ≤ 24 * epsilon + 1029 / 320 := add_le_add hfinalInputs htarget
      _ < 4 := by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon]
  have hresultRaw := approx_add_of_sum_lt_four hmean hdiss hfinalRange
  have hresult := hresultRaw.withBounds
    (25 * epsilon) (13 / 4) (1029 / 320)
    (by ring_nf; exact le_rfl) htarget
    (by norm_num [epsilon, CodeLib.Numerical.Kernels.f64Epsilon])
  simpa [Model.rusanovComponentBits, energyRusanovReal] using hresult

/-! ## Public componentwise contract -/

/-- Conservative absolute-error budget for the mass component. -/
noncomputable def massErrorBudget : ℝ :=
  10 * CodeLib.Numerical.Kernels.f64Epsilon

/-- Conservative absolute-error budget for the momentum component. -/
noncomputable def momentumErrorBudget : ℝ :=
  14 * CodeLib.Numerical.Kernels.f64Epsilon

/-- Conservative absolute-error budget for the energy component.  Its proof
includes the correlated strict-headroom argument above. -/
noncomputable def energyErrorBudget : ℝ :=
  25 * CodeLib.Numerical.Kernels.f64Epsilon

/-- Finite component words and their absolute errors against the independent
exact-real fixed-speed Rusanov flux. -/
structure FluxRealError
    (rhoL uL pL rhoR uR pR : UInt64) (result : Model.FluxBits) : Prop where
  massFinite : CodeLib.IEEE64.Finite result.mass
  momentumFinite : CodeLib.IEEE64.Finite result.momentum
  energyFinite : CodeLib.IEEE64.Finite result.energy
  massError :
    |CodeLib.IEEE64.value result.mass -
      (Model.rusanovRealOfBits rhoL uL pL rhoR uR pR).mass| ≤ massErrorBudget
  momentumError :
    |CodeLib.IEEE64.value result.momentum -
      (Model.rusanovRealOfBits rhoL uL pL rhoR uR pR).momentum| ≤
        momentumErrorBudget
  energyError :
    |CodeLib.IEEE64.value result.energy -
      (Model.rusanovRealOfBits rhoL uL pL rhoR uR pR).energy| ≤
        energyErrorBudget

private theorem mass_target_eq :
    massRusanovReal rhoL uL rhoR uR =
      (Model.rusanovRealOfBits rhoL uL pL rhoR uR pR).mass := by
  rfl

private theorem momentum_target_eq :
    momentumRusanovReal rhoL uL pL rhoR uR pR =
      (Model.rusanovRealOfBits rhoL uL pL rhoR uR pR).momentum := by
  rfl

private theorem energy_target_eq :
    energyRusanovReal rhoL uL pL rhoR uR pR =
      (Model.rusanovRealOfBits rhoL uL pL rhoR uR pR).energy := by
  simp only [energyRusanovReal, energyFluxReal, enthalpyReal, energyReal,
    kineticReal, massReal, Model.rusanovRealOfBits, Model.rusanovReal,
    Model.primitiveRealOfBits, Model.eulerFluxReal,
    Model.conservativeReal]
  ring

/-- Accepted left and right primitive states produce finite pure-model words
with explicit componentwise absolute-error budgets. -/
theorem rusanovBits_real_error_of_stateBounds
    (hleft : Bounds.StateBounds rhoL uL pL)
    (hright : Bounds.StateBounds rhoR uR pR) :
    FluxRealError rhoL uL pL rhoR uR pR
      (Model.rusanovBits rhoL uL pL rhoR uR pR) := by
  have hmass := mass_component_approx hleft hright
  have hmomentum := momentum_component_approx hleft hright
  have henergy := energy_component_approx hleft hright
  refine
    { massFinite := ?_
      momentumFinite := ?_
      energyFinite := ?_
      massError := ?_
      momentumError := ?_
      energyError := ?_ }
  · simpa [Model.rusanovBits] using hmass.finite
  · simpa [Model.rusanovBits] using hmomentum.finite
  · simpa [Model.rusanovBits] using henergy.finite
  · have h := hmass.error_le
    rw [mass_target_eq (rhoL := rhoL) (uL := uL) (pL := pL)
      (rhoR := rhoR) (uR := uR) (pR := pR)] at h
    simpa only [Model.rusanovBits, massErrorBudget, epsilon] using h
  · have h := hmomentum.error_le
    rw [momentum_target_eq (rhoL := rhoL) (uL := uL) (pL := pL)
      (rhoR := rhoR) (uR := uR) (pR := pR)] at h
    simpa only [Model.rusanovBits, momentumErrorBudget, epsilon] using h
  · have h := henergy.error_le
    rw [energy_target_eq (rhoL := rhoL) (uL := uL) (pL := pL)
      (rhoR := rhoR) (uR := uR) (pR := pR)] at h
    simpa only [Model.rusanovBits, energyErrorBudget, epsilon] using h

/-- Guard-shaped corollary used by the total checked model. -/
theorem rusanovBits_real_error_of_guard
    (hguard : Model.eulerGuard rhoL uL pL rhoR uR pR = true) :
    FluxRealError rhoL uL pL rhoR uR pR
      (Model.rusanovBits rhoL uL pL rhoR uR pR) := by
  have hbounds := Bounds.eulerGuard_spec rhoL uL pL rhoR uR pR hguard
  exact rusanovBits_real_error_of_stateBounds hbounds.1 hbounds.2

/-- The accepted branch of the total checked bit model has status zero and
inherits the finite/error theorem.  This is a pure model result, not a claim
about generated-Wasm execution. -/
theorem checkedFluxBitsModel_real_error_of_guard
    (hguard : Model.eulerGuard rhoL uL pL rhoR uR pR = true) :
    let result := Model.checkedFluxBitsModel rhoL uL pL rhoR uR pR
    result.status = 0 ∧
      FluxRealError rhoL uL pL rhoR uR pR
        { mass := result.mass, momentum := result.momentum,
          energy := result.energy } := by
  have hnumeric := rusanovBits_real_error_of_guard hguard
  have hmodel :
      Model.checkedFluxBitsModel rhoL uL pL rhoR uR pR =
        { status := 0
          mass := (Model.rusanovBits rhoL uL pL rhoR uR pR).mass
          momentum := (Model.rusanovBits rhoL uL pL rhoR uR pR).momentum
          energy := (Model.rusanovBits rhoL uL pL rhoR uR pR).energy } := by
    simp [Model.checkedFluxBitsModel, hguard]
  rw [hmodel]
  exact ⟨rfl, by simpa only [Model.rusanovBits] using hnumeric⟩

#print axioms rusanovBits_real_error_of_stateBounds
#print axioms rusanovBits_real_error_of_guard
#print axioms checkedFluxBitsModel_real_error_of_guard

end Project.EulerRusanov.Numerical
