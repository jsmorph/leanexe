import Project.EulerRusanov.Model
import Project.ProofKit.F64Bounds

/-!
# Input-domain bounds for the guarded Euler--Rusanov flux

The executable guard compares raw `UInt64` words before any floating-point
instruction is reached.  This module justifies that design: on the admitted
positive-normal interval, unsigned binary64 word order agrees with real-value
order.  It also reuses the shared sign-clearing theorem for velocity and proves
that the fixed `7 / 4` signal bound dominates the ideal-gas acoustic estimate.
-/

namespace Project.EulerRusanov.Bounds

open Wasm

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

open Project.EulerRusanov

/-! ## Boolean guard decomposition -/

theorem densityGuard_eq_true_iff (rho : UInt64) :
    Model.densityGuard rho = true ↔
      Model.rhoMinBits ≤ rho ∧ rho ≤ Model.rhoMaxBits := by
  simp [Model.densityGuard]

theorem pressureGuard_eq_true_iff (rho p : UInt64) :
    Model.pressureGuard rho p = true ↔
      Model.pressureMinBits ≤ p ∧ p ≤ rho := by
  simp [Model.pressureGuard]

theorem velocityGuard_eq_true_iff (u : UInt64) :
    Model.velocityGuard u = true ↔
      Model.magnitudeBits u ≤ Model.velocityMaxBits := by
  simp [Model.velocityGuard]

theorem stateGuard_eq_true_iff (rho u p : UInt64) :
    Model.stateGuard rho u p = true ↔
      Model.densityGuard rho = true ∧
      Model.pressureGuard rho p = true ∧
      Model.velocityGuard u = true := by
  simp [Model.stateGuard, and_assoc]

theorem eulerGuard_eq_true_iff
    (rhoL uL pL rhoR uR pR : UInt64) :
    Model.eulerGuard rhoL uL pL rhoR uR pR = true ↔
      Model.stateGuard rhoL uL pL = true ∧
      Model.stateGuard rhoR uR pR = true := by
  simp [Model.eulerGuard, Model.stateGuard, Model.densityGuard,
    Model.pressureGuard, Model.velocityGuard, and_assoc]

/-! ## Positive-normal raw words -/

/-- Integer field analysis common to density and pressure.  `minimumExponent`
is the biased exponent of a positive, fraction-zero lower endpoint.  The
upper endpoint is the binary64 encoding of one. -/
private theorem positiveNormalScaledBounds
    (bits : UInt64) (minimumExponent : Nat)
    (hminimumExponent : 1 ≤ minimumExponent)
    (hmaximumExponent : minimumExponent ≤ 1023)
    (hlower : minimumExponent * 2 ^ 52 ≤ bits.toNat)
    (hupper : bits.toNat ≤ 1023 * 2 ^ 52) :
    CodeLib.IEEE64.Finite bits ∧
      Wasm.IEEE64.sign bits = false ∧
      2 ^ (minimumExponent + 51) ≤ Wasm.IEEE64.scaledMagnitude bits ∧
      Wasm.IEEE64.scaledMagnitude bits ≤ 2 ^ 1074 := by
  let exponentField := bits.toNat / 2 ^ 52
  let fractionField := bits.toNat % 2 ^ 52
  have hfractionLt : fractionField < 2 ^ 52 := by
    exact Nat.mod_lt _ (by positivity)
  have hdecomp :
      bits.toNat = exponentField * 2 ^ 52 + fractionField := by
    dsimp [exponentField, fractionField]
    exact (Nat.div_add_mod' bits.toNat (2 ^ 52)).symm
  have hexponentLower : minimumExponent ≤ exponentField := by
    omega
  have hexponentUpper : exponentField ≤ 1023 := by
    omega
  have hquotientLt : bits.toNat / 2 ^ 52 < 2 ^ 11 := by
    change exponentField < 2 ^ 11
    norm_num
    omega
  have hexponent :
      Wasm.IEEE64.exponent bits = exponentField := by
    change bits.toNat / 2 ^ 52 % 2 ^ 11 = exponentField
    rw [Nat.mod_eq_of_lt hquotientLt]
  have hfraction :
      Wasm.IEEE64.fraction bits = fractionField := rfl
  have hbitsLt : bits.toNat < 2 ^ 63 := by
    norm_num at hupper ⊢
    omega
  have hsign : Wasm.IEEE64.sign bits = false := by
    rw [Wasm.IEEE64.sign, decide_eq_false_iff_not]
    exact Nat.not_le_of_lt hbitsLt
  have hfinite : CodeLib.IEEE64.Finite bits := by
    simp [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hexponent,
      show exponentField ≠ 0x7FF by omega]
  have hexponentNonzero : exponentField ≠ 0 := by omega
  have hscaled :
      Wasm.IEEE64.scaledMagnitude bits =
        (2 ^ 52 + fractionField) * 2 ^ (exponentField - 1) := by
    simp [Wasm.IEEE64.scaledMagnitude, hexponent, hfraction,
      hexponentNonzero]
  have hscaledLower :
      2 ^ (minimumExponent + 51) ≤
        Wasm.IEEE64.scaledMagnitude bits := by
    rw [hscaled]
    have hpower :
        2 ^ (minimumExponent - 1) ≤ 2 ^ (exponentField - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    calc
      2 ^ (minimumExponent + 51) =
          2 ^ 52 * 2 ^ (minimumExponent - 1) := by
            rw [← pow_add]
            congr 1
            omega
      _ ≤ (2 ^ 52 + fractionField) * 2 ^ (exponentField - 1) :=
        Nat.mul_le_mul (by omega) hpower
  have hscaledUpper :
      Wasm.IEEE64.scaledMagnitude bits ≤ 2 ^ 1074 := by
    rw [hscaled]
    by_cases htop : exponentField = 1023
    · have hfractionZero : fractionField = 0 := by omega
      rw [htop, hfractionZero]
      norm_num [pow_add]
    · have hexponentSmall : exponentField ≤ 1022 := by omega
      have hsignificand : 2 ^ 52 + fractionField ≤ 2 ^ 53 := by
        calc
          2 ^ 52 + fractionField ≤ 2 ^ 52 + 2 ^ 52 :=
            Nat.add_le_add_left (Nat.le_of_lt hfractionLt) _
          _ = 2 ^ 53 := by norm_num
      have hpower : 2 ^ (exponentField - 1) ≤ 2 ^ 1021 :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      calc
        (2 ^ 52 + fractionField) * 2 ^ (exponentField - 1) ≤
            2 ^ 53 * 2 ^ 1021 := Nat.mul_le_mul hsignificand hpower
        _ = 2 ^ 1074 := by rw [← pow_add]
  exact ⟨hfinite, hsign, hscaledLower, hscaledUpper⟩

/-- Real-value form of `positiveNormalScaledBounds`. -/
private theorem positiveNormalRealBounds
    (bits : UInt64) (minimumExponent : Nat)
    (hminimumExponent : 1 ≤ minimumExponent)
    (hmaximumExponent : minimumExponent ≤ 1023)
    (hlower : minimumExponent * 2 ^ 52 ≤ bits.toNat)
    (hupper : bits.toNat ≤ 1023 * 2 ^ 52) :
    CodeLib.IEEE64.Finite bits ∧
      (2 : ℝ) ^ (minimumExponent + 51) / (2 : ℝ) ^ 1074 ≤
        CodeLib.IEEE64.value bits ∧
      CodeLib.IEEE64.value bits ≤ 1 := by
  have hscaled := positiveNormalScaledBounds bits minimumExponent
    hminimumExponent hmaximumExponent hlower hupper
  have hscaledValue :
      Wasm.IEEE64.scaledValue bits =
        (Wasm.IEEE64.scaledMagnitude bits : Int) := by
    simp [Wasm.IEEE64.scaledValue, hscaled.2.1]
  have hlowerReal :
      (2 : ℝ) ^ (minimumExponent + 51) ≤
        (Wasm.IEEE64.scaledMagnitude bits : ℝ) := by
    exact_mod_cast hscaled.2.2.1
  have hupperReal :
      (Wasm.IEEE64.scaledMagnitude bits : ℝ) ≤ (2 : ℝ) ^ 1074 := by
    exact_mod_cast hscaled.2.2.2
  have hdenominator : 0 < (2 : ℝ) ^ 1074 := by positivity
  refine ⟨hscaled.1, ?_, ?_⟩
  · rw [CodeLib.IEEE64.value, hscaledValue]
    simpa using div_le_div_of_nonneg_right hlowerReal hdenominator.le
  · rw [CodeLib.IEEE64.value, hscaledValue]
    apply (div_le_one hdenominator).2
    simpa using hupperReal

/-- Unsigned word order is monotone in real value throughout the guarded
positive-normal range. -/
private theorem positiveNormalValue_mono
    (left right : UInt64)
    (hleftLower : 1019 * 2 ^ 52 ≤ left.toNat)
    (hrightUpper : right.toNat ≤ 1023 * 2 ^ 52)
    (hle : left ≤ right) :
    CodeLib.IEEE64.value left ≤ CodeLib.IEEE64.value right := by
  let leftExponent := left.toNat / 2 ^ 52
  let leftFraction := left.toNat % 2 ^ 52
  let rightExponent := right.toNat / 2 ^ 52
  let rightFraction := right.toNat % 2 ^ 52
  have hleNat : left.toNat ≤ right.toNat := UInt64.le_iff_toNat_le.mp hle
  have hleftUpper : left.toNat ≤ 1023 * 2 ^ 52 := hleNat.trans hrightUpper
  have hleftFields := positiveNormalScaledBounds left 1019
    (by norm_num) (by norm_num) hleftLower hleftUpper
  have hrightLower : 1019 * 2 ^ 52 ≤ right.toNat :=
    hleftLower.trans hleNat
  have hrightFields := positiveNormalScaledBounds right 1019
    (by norm_num) (by norm_num) hrightLower hrightUpper
  have hleftFractionLt : leftFraction < 2 ^ 52 :=
    Nat.mod_lt _ (by positivity)
  have hrightFractionLt : rightFraction < 2 ^ 52 :=
    Nat.mod_lt _ (by positivity)
  have hleftDecomp :
      left.toNat = leftExponent * 2 ^ 52 + leftFraction := by
    dsimp [leftExponent, leftFraction]
    exact (Nat.div_add_mod' left.toNat (2 ^ 52)).symm
  have hrightDecomp :
      right.toNat = rightExponent * 2 ^ 52 + rightFraction := by
    dsimp [rightExponent, rightFraction]
    exact (Nat.div_add_mod' right.toNat (2 ^ 52)).symm
  have hleftExponent :
      Wasm.IEEE64.exponent left = leftExponent := by
    have hq : left.toNat / 2 ^ 52 < 2 ^ 11 := by
      change leftExponent < 2 ^ 11
      norm_num
      omega
    change left.toNat / 2 ^ 52 % 2 ^ 11 = leftExponent
    rw [Nat.mod_eq_of_lt hq]
  have hrightExponent :
      Wasm.IEEE64.exponent right = rightExponent := by
    have hq : right.toNat / 2 ^ 52 < 2 ^ 11 := by
      change rightExponent < 2 ^ 11
      norm_num
      omega
    change right.toNat / 2 ^ 52 % 2 ^ 11 = rightExponent
    rw [Nat.mod_eq_of_lt hq]
  have hleftExponentLower : 1019 ≤ leftExponent := by omega
  have hrightExponentLower : 1019 ≤ rightExponent := by omega
  have hscaledLeft :
      Wasm.IEEE64.scaledMagnitude left =
        (2 ^ 52 + leftFraction) * 2 ^ (leftExponent - 1) := by
    simp [Wasm.IEEE64.scaledMagnitude, hleftExponent,
      show Wasm.IEEE64.fraction left = leftFraction from rfl,
      show leftExponent ≠ 0 by omega]
  have hscaledRight :
      Wasm.IEEE64.scaledMagnitude right =
        (2 ^ 52 + rightFraction) * 2 ^ (rightExponent - 1) := by
    simp [Wasm.IEEE64.scaledMagnitude, hrightExponent,
      show Wasm.IEEE64.fraction right = rightFraction from rfl,
      show rightExponent ≠ 0 by omega]
  have hscaledMono :
      Wasm.IEEE64.scaledMagnitude left ≤
        Wasm.IEEE64.scaledMagnitude right := by
    rw [hscaledLeft, hscaledRight]
    by_cases heq : leftExponent = rightExponent
    · rw [← heq]
      have hfractionLe : leftFraction ≤ rightFraction := by omega
      exact Nat.mul_le_mul_right _ (Nat.add_le_add_left hfractionLe _)
    · have hexponentLt : leftExponent < rightExponent := by omega
      have hleftSignificand : 2 ^ 52 + leftFraction ≤ 2 ^ 53 := by
        calc
          2 ^ 52 + leftFraction ≤ 2 ^ 52 + 2 ^ 52 :=
            Nat.add_le_add_left (Nat.le_of_lt hleftFractionLt) _
          _ = 2 ^ 53 := by norm_num
      have hpower : 2 ^ leftExponent ≤ 2 ^ (rightExponent - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      calc
        (2 ^ 52 + leftFraction) * 2 ^ (leftExponent - 1) ≤
            2 ^ 53 * 2 ^ (leftExponent - 1) :=
          Nat.mul_le_mul_right _ hleftSignificand
        _ = 2 ^ 52 * 2 ^ leftExponent := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ 52 * 2 ^ (rightExponent - 1) :=
          Nat.mul_le_mul_left _ hpower
        _ ≤ (2 ^ 52 + rightFraction) *
            2 ^ (rightExponent - 1) :=
          Nat.mul_le_mul_right _ (by omega)
  have hscaledValueLeft :
      Wasm.IEEE64.scaledValue left =
        (Wasm.IEEE64.scaledMagnitude left : Int) := by
    simp [Wasm.IEEE64.scaledValue, hleftFields.2.1]
  have hscaledValueRight :
      Wasm.IEEE64.scaledValue right =
        (Wasm.IEEE64.scaledMagnitude right : Int) := by
    simp [Wasm.IEEE64.scaledValue, hrightFields.2.1]
  have hscaledMonoReal :
      (Wasm.IEEE64.scaledValue left : ℝ) ≤
        (Wasm.IEEE64.scaledValue right : ℝ) := by
    rw [hscaledValueLeft, hscaledValueRight]
    exact_mod_cast hscaledMono
  simp only [CodeLib.IEEE64.value]
  exact div_le_div_of_nonneg_right hscaledMonoReal (by positivity)

/-! ## Public state bounds -/

/-- All real and finiteness facts supplied by one successful raw-word guard. -/
structure StateBounds (rho u p : UInt64) : Prop where
  densityFinite : CodeLib.IEEE64.Finite rho
  velocityFinite : CodeLib.IEEE64.Finite u
  pressureFinite : CodeLib.IEEE64.Finite p
  densityLower : (1 : ℝ) / 8 ≤ CodeLib.IEEE64.value rho
  densityUpper : CodeLib.IEEE64.value rho ≤ 1
  velocityAbs : |CodeLib.IEEE64.value u| ≤ (1 : ℝ) / 2
  pressureLower : (1 : ℝ) / 16 ≤ CodeLib.IEEE64.value p
  pressureLeDensity : CodeLib.IEEE64.value p ≤ CodeLib.IEEE64.value rho

theorem densityGuard_spec (rho : UInt64)
    (hguard : Model.densityGuard rho = true) :
    CodeLib.IEEE64.Finite rho ∧
      (1 : ℝ) / 8 ≤ CodeLib.IEEE64.value rho ∧
      CodeLib.IEEE64.value rho ≤ 1 := by
  have hraw := (densityGuard_eq_true_iff rho).mp hguard
  have hlower := UInt64.le_iff_toNat_le.mp hraw.1
  have hupper := UInt64.le_iff_toNat_le.mp hraw.2
  change (Model.rhoMinBits).toNat ≤ rho.toNat at hlower
  change rho.toNat ≤ (Model.rhoMaxBits).toNat at hupper
  norm_num [Model.rhoMinBits] at hlower
  norm_num [Model.rhoMaxBits] at hupper
  have hbounds := positiveNormalRealBounds rho 1020
    (by norm_num) (by norm_num) hlower hupper
  refine ⟨hbounds.1, ?_, hbounds.2.2⟩
  convert hbounds.2.1 using 1
  all_goals norm_num [pow_succ]

theorem velocityGuard_spec (u : UInt64)
    (hguard : Model.velocityGuard u = true) :
    CodeLib.IEEE64.Finite u ∧
      |CodeLib.IEEE64.value u| ≤ (1 : ℝ) / 2 := by
  apply Project.ProofKit.F64Bounds.boundedByHalf_spec u
  have hguardsEqual :
      Model.velocityGuard u =
        Project.ProofKit.F64Bounds.boundedByHalfBits u := by
    rfl
  rw [← hguardsEqual]
  exact hguard

theorem pressureGuard_spec (rho p : UInt64)
    (hdensity : Model.densityGuard rho = true)
    (hpressure : Model.pressureGuard rho p = true) :
    CodeLib.IEEE64.Finite p ∧
      (1 : ℝ) / 16 ≤ CodeLib.IEEE64.value p ∧
      CodeLib.IEEE64.value p ≤ CodeLib.IEEE64.value rho := by
  have hdensityRaw := (densityGuard_eq_true_iff rho).mp hdensity
  have hpressureRaw := (pressureGuard_eq_true_iff rho p).mp hpressure
  have hpLower := UInt64.le_iff_toNat_le.mp hpressureRaw.1
  have hpUpper : p.toNat ≤ 1023 * 2 ^ 52 := by
    have hpRho := UInt64.le_iff_toNat_le.mp hpressureRaw.2
    have hrhoUpper := UInt64.le_iff_toNat_le.mp hdensityRaw.2
    change p.toNat ≤ rho.toNat at hpRho
    change rho.toNat ≤ (Model.rhoMaxBits).toNat at hrhoUpper
    norm_num [Model.rhoMaxBits] at hrhoUpper
    exact hpRho.trans hrhoUpper
  change (Model.pressureMinBits).toNat ≤ p.toNat at hpLower
  norm_num [Model.pressureMinBits] at hpLower
  have hpBounds := positiveNormalRealBounds p 1019
    (by norm_num) (by norm_num) hpLower hpUpper
  have hpRho : CodeLib.IEEE64.value p ≤ CodeLib.IEEE64.value rho := by
    apply positiveNormalValue_mono p rho hpLower
    · have hrhoUpper := UInt64.le_iff_toNat_le.mp hdensityRaw.2
      change rho.toNat ≤ (Model.rhoMaxBits).toNat at hrhoUpper
      norm_num [Model.rhoMaxBits] at hrhoUpper
      exact hrhoUpper
    · exact hpressureRaw.2
  refine ⟨hpBounds.1, ?_, hpRho⟩
  convert hpBounds.2.1 using 1
  all_goals norm_num [pow_succ]

theorem stateGuard_spec (rho u p : UInt64)
    (hguard : Model.stateGuard rho u p = true) :
    StateBounds rho u p := by
  have hparts := (stateGuard_eq_true_iff rho u p).mp hguard
  have hdensity := densityGuard_spec rho hparts.1
  have hpressure := pressureGuard_spec rho p hparts.1 hparts.2.1
  have hvelocity := velocityGuard_spec u hparts.2.2
  exact
    { densityFinite := hdensity.1
      velocityFinite := hvelocity.1
      pressureFinite := hpressure.1
      densityLower := hdensity.2.1
      densityUpper := hdensity.2.2
      velocityAbs := hvelocity.2
      pressureLower := hpressure.2.1
      pressureLeDensity := hpressure.2.2 }

theorem eulerGuard_spec
    (rhoL uL pL rhoR uR pR : UInt64)
    (hguard : Model.eulerGuard rhoL uL pL rhoR uR pR = true) :
    StateBounds rhoL uL pL ∧ StateBounds rhoR uR pR := by
  have hparts := (eulerGuard_eq_true_iff rhoL uL pL rhoR uR pR).mp hguard
  exact ⟨stateGuard_spec rhoL uL pL hparts.1,
    stateGuard_spec rhoR uR pR hparts.2⟩

theorem StateBounds.densityAbs (h : StateBounds rho u p) :
    |CodeLib.IEEE64.value rho| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [h.densityLower])]
  exact h.densityUpper

theorem StateBounds.pressureAbs (h : StateBounds rho u p) :
    |CodeLib.IEEE64.value p| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [h.pressureLower])]
  exact h.pressureLeDensity.trans h.densityUpper

/-! ## Fixed signal-speed certificate -/

/-- The fixed `alpha = 7 / 4` dominates `|u| + sqrt(gamma * p / rho)`
throughout the admitted primitive-state domain.  The rational margin is
explicit: `sqrt(7 / 5) < 5 / 4`. -/
theorem signalSpeed_le_alpha
    (rho velocity pressure : ℝ)
    (hrho : (1 : ℝ) / 8 ≤ rho)
    (hvelocity : |velocity| ≤ (1 : ℝ) / 2)
    (hpressure : 0 ≤ pressure)
    (hpressureRho : pressure ≤ rho) :
    |velocity| + Real.sqrt (Model.gammaReal * pressure / rho) ≤
      Model.alphaReal := by
  have hrhoPositive : 0 < rho := by linarith
  have hratioNonnegative : 0 ≤ pressure / rho :=
    div_nonneg hpressure hrhoPositive.le
  have hratio : pressure / rho ≤ 1 :=
    (div_le_one hrhoPositive).2 hpressureRho
  have hradicandNonnegative :
      0 ≤ Model.gammaReal * pressure / rho := by
    rw [show Model.gammaReal * pressure / rho =
      Model.gammaReal * (pressure / rho) by ring]
    exact mul_nonneg (by norm_num [Model.gammaReal]) hratioNonnegative
  have hradicandBound :
      Model.gammaReal * pressure / rho ≤ ((5 : ℝ) / 4) ^ 2 := by
    rw [show Model.gammaReal * pressure / rho =
      Model.gammaReal * (pressure / rho) by ring]
    have hgamma : Model.gammaReal = (7 : ℝ) / 5 := rfl
    rw [hgamma]
    nlinarith
  have hsqrt :
      Real.sqrt (Model.gammaReal * pressure / rho) ≤ (5 : ℝ) / 4 := by
    exact (Real.sqrt_le_left (by norm_num)).2 hradicandBound
  rw [Model.alphaReal]
  linarith

theorem StateBounds.signalSpeed_le_alpha (h : StateBounds rho u p) :
    |CodeLib.IEEE64.value u| +
        Real.sqrt
          (Model.gammaReal * CodeLib.IEEE64.value p /
            CodeLib.IEEE64.value rho) ≤ Model.alphaReal := by
  apply Project.EulerRusanov.Bounds.signalSpeed_le_alpha
  · exact h.densityLower
  · exact h.velocityAbs
  · linarith [h.pressureLower]
  · exact h.pressureLeDensity

#print axioms densityGuard_spec
#print axioms velocityGuard_spec
#print axioms pressureGuard_spec
#print axioms stateGuard_spec
#print axioms eulerGuard_spec
#print axioms signalSpeed_le_alpha

end Project.EulerRusanov.Bounds
