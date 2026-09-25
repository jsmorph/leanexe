import Project.EulerRiemann.FrozenNumericsSideFinite
import Project.ProofKit.F64QuotientResidual
import Project.ProofKit.F64ErrorPropagation

namespace Project.EulerRiemann.Frozen.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64RoundingResidual
set_option exponentiation.threshold 4096
noncomputable section

structure SideErrorBounds where
  pressure : ℝ
  momentum : ℝ
  transverse : ℝ
  energy : ℝ

def sideErrorBounds (rho mx my energy : UInt64) : SideErrorBounds :=
  let u := Wasm.IEEE64.div mx rho
  let v := Wasm.IEEE64.div my rho
  let tx := Wasm.IEEE64.mul mx u
  let ty := Wasm.IEEE64.mul my v
  let total := Wasm.IEEE64.add tx ty
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 total
  let internal := Wasm.IEEE64.sub energy kinetic
  let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
  let enthalpy := Wasm.IEEE64.add energy pressure
  let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
  let txError := radius tx + |value mx| * radius u
  let tyError := radius ty + |value my| * radius v
  let sumError := radius total + (txError + tyError)
  let internalError := radius internal + (radius kinetic + (1 / 2) * sumError)
  let pressureError := radius pressure + (|value 0x3FD999999999999A| * internalError +
    |value 0x3FD999999999999A - 2 / 5| * |I|)
  ⟨pressureError,
    radius (Wasm.IEEE64.add tx pressure) + (txError + pressureError),
    radius (Wasm.IEEE64.mul my u) + |value my| * radius u,
    radius (Wasm.IEEE64.mul u enthalpy) +
      (|value u| * (radius enthalpy + pressureError) +
        radius u * |value energy + (2 / 5) * I|)⟩

theorem physical_side_reference_bound (rho mx my energy : UInt64)
    (input : Project.Euler2DConservative.Guard.StateBounds rho mx my energy)
    (finite : SideFinite rho mx my energy) :
    let u := Wasm.IEEE64.div mx rho
    let v := Wasm.IEEE64.div my rho
    let tx := Wasm.IEEE64.mul mx u
    let ty := Wasm.IEEE64.mul my v
    let internal := Wasm.IEEE64.sub energy (Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.add tx ty))
    let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
    let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
    let bound := sideErrorBounds rho mx my energy
    |value pressure - (2 / 5) * I| ≤ bound.pressure ∧
    |value (Wasm.IEEE64.add tx pressure) - ((value mx)^2 / value rho + (2 / 5) * I)| ≤ bound.momentum ∧
    |value (Wasm.IEEE64.mul my u) - value mx * value my / value rho| ≤ bound.transverse ∧
    |value (Wasm.IEEE64.mul u (Wasm.IEEE64.add energy pressure)) -
      (value energy + (2 / 5) * I) * (value mx / value rho)| ≤ bound.energy := by
  obtain ⟨hu, hv, htx, hty, htotal, hkinetic, hi, hp, hnormal, htransverse, henthalpy, heflux⟩ := finite
  have hr0 : Wasm.IEEE64.scaledMagnitude rho ≠ 0 := by
    intro hz
    have hzValue : value rho = 0 := by
      simp [value, Wasm.IEEE64.scaledValue, hz]
    have := input.densityPositive
    linarith
  have halfFinite : CodeLib.IEEE64.Finite 0x3FE0000000000000 := by
    unfold CodeLib.IEEE64.Finite
    decide
  have halfValue : value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have coefficientFinite : CodeLib.IEEE64.Finite 0x3FD999999999999A := by
    unfold CodeLib.IEEE64.Finite
    decide
  have eu := div_error mx rho input.momentumFinite input.densityFinite hr0 hu
  have ev := div_error my rho input.transverseFinite input.densityFinite hr0 hv
  have etx := Project.ProofKit.F64ErrorPropagation.mul mx _ (value mx) _ 0 _
    input.momentumFinite hu htx (by simp) eu
  have ety := Project.ProofKit.F64ErrorPropagation.mul my _ (value my) _ 0 _
    input.transverseFinite hv hty (by simp) ev
  simp only [zero_mul, add_zero] at etx ety
  have esum := Project.ProofKit.F64ErrorPropagation.add _ _ _ _ _ _ htx hty htotal etx ety
  have ek := Project.ProofKit.F64ErrorPropagation.mul 0x3FE0000000000000 _ (1 / 2) _ 0 _
    halfFinite htotal hkinetic (by rw [halfValue]; simp) esum
  simp only [halfValue, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), zero_mul, add_zero] at ek
  have ei := Project.ProofKit.F64ErrorPropagation.sub energy _ (value energy) _ 0 _
    input.energyFinite hkinetic hi (by simp) ek
  simp only [zero_add] at ei
  have internalIdentity : value energy - (1 / 2) *
      (value mx * (value mx / value rho) + value my * (value my / value rho)) =
      value energy - ((value mx)^2 + (value my)^2) / (2 * value rho) := by
    field_simp [ne_of_gt input.densityPositive]
  rw [internalIdentity] at ei
  have ep := Project.ProofKit.F64ErrorPropagation.mul 0x3FD999999999999A _ (2 / 5) _ _ _
    coefficientFinite hi hp le_rfl ei
  have en := Project.ProofKit.F64ErrorPropagation.add _ _ _ _ _ _ htx hp hnormal etx ep
  have et := Project.ProofKit.F64ErrorPropagation.mul my _ (value my) _ 0 _
    input.transverseFinite hu htransverse (by simp) eu
  simp only [zero_mul, add_zero] at et
  have eh := Project.ProofKit.F64ErrorPropagation.add energy _ (value energy) _ 0 _
    input.energyFinite hp henthalpy (by simp) ep
  simp only [zero_add] at eh
  have ee := Project.ProofKit.F64ErrorPropagation.mul _ _ _ _ _ _ hu henthalpy heflux eu eh
  dsimp only
  refine ⟨ep, ?_, ?_, ?_⟩
  · convert en using 1 <;> first | rfl | ring
  · convert et using 1 <;> first | rfl | ring
  · convert ee using 1 <;> first | rfl | ring

theorem accepted_side_reference_bound (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
    let side := sideCheckedBits rho mx my energy
    let bound := sideErrorBounds rho mx my energy
    value side.massFlux = value mx ∧
    |value side.pressure - (2 / 5) * I| ≤ bound.pressure ∧
    |value side.momentumFlux - ((value mx)^2 / value rho + (2 / 5) * I)| ≤ bound.momentum ∧
    |value side.transverseFlux - value mx * value my / value rho| ≤ bound.transverse ∧
    |value side.energyFlux - (value energy + (2 / 5) * I) * (value mx / value rho)| ≤
      bound.energy := by
  have input := stateGuard_spec rho mx my energy (side_inputGuard rho mx my energy h)
  have bound := physical_side_reference_bound rho mx my energy input
    (accepted_side_finite rho mx my energy h)
  dsimp only
  rw [side_values_of_accepted rho mx my energy h]
  exact ⟨rfl, bound⟩

#print axioms physical_side_reference_bound
#print axioms accepted_side_reference_bound
end
end Project.EulerRiemann.Frozen.Numerics
