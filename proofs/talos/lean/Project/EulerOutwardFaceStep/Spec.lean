import Project.EulerOutwardFaceStep.Execution
import Project.EulerOutwardFaceStep.AnnotationMatches
import Project.EulerRiemann.OutwardFaceStepSpec
import Project.EulerRiemann.OutwardFaceStepResidual

namespace Project.EulerOutwardFaceStep.Spec
open Wasm CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DCellStep.Model (CheckedCell rejectedCell)
open Project.Euler2DConservative.Guard (StateBounds decodedState)
open Project.Euler2DConservative.RealFlux (eigenvalues velocity soundSpeed)
open Project.EulerRiemann
open Project.EulerRiemann.OutwardNumerics (faceStepCheckedBits fluxCheckedBits interfaceErrorBounds)
open Project.EulerRiemann.Numerics (stateWords fluxWords cellWords)
open Project.ProofKit.F64ConservativeUpdate (Certificate)
open Project.ProofKit.F64RoundingResidual (radius)
open Execution (arguments cellValues)

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State),
    TerminatesWith env m 70 initial (arguments ratio center leftOuter leftInner rightInner rightOuter)
      (fun final values => final = initial ∧
        values = cellValues (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter))

def CharacteristicCfl (ratio : ℝ) (face : State) : Prop :=
  ∀ i : Fin 4, ratio * |eigenvalues
    (velocity (decodedState face.density face.mx face.my face.energy))
    (soundSpeed (decodedState face.density face.mx face.my face.energy)) i| ≤ (1 : ℝ) / 2

def Behavior (ratio : UInt64)
    (leftOuter leftInner rightInner rightOuter : State) (values : List Value) : Prop :=
  values = cellValues rejectedCell ∨
    ∃ out : CheckedCell, values = cellValues out ∧ out.status = 0 ∧
      StateBounds out.density out.momentum out.transverse out.energy ∧
      Project.ProofKit.F64Order.positiveBits out.pressure = true ∧
      Project.ProofKit.F64Order.positiveBits ratio = true ∧
      Project.ProofKit.F64Order.positiveBits out.alpha = true ∧
      Finite out.courant ∧ 0 < value out.courant ∧
      value ratio * value out.alpha ≤ value out.courant ∧
      value out.courant ≤ (1 : ℝ) / 2 ∧
      (∀ face ∈ [leftOuter, leftInner, rightInner, rightOuter],
        OutwardMaximum.Bounds face out.alpha ∧ CharacteristicCfl (value ratio) face) ∧
      (∀ (n : Nat) (dt globalAlpha : UInt64),
        (OutwardCfl.gridRatioChecked n dt globalAlpha).status = 0 →
        ratio = (OutwardCfl.gridRatioChecked n dt globalAlpha).value →
        ∀ face ∈ [leftOuter, leftInner, rightInner, rightOuter],
          CharacteristicCfl (value dt * (n : ℝ)) face)

def BehaviorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State),
    TerminatesWith env m 70 initial (arguments ratio center leftOuter leftInner rightInner rightOuter)
      (fun final values => final = initial ∧ Behavior ratio leftOuter leftInner rightInner rightOuter values)

def Residual (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State) (out : CheckedCell) : Prop :=
  out.status = 0 → ∀ i : Fin 4,
    let left := fluxCheckedBits leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
      leftInner.density leftInner.mx leftInner.my leftInner.energy
    let right := fluxCheckedBits rightInner.density rightInner.mx rightInner.my rightInner.energy
      rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy
    let refL := RealRusanov.interfaceFlux (value left.alpha)
      (decodedState leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy)
      (decodedState leftInner.density leftInner.mx leftInner.my leftInner.energy) i
    let refR := RealRusanov.interfaceFlux (value right.alpha)
      (decodedState rightInner.density rightInner.mx rightInner.my rightInner.energy)
      (decodedState rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy) i
    let state := stateWords center.density center.mx center.my center.energy i
    let fl := fluxWords left i
    let fr := fluxWords right i
    let result := cellWords out i
    Certificate ratio state fl fr result ∧
      |value result - (value state - value ratio * (refR - refL))| ≤
        |value ratio| * radius (Wasm.IEEE64.sub fr fl) +
        radius (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fr fl)) + radius result +
        |value ratio| * (interfaceErrorBounds
          leftOuter.density leftOuter.mx leftOuter.my leftOuter.energy
          leftInner.density leftInner.mx leftInner.my leftInner.energy i +
          interfaceErrorBounds
          rightInner.density rightInner.mx rightInner.my rightInner.energy
          rightOuter.density rightOuter.mx rightOuter.my rightOuter.energy i)

def ResidualSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State),
    TerminatesWith env m 70 initial (arguments ratio center leftOuter leftInner rightInner rightOuter)
      (fun final values => final = initial ∧
        ∃ out : CheckedCell, values = cellValues out ∧
          Residual ratio center leftOuter leftInner rightInner rightOuter out)

theorem faceStepCheckedBits_exact : ExactSpecFor module :=
  Execution.face_step_exact

theorem faceStepCheckedBits_behavior : BehaviorSpecFor module := by
  intro env initial ratio center leftOuter leftInner rightInner rightOuter
  refine TerminatesWith.mono (faceStepCheckedBits_exact env initial ratio
    center leftOuter leftInner rightInner rightOuter) ?_
  rintro final values ⟨hfinal, rfl⟩
  refine ⟨hfinal, ?_⟩
  rcases OutwardNumerics.face_step_behavior ratio center leftOuter leftInner rightInner rightOuter with hr | hs
  · exact Or.inl (congrArg cellValues hr)
  · rcases hs with ⟨hstatus, hstate, hp, hratio, ha, hfinite, hpos, hproduct, hhalf⟩
    refine Or.inr ⟨_, rfl, hstatus, hstate, hp, hratio, ha, hfinite, hpos, hproduct, hhalf, ?_, ?_⟩
    · intro face hf
      refine ⟨?_, fun i => OutwardNumerics.face_step_characteristic_courant ratio
        center leftOuter leftInner rightInner rightOuter hstatus face hf i⟩
      have hb := OutwardNumerics.face_step_bounds ratio center leftOuter leftInner rightInner rightOuter hstatus
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact hb.1
      · exact hb.2.1
      · exact hb.2.2.1
      · exact hb.2.2.2
    · intro n dt globalAlpha hcfl heq face hf i
      subst ratio
      exact OutwardNumerics.face_step_grid_characteristic_courant n dt globalAlpha
        center leftOuter leftInner rightInner rightOuter hcfl hstatus face hf i

theorem faceStepCheckedBits_residual : ResidualSpecFor module := by
  intro env initial ratio center leftOuter leftInner rightInner rightOuter
  refine TerminatesWith.mono (faceStepCheckedBits_exact env initial ratio
    center leftOuter leftInner rightInner rightOuter) ?_
  rintro final values ⟨hfinal, rfl⟩
  exact ⟨hfinal, _, rfl, fun h i =>
    OutwardNumerics.face_step_reference_bound ratio center leftOuter leftInner rightInner rightOuter h i⟩

#print axioms faceStepCheckedBits_exact
#print axioms faceStepCheckedBits_behavior
#print axioms faceStepCheckedBits_residual
end Project.EulerOutwardFaceStep.Spec
