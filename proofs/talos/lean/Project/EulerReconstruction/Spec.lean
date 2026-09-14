import Project.EulerReconstruction.Reconstruct
import Project.EulerRiemann.ReconstructionAccuracy
import Project.EulerRiemann.ReconstructionFactor

namespace Project.EulerReconstruction.Spec
open Wasm CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (State StateSafe)
open Project.EulerRiemann.Reconstruction
open Project.ProofKit.F64RoundingResidual (radius)

def arguments (fuel : UInt64) (left center right : State) : List Value :=
  Execution.stateValues right ++ Execution.stateValues center ++
    Execution.stateValues left ++ [.i64 fuel]

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (fuel : UInt64) (left center right : State),
    TerminatesWith env m 40 initial (arguments fuel left center right)
      (fun final values => final = initial ∧
        values = Execution.facesValues (reconstruct fuel.toNat left center right))

def SafeBehavior (values : List Value) : Prop :=
  values = Execution.facesValues rejectedFaces ∨
    ∃ output : Faces, values = Execution.facesValues output ∧ output.status = 0 ∧
      StateSafe output.left ∧ StateSafe output.right

def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (fuel : UInt64) (left center right : State),
    TerminatesWith env m 40 initial (arguments fuel left center right)
      (fun final values => final = initial ∧ SafeBehavior values)

def Accuracy (fuel : Nat) (left center right : State) (output : Faces) : Prop :=
  output = constantFaces center ∨
    ∃ steps < fuel, output.factor = factorAfter steps 0x3FE0000000000000 ∧
      ∀ i : Fin 4,
        let delta := words (slope left center right).state i
        let offsetRadius := radius (IEEE64.mul output.factor delta)
        (|decoded output.left i - (decoded center i - value output.factor * exactSlope left center right i)| ≤
          offsetRadius + radius (words output.left i) + |value output.factor| * slopeRadius left center right i ∧
        |decoded output.right i - (decoded center i + value output.factor * exactSlope left center right i)| ≤
          offsetRadius + radius (words output.right i) + |value output.factor| * slopeRadius left center right i) ∧
        |(decoded output.left i + decoded output.right i)/2 - decoded center i| ≤
          (radius (words output.left i) + radius (words output.right i))/2

def AccuracyBehavior (fuel : Nat) (left center right : State) (values : List Value) : Prop :=
  values = Execution.facesValues rejectedFaces ∨
    ∃ output : Faces, values = Execution.facesValues output ∧ output.status = 0 ∧
      StateSafe output.left ∧ StateSafe output.right ∧ Accuracy fuel left center right output

def AccuracySpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (fuel : UInt64) (left center right : State),
    TerminatesWith env m 40 initial (arguments fuel left center right)
      (fun final values => final = initial ∧ AccuracyBehavior fuel.toNat left center right values)

def FactorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (fuel : UInt64) (left center right : State),
    TerminatesWith env m 40 initial (arguments fuel left center right)
      (fun final values => final = initial ∧
        ∃ output : Faces, values = Execution.facesValues output ∧
          Finite output.factor ∧ 0 ≤ value output.factor ∧ value output.factor ≤ 1/2)

theorem reconstruct_exact : ExactSpecFor module := Execution.reconstruct_exact

theorem reconstruct_safe : SafeSpecFor module := by
  intro env initial fuel left center right
  refine TerminatesWith.mono (reconstruct_exact env initial fuel left center right) ?_
  rintro final values ⟨hFinal, rfl⟩
  refine ⟨hFinal, ?_⟩
  rcases reconstruct_behavior fuel.toNat left center right with hr | hs
  · exact Or.inl (congrArg Execution.facesValues hr)
  · exact Or.inr ⟨reconstruct fuel.toNat left center right, rfl, hs⟩

theorem reconstruct_accuracy : AccuracySpecFor module := by
  intro env initial fuel left center right
  refine TerminatesWith.mono (reconstruct_exact env initial fuel left center right) ?_
  rintro final values ⟨hFinal, rfl⟩
  refine ⟨hFinal, ?_⟩
  rcases reconstruct_behavior fuel.toNat left center right with hr | hs
  · exact Or.inl (congrArg Execution.facesValues hr)
  · exact Or.inr ⟨reconstruct fuel.toNat left center right, rfl, hs.1, hs.2.1, hs.2.2,
      Project.EulerRiemann.Reconstruction.reconstruct_accuracy fuel.toNat left center right hs.1⟩

theorem reconstruct_factor : FactorSpecFor module := by
  intro env initial fuel left center right
  refine TerminatesWith.mono (reconstruct_exact env initial fuel left center right) ?_
  rintro final values ⟨hFinal, rfl⟩
  exact ⟨hFinal, reconstruct fuel.toNat left center right, rfl,
    Project.EulerRiemann.Reconstruction.reconstruct_factor fuel.toNat left center right⟩

#print axioms reconstruct_exact
#print axioms reconstruct_safe
#print axioms reconstruct_accuracy
#print axioms reconstruct_factor

end Project.EulerReconstruction.Spec
