import Project.EulerRiemann.ArtifactTranslation
import Project.EulerRiemann.SpeedCounterexample

namespace Project.EulerRiemann.SpeedCounterexample
open Wasm
open Wasm.Binary
open CodeLib.IEEE64
open Project.Euler2DConservative

def UnderestimateFor (module_ : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit),
    TerminatesWith env module_ 22 initial
      [.i64 0x3FF0000000000000, .i64 0, .i64 0, .i64 0x3FF0000000000000]
      (fun final values => final = initial ∧ ∃ speed : UInt64,
        values[4]? = some (.i64 speed) ∧ values[7]? = some (.i64 0) ∧
        value speed < RealFlux.soundSpeed
          (Guard.decodedState 0x3FF0000000000000 0 0 0x3FF0000000000000))

theorem side_execution : UnderestimateFor Project.EulerRiemann.«module» := by
  intro env initial
  refine TerminatesWith.mono
    (Execution.side_exact env initial 0x3FF0000000000000 0 0 0x3FF0000000000000) ?_
  rintro final values ⟨hf, hv⟩
  refine ⟨hf, side.speed, ?_, ?_, ?_⟩
  · rw [hv]
    rfl
  · rw [hv]
    change some (Wasm.Value.i64 side.status) = some (Wasm.Value.i64 0)
    rw [accepted]
  · rw [← state_eq_decoded]
    exact speed_below_sound

theorem artifact_underestimate :
    ∃ raw validated,
      decode Artifact.artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧ UnderestimateFor validated.toTalos :=
  Artifact.artifact_correct_of UnderestimateFor side_execution

#print axioms side_execution
#print axioms artifact_underestimate
end Project.EulerRiemann.SpeedCounterexample
