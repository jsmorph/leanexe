import Project.ExpArm.Execution
import Project.ExpArm.InitialTable
import Project.ExpArm.TinyBounds
import Project.ExpArm.NormalAccuracy
import Project.ExpArm.AnnotationMatches
import Project.ExpArm.ArtifactTranslation

namespace Project.ExpArm.Spec
open Wasm CodeLib.IEEE64 Project.ProofKit

def InitialSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (x : UInt64),
    TerminatesWith env m 2 m.initialStore [.i64 x]
      (fun final values => final = m.initialStore ∧ values = [.i64 (exp x)])

theorem exp_initial : InitialSpecFor Project.ExpArm.module := by
  intro env x
  exact exp_exact env _ x initial_table

theorem exp_binary :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧ InitialSpecFor validated.toTalos :=
  Artifact.artifact_correct_of InitialSpecFor exp_initial

theorem exp_tiny_error (env : HostEnv Unit) (initial : Store Unit) (x : UInt64)
    (ht : UInt64Array.At initial 4096 table)
    (hx : x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000) :
    TerminatesWith env Project.ExpArm.module 2 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 0x3FF0000000000000] ∧
        |value 0x3FF0000000000000 - Real.exp (value x)| < 1/(2 : ℝ)^53) := by
  refine TerminatesWith.mono (exp_exact env initial x ht) ?_
  rintro final values ⟨rfl, rfl⟩
  have h := tiny_error x hx
  rw [exp_tiny x hx] at h ⊢
  exact ⟨rfl, rfl, h.2.2⟩

theorem exp_nan_result (env : HostEnv Unit) (initial : Store Unit) (x : UInt64)
    (ht : UInt64Array.At initial 4096 table)
    (hx : 0x7FF0000000000000 < x &&& 0x7FFFFFFFFFFFFFFF) :
    TerminatesWith env Project.ExpArm.module 2 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 0x7FF8000000000000]) := by
  simpa only [exp_nan x hx] using exp_exact env initial x ht

theorem exp_normal_accuracy (env : HostEnv Unit) (initial : Store Unit) (x : UInt64)
    (ht : UInt64Array.At initial 4096 table)
    (hx : x &&& 0x7FFFFFFFFFFFFFFF < 0x4080000000000000) :
    TerminatesWith env Project.ExpArm.module 2 initial [.i64 x]
      (fun final values => final = initial ∧ ∃ result,
        values = [.i64 result] ∧ F64Accuracy.ErrorBelowOneUlp result (Real.exp (value x))) := by
  refine TerminatesWith.mono (exp_exact env initial x ht) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, exp x, rfl, Project.ExpArm.exp_normal_accuracy x hx⟩

def NormalAccuracySpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (x : UInt64),
    x &&& 0x7FFFFFFFFFFFFFFF < 0x4080000000000000 →
    TerminatesWith env m 2 m.initialStore [.i64 x]
      (fun final values => final = m.initialStore ∧ ∃ result,
        values = [.i64 result] ∧ F64Accuracy.ErrorBelowOneUlp result (Real.exp (value x)))

theorem exp_binary_normal_accuracy :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧ NormalAccuracySpecFor validated.toTalos := by
  apply Artifact.artifact_correct_of NormalAccuracySpecFor
  intro env x hx
  exact exp_normal_accuracy env _ x initial_table hx

#print axioms exp_exact
#print axioms exp_initial
#print axioms exp_binary
#print axioms exp_tiny_error
#print axioms exp_nan_result
#print axioms exp_normal_accuracy
#print axioms exp_binary_normal_accuracy
end Project.ExpArm.Spec
