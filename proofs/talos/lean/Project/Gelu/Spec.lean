import Project.Gelu.Bounds
import Project.Gelu.Execution
import Project.Gelu.AnnotationMatches

namespace Project.Gelu.Spec
open Wasm CodeLib.IEEE64

def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    Finite x → |value x| ≤ 3 →
    TerminatesWith env m 8 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (gelu x).bits, .i64 (gelu x).status] ∧ NumericalResult x (gelu x))

theorem gelu_real_error : RealErrorSpecFor Project.Gelu.module := by
  intro env initial x hf hx
  refine TerminatesWith.mono (gelu_exact env initial x) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, gelu_numerical x hf hx⟩

#print axioms gelu_real_error
end Project.Gelu.Spec
