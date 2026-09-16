import Project.Softmax.Numerical
import Project.Softmax.Execution
import Project.Softmax.AnnotationMatches

namespace Project.Softmax.Spec
open Wasm

def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64),
    Valid n a b c d →
    TerminatesWith env m 11 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧
        values = resultWords (softmax n a b c d) ∧
        NumericalResult n a b c d (softmax n a b c d))

theorem softmax_real_error : RealErrorSpecFor Project.Softmax.module := by
  intro env initial n a b c d h
  refine TerminatesWith.mono (softmax_exact env initial n a b c d) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, softmax_numerical n a b c d h⟩

#print axioms softmax_real_error
end Project.Softmax.Spec
