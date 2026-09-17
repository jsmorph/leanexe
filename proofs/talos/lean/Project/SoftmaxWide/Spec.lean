import Project.SoftmaxWide.Numerical
import Project.SoftmaxWide.Execution
import Project.SoftmaxWide.AnnotationMatches

namespace Project.SoftmaxWide.Spec
open Wasm CodeLib.IEEE64 Project.Softmax Project.ProofKit

def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (n a b c d : UInt64),
    Valid n a b c d →
    TerminatesWith env m 12 initial [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = Softmax.Spec.resultWords (compute n a b c d) ∧
        (∀ i, Finite (outputs (compute n a b c d) i)) ∧
        (∑ i, |value (outputs (compute n a b c d) i)-reference n (scores a b c d) i|) ≤
          10053*arithmeticEpsilon ∧
        |(∑ i, value (outputs (compute n a b c d) i))-1| ≤ 52*arithmeticEpsilon)

theorem compute_real_error : RealErrorSpecFor Project.SoftmaxWide.module := by
  intro env initial n a b c d h
  refine TerminatesWith.mono (compute_exact env initial n a b c d) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, compute_numerical n a b c d h⟩

#print axioms compute_real_error
end Project.SoftmaxWide.Spec
