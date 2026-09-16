import Project.Softmax.Perturbation
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

theorem softmax_input_error (env : HostEnv Unit) (initial : Store Unit)
    (n a b c d : UInt64) (h : Valid n a b c d)
    (target : Fin 4 → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (he : ∀ j, |CodeLib.IEEE64.value (scores a b c d j)-target j| ≤ delta) :
    TerminatesWith env Project.Softmax.module 11 initial
      [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = resultWords (softmax n a b c d) ∧
        ∀ i, |CodeLib.IEEE64.value (outputs (softmax n a b c d) i)-
          Real.probability (visible n) target i| ≤ 1/50000+2*delta) := by
  refine TerminatesWith.mono (softmax_exact env initial n a b c d) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, softmax_perturbed n a b c d h target delta hd he⟩

#print axioms softmax_real_error
#print axioms softmax_input_error

theorem compute_spread_error (env : HostEnv Unit) (initial : Store Unit)
    (n a b c d : UInt64) (h : SpreadValid n a b c d) :
    TerminatesWith env Project.Softmax.module 10 initial
      [.i64 d, .i64 c, .i64 b, .i64 a, .i64 n]
      (fun final values => final = initial ∧ values = resultWords (compute n a b c d) ∧
        NumericalResult n a b c d (compute n a b c d)) := by
  refine TerminatesWith.mono (compute_exact env initial n a b c d) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, compute_numerical_spread n a b c d h⟩

#print axioms compute_spread_error
end Project.Softmax.Spec
