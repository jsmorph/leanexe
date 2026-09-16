import Project.ExpSmall.Bounds
import Project.ExpSmall.Execution
import Project.ExpSmall.AnnotationMatches

namespace Project.ExpSmall.Spec
open Wasm CodeLib.IEEE64

def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    Finite x → -1 ≤ value x → value x ≤ 0 →
    TerminatesWith env m 2 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (polynomial x), .i64 0] ∧
        Finite (polynomial x) ∧ 0 < value (polynomial x) ∧
        |value (polynomial x) - Real.exp (value x)| ≤ 1 / 4000)

theorem expSmall_real_error : RealErrorSpecFor Project.ExpSmall.module := by
  intro env initial x hx hl hu
  refine TerminatesWith.mono (expSmall_exact env initial x) ?_
  rintro final values ⟨rfl, rfl⟩
  have hs := expSmall_success x hl hu
  have hn := polynomial_positive x hx hl hu
  exact ⟨rfl, by rw [hs.1, hs.2], hn.1, hn.2.1, hn.2.2.2⟩

#print axioms expSmall_real_error
end Project.ExpSmall.Spec
