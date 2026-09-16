import Project.ExpWide.Bounds
import Project.ExpWide.Execution
import Project.ExpWide.AnnotationMatches

namespace Project.ExpWide.Spec
open Wasm CodeLib.IEEE64

def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    Finite x → -8 ≤ value x → value x ≤ 0 →
    TerminatesWith env m 3 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (evaluate x), .i64 0] ∧
        Finite (evaluate x) ∧ 0 < value (evaluate x) ∧
        |value (evaluate x) - Real.exp (value x)| ≤ 1 / 400)

theorem expWide_real_error : RealErrorSpecFor Project.ExpWide.module := by
  intro env initial x hx hl hu
  refine TerminatesWith.mono (expWide_exact env initial x) ?_
  rintro final values ⟨rfl, rfl⟩
  have hs := expWide_success x hl hu
  have hn := evaluate_error x hx hl hu
  exact ⟨rfl, by rw [hs.1, hs.2], hn.1, by linarith [hn.2.1], hn.2.2⟩

#print axioms expWide_real_error
end Project.ExpWide.Spec
