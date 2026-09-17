import Project.ExpNeg.Bounds
import Project.ExpNeg.Execution
import Project.ExpNeg.AnnotationMatches

namespace Project.ExpNeg.Spec
open Wasm CodeLib.IEEE64

def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    Finite x → value x ≤ 0 →
    TerminatesWith env m 7 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (evaluate x), .i64 0] ∧
        Finite (evaluate x) ∧ 0 ≤ value (evaluate x) ∧
        |value (evaluate x)-Real.exp (value x)| ≤
          4029*arithmeticEpsilon*Real.exp (value x)+1/10^27)

theorem expNeg_real_error : RealErrorSpecFor Project.ExpNeg.module := by
  intro env initial x hf hu
  refine TerminatesWith.mono (expNeg_exact env initial x) ?_
  rintro final values ⟨rfl, rfl⟩
  have hd := (inDomain_iff x).mpr ⟨hf, hu⟩
  have he := evaluate_error x hf hu
  exact ⟨rfl, by simp [expNeg, hd], he.1, he.2.1,
    he.2.2.trans (add_le_add le_rfl tail_bound)⟩

#print axioms expNeg_real_error
end Project.ExpNeg.Spec
