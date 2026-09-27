import Project.GeluWide.Bounds
import Project.GeluWide.Execution
import Project.GeluWide.AnnotationMatches

namespace Project.GeluWide.Spec
open Wasm CodeLib.IEEE64

def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    Finite x →
    TerminatesWith env m 13 initial [.i64 x]
      (fun final values => final = initial ∧
        values = [.i64 (geluWide x).bits, .i64 (geluWide x).status] ∧ NumericalResult x (geluWide x))

theorem geluWide_real_error : RealErrorSpecFor Project.GeluWide.module := by
  intro env initial x hf
  refine TerminatesWith.mono (geluWide_exact env initial x) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, geluWide_numerical x hf⟩

#print axioms geluWide_real_error
end Project.GeluWide.Spec
