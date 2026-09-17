import Project.LayerNorm.Bounds
import Project.LayerNorm.Wide
import Project.LayerNorm.Execution
import Project.LayerNorm.AnnotationMatches

namespace Project.LayerNorm.Spec
open Wasm

def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 : UInt64),
    Valid x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 →
    TerminatesWith env m 6 initial (arguments x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3)
      (fun final values => final = initial ∧
        values = resultWords (layerNorm x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3) ∧
        NumericalResult x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3
          (layerNorm x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3))

theorem layerNorm_real_error : RealErrorSpecFor Project.LayerNorm.module := by
  intro env initial x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 h
  refine TerminatesWith.mono (layerNorm_exact env initial x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl, layerNorm_numerical x0 x1 x2 x3 g0 g1 g2 g3 b0 b1 b2 b3 h⟩

#print axioms layerNorm_real_error
end Project.LayerNorm.Spec
