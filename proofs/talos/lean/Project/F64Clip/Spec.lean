import Project.F64Clip.Array
import Project.F64Clip.Validation
import Project.F64Clip.AnnotationMatches

namespace Project.F64Clip.Spec
open Wasm CodeLib.IEEE64

theorem clip_real (env : HostEnv Unit) (initial : Store Unit) (bound x : UInt64)
    (hb : validBound bound = true) (hx : Finite x) :
    TerminatesWith env Project.F64Clip.module 5 initial [.i64 x, .i64 bound]
      (fun final values => final = initial ∧ ∃ output : UInt64, values = [.i64 output] ∧
        Finite output ∧ |value output| ≤ value bound ∧
        value output = max (-value bound) (min (value bound) (value x))) := by
  have hBound := (validBound_iff bound).mp hb
  refine TerminatesWith.mono (clip_exact env initial bound x) ?_
  rintro final values ⟨rfl, rfl⟩
  have hc := clip_bounded bound x hBound.1 hBound.2.1 hx
  exact ⟨rfl, clip bound x, rfl, hc.1, hc.2, clip_value bound x hBound.1 hBound.2.1 hx⟩

#print axioms clip_real
end Project.F64Clip.Spec
