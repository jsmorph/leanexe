import Project.EulerGridStep.InitializationShape
import Project.EulerGridStep.FieldIndexing

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def initialCapacityFrame (frame : Locals) (length : UInt64) : Locals :=
  { frame with
    locals := frame.locals.set 37 (.i64 (FixedArrayCapacity.normalizedCapacity length 1)),
    values := [] }

/-- Exact capacity arithmetic in the valid grid entry. -/
theorem initial_capacity_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (length : UInt64)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 43)
    (hValues : frame.values = []) (hLength : frame.locals[31]? = some (.i64 length))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (initialCapacityFrame frame length) env) :
    wp m ((gridValidBody.drop 36).take 18 ++ rest) Q initial frame env := by
  have hLengthGet : frame.locals[31] = .i64 length := by
    have h := hLength
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hRaw : FixedArrayCapacity.unnormalizedCapacity length 1 = ((8 + length * 8 + 7) / 8) * 8 := by
    simp [FixedArrayCapacity.unnormalizedCapacity]
  wp_alloc_window_lists [gridValidBody, func36, List.drop, List.take, hParams, hLocals, hValues, hLengthGet]
  apply wp_iff_cons rfl
  by_cases hSmall : ((8 + length * 8 + 7) / 8) * 8 < 8
  · rw [ite_eq_left hSmall]
    wp_alloc_window_lists [hParams, hLocals, hValues, List.set_set]
    simpa [initialCapacityFrame, FixedArrayCapacity.normalizedCapacity, hRaw, hSmall, hValues] using hNext
  · rw [ite_eq_right hSmall]
    wp_alloc_window_lists [hParams, hLocals, hValues]
    simpa [initialCapacityFrame, FixedArrayCapacity.normalizedCapacity, hRaw, hSmall, hValues] using hNext

#print axioms initial_capacity_spec
end Project.EulerGridStep.Execution
