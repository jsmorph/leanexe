import Project.EulerGridStep.FieldShape
import Project.ProofKit.FixedArrayAllocatorWindow

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def fieldCapacityFrame (frame : Locals) (length : UInt64) : Locals :=
  { frame with
    locals := (frame.locals.set 8 (.i64 length)).set 14 (.i64 (FixedArrayCapacity.normalizedCapacity length 1)),
    values := [] }

/-- Exact emitted copy-count and normalized-capacity setup, for arbitrary raw length words. -/
theorem field_capacity_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (length : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 20)
    (hValues : frame.values = []) (hLength : frame.locals[7]? = some (.i64 length))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (fieldCapacityFrame frame length) env) :
    wp m (fieldAcceptedBody.take 22 ++ rest) Q initial frame env := by
  have hLengthGet : frame.locals[7] = .i64 length := by
    have h := hLength
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hRaw : FixedArrayCapacity.unnormalizedCapacity length 1 = ((8 + length * 8 + 7) / 8) * 8 := by
    simp [FixedArrayCapacity.unnormalizedCapacity]
  wp_alloc_window_lists [fieldAcceptedBody, func27, List.take, hParams, hLocals, hValues, hLengthGet]
  apply wp_iff_cons rfl
  by_cases hSmall : ((8 + length * 8 + 7) / 8) * 8 < 8
  · rw [ite_eq_left hSmall]
    wp_alloc_window_lists [hParams, hLocals, hValues, List.set_set]
    simpa [fieldCapacityFrame, FixedArrayCapacity.normalizedCapacity, hRaw, hSmall, hValues] using hNext
  · rw [ite_eq_right hSmall]
    wp_alloc_window_lists [hParams, hLocals, hValues]
    simpa [fieldCapacityFrame, FixedArrayCapacity.normalizedCapacity, hRaw, hSmall, hValues] using hNext

#print axioms field_capacity_spec
end Project.EulerGridStep.Execution
