import Project.EulerGridStep.FieldFrame

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy

/-- The accepted branch splits exactly into capacity, allocation and the copy/update tail. -/
theorem field_accepted_shape : fieldAcceptedBody = fieldAcceptedBody.take 22 ++
    fieldAllocationRegion ++ fieldAcceptedBody.drop 39 := rfl

def fieldReturnedFrame (choice : FieldAllocation) (unused source : UInt64)
    (count index field : Nat) (value : UInt64) : Locals :=
  { counterFrame (choice.frame (fieldReadyFrame unused source count index field value) count)
      15 count (field_allocated_frame choice unused source count index field value).counter with
    values := [.i64 choice.root] }

/-- Complete accepted branch: exact allocation, terminating copy and one logical update. -/
theorem field_accepted_spec (choice : FieldAllocation) (m : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (unused source : UInt64) (input : Array UInt64)
    (index field : Nat) (value : UInt64)
    (hInput : UInt64Array.At initial source input) (hi : 1 + 6 * index + field < input.size)
    (hValid : choice.Valid initial source input)
    (hPages : initial.mem.pages ≤ 65536) (hMemory32 : m.memIs64 = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      FieldWriteState (choice.store initial input.size) source choice.root input
        (1 + 6 * index + field) value final →
      wp m rest Q final (fieldReturnedFrame choice unused source input.size index field value) env) :
    wp m (fieldAcceptedBody ++ rest) Q initial
      { fieldPrefixFrame unused source input.size index field value with values := [] } env := by
  have hSize : 8 * (input.size + 1) ≤ 4294967296 := by have := hInput.1; omega
  have hReady := field_ready_shape unused source input.size index field value hSize
  have hFrame := field_allocated_frame choice unused source input.size index field value
  have hRegion := field_allocation_region choice initial source input hInput hValid
  rw [field_accepted_shape]
  simp only [List.append_assoc]
  apply field_capacity_spec m env initial
    { fieldPrefixFrame unused source input.size index field value with values := [] }
    (UInt64.ofNat input.size) rfl rfl rfl rfl Q _
  change wp m (fieldAllocationRegion ++ (fieldAcceptedBody.drop 39 ++ rest)) Q initial
    (fieldReadyFrame unused source input.size index field value) env
  apply field_allocation_spec choice m env initial _ source input hValid
    hReady.1 hReady.2.1 hReady.2.2.1 hReady.2.2.2 hPages hMemory32 Q _
  apply field_after_alloc_spec m env (choice.store initial input.size) _ source choice.root
    input (1 + 6 * index + field) value hFrame.counter hFrame.values hFrame.sourceGet
    hFrame.targetGet hFrame.indexGet hFrame.lengthGet hFrame.countGet hFrame.valueGet
    hRegion.inputAt hi hRegion.fit32 hRegion.fitMemory
    (by have := hValid.separate; omega) Q rest
  exact hNext

#print axioms field_accepted_shape
#print axioms field_accepted_spec
end Project.EulerGridStep.Execution
