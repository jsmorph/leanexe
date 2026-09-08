import Project.EulerGridStep.FieldShape
import Project.EulerGridStep.FieldTailModel

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def fieldStoreReturn : Wasm.Program :=
  [.localGet 14, .localGet 11, .constI64 1, .mulI64, .constI64 1, .addI64,
   .constI64 8, .mulI64, .addI64, .wrapI64, .localGet 16, .store64 0, .localGet 14]

theorem field_after_alloc_shape : fieldAcceptedBody.drop 39 =
    [.localGet 14, .wrapI64, .localGet 12, .store64 0] ++
      prefixProgram 10 14 13 15 ++ fieldStoreReturn := rfl

/-- The complete generated tail after allocation: initialize, copy, update and return. -/
theorem field_after_alloc_spec (m : Wasm.Module) (env : HostEnv Unit)
    (initial : Store Unit) (frame : Locals) (source target : UInt64)
    (input : Array UInt64) (index : Nat) (value : UInt64)
    (hCounter : frame.validIndex 15) (hValues : frame.values = [])
    (hSource : frame.get 10 = some (.i64 source))
    (hTarget : frame.get 14 = some (.i64 target))
    (hIndex : frame.get 11 = some (.i64 (UInt64.ofNat index)))
    (hLength : frame.get 12 = some (.i64 (UInt64.ofNat input.size)))
    (hCount : frame.get 13 = some (.i64 (UInt64.ofNat input.size)))
    (hValue : frame.get 16 = some (.i64 value))
    (hInput : UInt64Array.At initial source input) (hi : index < input.size)
    (hFit32 : target.toNat + 8 * (input.size + 1) ≤ 4294967296)
    (hFitMemory : target.toNat + 8 * (input.size + 1) ≤ initial.mem.pages * 65536)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, FieldWriteState initial source target input index value final →
      wp m rest Q final
        { counterFrame frame 15 input.size hCounter with values := [.i64 target] } env) :
    wp m (fieldAcceptedBody.drop 39 ++ rest) Q initial frame env := by
  have hTargetNat : target.toUInt32.toNat = target.toNat := by
    simpa [UInt64Array.wordAddress] using
      UInt64Array.wordAddress_toNat hFit32 (by omega : 0 < input.size + 1)
  have hHeaderBound : target.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [hTargetNat]
    omega
  rw [field_after_alloc_shape]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  simp only [wp_localGet_cons, copyFrame_get_withValues, hTarget, hLength, hValues,
    wp_wrapI64_cons, wp_store64_cons]
  have hWrap : UInt32.ofNat (target.toNat % (2 ^ 32)) = target.toUInt32 :=
    (Memory.toUInt32_eq_ofNat target).symm
  rw [hWrap]
  simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hHeaderBound)]
  change wp m (prefixProgram 10 14 13 15 ++ (fieldStoreReturn ++ rest)) Q
    (writeLength initial target input.size) { params := frame.params, locals := frame.locals } env
  rw [copyFrame_ofParts frame hValues]
  apply copy_loop_spec 10 14 13 15 m env (writeLength initial target input.size) frame
    source target input (payloadSnapshot initial target input.size) hCounter
    (by decide) (by decide) (by decide) hValues hSource hTarget hCount
    (writeLength_preserves_array initial source target input input.size hInput hFit32 hSeparate)
    (writeLength_array initial target input.size hFit32 hFitMemory)
    (by simp [payloadSnapshot]) hSeparate Q (fieldStoreReturn ++ rest)
  intro current output hCopy
  have hArray := copyState_complete _ _ _ _ _ _ hCopy
  have hTargetGet := (counterFrame_get_ne frame 15 input.size 14 hCounter (by decide)).trans hTarget
  have hIndexGet := (counterFrame_get_ne frame 15 input.size 11 hCounter (by decide)).trans hIndex
  have hValueGet := (counterFrame_get_ne frame 15 input.size 16 hCounter (by decide)).trans hValue
  have hBound := hArray.elementBound index hi
  change (UInt64Array.wordAddress target (index + 1)).toNat + 8 ≤ current.mem.pages * 65536 at hBound
  simp only [fieldStoreReturn, List.cons_append, List.nil_append, wp_localGet_cons,
    copyFrame_get_withValues, hTargetGet, hIndexGet, hValueGet, wp_constI64_cons,
    wp_mulI64_cons, UInt64.mul_one, wp_addI64_cons, wp_wrapI64_cons, wp_store64_cons]
  rw [copyRuntimeAddress target index]
  simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (Nat.not_lt.mpr hBound)]
  simpa only [wp_localGet_cons, copyFrame_get_withValues, hTargetGet, counterFrame_values, writeWord] using
    hNext (writeWord current target index value)
      (fieldWrite_after_copy initial current source target input output index value hi hCopy hSeparate)

#print axioms field_after_alloc_shape
#print axioms field_after_alloc_spec
end Project.EulerGridStep.Execution
