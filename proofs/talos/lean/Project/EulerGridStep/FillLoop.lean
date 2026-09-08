import Project.EulerGridStep.FillState
import Project.EulerGridStep.CopyFrame

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def fillBody (targetLocal countLocal counterLocal valueLocal : Nat) : Wasm.Program :=
  [.localGet counterLocal, .localGet countLocal, .geUI64, .br_if 1,
    .localGet targetLocal, .localGet counterLocal, .constI64 1, .mulI64, .constI64 1, .addI64,
    .constI64 8, .mulI64, .addI64, .wrapI64, .localGet valueLocal, .store64 0,
    .localGet counterLocal, .constI64 1, .addI64, .localSet counterLocal, .br 0]

def fillProgram (targetLocal countLocal counterLocal valueLocal : Nat) : Wasm.Program :=
  [.constI64 0, .localSet counterLocal,
    .block 0 0 [.loop 0 0 (fillBody targetLocal countLocal counterLocal valueLocal)]]

def fillInvariant (initial : Store Unit) (frame : Locals) (counterLocal : Nat)
    (hCounter : frame.validIndex counterLocal) (target value : UInt64)
    (original : Array UInt64) : AssertionF Unit :=
  fun current currentFrame => ∃ (index : Nat) (output : Array UInt64),
    index ≤ original.size ∧ FillState initial target value original current output index ∧
    currentFrame = counterFrame frame counterLocal index hCounter

/-- Complete constant initialization with an exact array, store frame and outside-byte frame. -/
theorem fill_loop_spec (targetLocal countLocal counterLocal valueLocal : Nat)
    (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (target value : UInt64) (original : Array UInt64)
    (hCounter : frame.validIndex counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal) (hCounterCount : countLocal ≠ counterLocal)
    (hCounterValue : valueLocal ≠ counterLocal) (hValues : frame.values = [])
    (hTargetLocal : frame.get targetLocal = some (.i64 target))
    (hCountLocal : frame.get countLocal = some (.i64 (UInt64.ofNat original.size)))
    (hValueLocal : frame.get valueLocal = some (.i64 value))
    (hArray : UInt64Array.At initial target original)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (result : Array UInt64),
      FillState initial target value original final result original.size →
      wp m rest Q final (counterFrame frame counterLocal original.size hCounter) env) :
    wp m (fillProgram targetLocal countLocal counterLocal valueLocal ++ rest) Q initial frame env := by
  have hCount64 := hArray.size_lt
  have hCountNat := UInt64.toNat_ofNat_of_lt' hCount64
  simp only [fillProgram, List.cons_append, List.nil_append]
  apply copy_initialize_counter hCounter hValues
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fillInvariant initial frame counterLocal hCounter target value original)
    (μ := copyMeasure counterLocal original.size)
  · exact ⟨0, original, Nat.zero_le _, fillState_initial _ _ _ _ hArray, rfl⟩
  · rintro current currentFrame ⟨index, values, hIndexLe, hFill, rfl⟩
    have hIndex64 : index < UInt64.size := by omega
    have hIndexNat := UInt64.toNat_ofNat_of_lt' hIndex64
    have hCounterGet := counterFrame_get_counter frame counterLocal index hCounter
    have hTargetGet := (counterFrame_get_ne frame counterLocal index targetLocal hCounter
      hCounterTarget).trans hTargetLocal
    have hCountGet := (counterFrame_get_ne frame counterLocal index countLocal hCounter
      hCounterCount).trans hCountLocal
    have hValueGet := (counterFrame_get_ne frame counterLocal index valueLocal hCounter
      hCounterValue).trans hValueLocal
    simp only [fillBody, wp_localGet_cons, copyFrame_get_withValues, hCounterGet, hCountGet,
      counterFrame_values, wp_geUI64_cons, wp_br_if_cons]
    by_cases hEnd : index = original.size
    · have hGuard : UInt64.ofNat index ≥ UInt64.ofNat original.size := by simp [hEnd]
      rw [ite_eq_left hGuard]
      subst index
      simp
      convert hNext current values hFill using 1
      exact copyFrame_ofParts _ (counterFrame_values frame counterLocal original.size hCounter)
    · have hi : index < original.size := by omega
      have ho : index < values.size := by have := hFill.size; omega
      have hGuard : ¬ UInt64.ofNat index ≥ UInt64.ofNat original.size := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hIndexNat, hCountNat]
        omega
      rw [ite_eq_right hGuard]
      have hStoreBound := hFill.arrayAt.elementBound index ho
      change (UInt64Array.wordAddress target (index + 1)).toNat + 8 ≤ current.mem.pages * 65536 at hStoreBound
      have hSucc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := (UInt64.ofNat_add index 1).symm
      simp only [wp_localGet_cons, copyFrame_get_withValues, hTargetGet, hCounterGet, hValueGet,
        wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons, UInt64.mul_one, wp_wrapI64_cons, wp_store64_cons]
      rw [copyRuntimeAddress target index]
      simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
      rw [ite_eq_right (Nat.not_lt.mpr hStoreBound), hSucc]
      simp only [wp_localSet_cons, copyFrame_set_counter, wp_br_cons,
        List.take_zero, List.drop_zero, List.nil_append]
      refine ⟨?_, ?_⟩
      · exact ⟨index + 1, values.set! index value, by omega,
          fillState_step initial current target value original values index hFill hi, rfl⟩
      · rw [copyFrame_ofParts _ (counterFrame_values frame counterLocal (index + 1) hCounter),
          copyMeasure_frame, copyMeasure_frame,
          UInt64.toNat_ofNat_of_lt' (by omega : index + 1 < UInt64.size), hIndexNat]
        omega

#print axioms fill_loop_spec
end Project.EulerGridStep.Execution
