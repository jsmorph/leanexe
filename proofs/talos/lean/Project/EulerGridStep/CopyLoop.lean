import Project.EulerGridStep.CopyFrame

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayCopy
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def copyInvariant (initial : Store Unit) (frame : Locals) (counterLocal : Nat)
    (hCounter : frame.validIndex counterLocal) (source target : UInt64)
    (input : Array UInt64) : AssertionF Unit :=
  fun current currentFrame => ∃ (index : Nat) (output : Array UInt64),
    index ≤ input.size ∧ CopyState initial source target input output current index ∧
    currentFrame = counterFrame frame counterLocal index hCounter

/-- Exact copying with input preservation, all non-memory store fields, and an outside-byte frame. -/
theorem copy_loop_spec (sourceLocal targetLocal countLocal counterLocal : Nat)
    (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target : UInt64) (input output : Array UInt64)
    (hCounter : frame.validIndex counterLocal)
    (hCounterSource : sourceLocal ≠ counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal)
    (hCounterCount : countLocal ≠ counterLocal)
    (hValues : frame.values = [])
    (hSourceLocal : frame.get sourceLocal = some (.i64 source))
    (hTargetLocal : frame.get targetLocal = some (.i64 target))
    (hCountLocal : frame.get countLocal = some (.i64 (UInt64.ofNat input.size)))
    (hInput : UInt64Array.At initial source input)
    (hOutput : UInt64Array.At initial target output) (hSize : output.size = input.size)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ (final : Store Unit) (result : Array UInt64),
      CopyState initial source target input result final input.size →
      wp m rest Q final (counterFrame frame counterLocal input.size hCounter) env) :
    wp m (prefixProgram sourceLocal targetLocal countLocal counterLocal ++ rest) Q initial frame env := by
  have hCount64 := hInput.size_lt
  have hCountNat := UInt64.toNat_ofNat_of_lt' hCount64
  simp only [prefixProgram, List.cons_append, List.nil_append]
  apply copy_initialize_counter hCounter hValues
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := copyInvariant initial frame counterLocal hCounter source target input)
    (μ := copyMeasure counterLocal input.size)
  · exact ⟨0, output, Nat.zero_le _, copyState_initial _ _ _ _ _ hInput hOutput hSize, rfl⟩
  · rintro current currentFrame ⟨index, values, hIndexLe, hCopy, rfl⟩
    have hIndex64 : index < UInt64.size := by omega
    have hIndexNat := UInt64.toNat_ofNat_of_lt' hIndex64
    have hCounterGet := counterFrame_get_counter frame counterLocal index hCounter
    have hSourceGet := (counterFrame_get_ne frame counterLocal index sourceLocal hCounter
      hCounterSource).trans hSourceLocal
    have hTargetGet := (counterFrame_get_ne frame counterLocal index targetLocal hCounter
      hCounterTarget).trans hTargetLocal
    have hCountGet := (counterFrame_get_ne frame counterLocal index countLocal hCounter
      hCounterCount).trans hCountLocal
    simp only [prefixBody, wp_localGet_cons, copyFrame_get_withValues, hCounterGet, hCountGet,
      counterFrame_values, wp_geUI64_cons, wp_br_if_cons]
    by_cases hEnd : index = input.size
    · have hGuard : UInt64.ofNat index ≥ UInt64.ofNat input.size := by simp [hEnd]
      rw [ite_eq_left hGuard]
      subst index
      simp
      convert hNext current values hCopy using 1
      exact copyFrame_ofParts _ (counterFrame_values frame counterLocal input.size hCounter)
    · have hi : index < input.size := by omega
      have ho : index < values.size := by have := hCopy.size; omega
      have hGuard : ¬ UInt64.ofNat index ≥ UInt64.ofNat input.size := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hIndexNat, hCountNat]
        omega
      rw [ite_eq_right hGuard]
      have hLoadBound := hCopy.inputAt.elementBound index hi
      have hStoreBound := hCopy.outputAt.elementBound index ho
      change (UInt64Array.wordAddress source (index + 1)).toNat + 8 ≤ current.mem.pages * 65536 at hLoadBound
      change (UInt64Array.wordAddress target (index + 1)).toNat + 8 ≤ current.mem.pages * 65536 at hStoreBound
      have hRead : current.mem.read64 (UInt64Array.wordAddress source (index + 1)) = input[index]! := by
        simpa [UInt64Array.wordAddress, hi] using hCopy.inputAt.elementRead index hi
      have hSucc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) :=
        (UInt64.ofNat_add index 1).symm
      simp only [wp_localGet_cons, copyFrame_get_withValues, hTargetGet, hCounterGet, hSourceGet,
        wp_constI64_cons, wp_addI64_cons, wp_mulI64_cons, wp_wrapI64_cons, wp_load64_cons, wp_store64_cons]
      rw [copyRuntimeAddress source index, copyRuntimeAddress target index]
      simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
      rw [ite_eq_right (Nat.not_lt.mpr hLoadBound), ite_eq_right (Nat.not_lt.mpr hStoreBound), hRead, hSucc]
      simp only [wp_localSet_cons, copyFrame_set_counter, wp_br_cons,
        List.take_zero, List.drop_zero, List.nil_append]
      refine ⟨?_, ?_⟩
      · exact ⟨index + 1, values.set! index input[index]!, by omega,
          copyState_step initial current source target input values index hCopy hi hSeparate, rfl⟩
      · rw [copyFrame_ofParts _ (counterFrame_values frame counterLocal (index + 1) hCounter),
          copyMeasure_frame, copyMeasure_frame,
          UInt64.toNat_ofNat_of_lt' (by omega : index + 1 < UInt64.size), hIndexNat]
        omega

#print axioms copy_loop_spec
end Project.EulerGridStep.Execution
