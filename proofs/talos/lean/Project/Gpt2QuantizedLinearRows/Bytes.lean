import Project.Gpt2QuantizedLinearRows.Scales
import Project.Gpt2QuantizedLinearRows.ByteSize
import Project.Gpt2QuantizedLinearRows.ByteLoop

namespace Project.Gpt2QuantizedLinearRows.QuantizeRows
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def byteNeed (width rows : Nat) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (rows * width))

theorem emitted_bytes_prefix : (func3.drop 49).take 50 = byteSizeCode ++ PackedCapacity.program 40 42 ++
    PackedAllocation.program 42 ++ [.localGet 47, .localSet 41, .constI64 0, .localSet 17] ++
    (func3.drop 98).take 1 := rfl

set_option maxRecDepth 32768 in
theorem bytes_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner ptr scalePtr : UInt64) (input : ByteArray) (width rows : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem ptr.toNat input)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input width rows).scales)
    (hInputSize : rows * width * 4 ≤ input.size)
    (hInputProtected : heap.Protects ptr.toNat (ptr.toNat + input.size))
    (hScalesProtected : heap.Protects scalePtr.toNat (scalePtr.toNat + 4 * rows))
    (hCount : rows * width ≤ 2^32)
    (hBump : takeFirstFitFrom 0 (byteNeed width rows) heap.nodes = none →
      heap.top.toNat + 48 + (byteNeed width rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (byteNeed width rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hState : ScaleBuiltState (parameters owner ptr input width rows) scalePtr rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      PackedByteGenerateLoop.Ready 17 40 41 (rows * width) (rows * width)
        (allocatedRoot heap.top (byteNeed width rows) heap.nodes) result →
      ByteState (parameters owner ptr input width rows) scalePtr width rows result →
      heap.PackedOutput initial final (byteNeed width rows) (quantizeRows input width rows).values →
      wp «module» rest Q final result env) :
    wp «module» ((func3.drop 49).take 50 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hScaleOwner, hScalePtr, hScaleSize, hTyped⟩
  have hParamLength : frame.params.length = 5 := by rw [hParams]; rfl
  have hCapacity : (byteNeed width rows).toNat = PackedCapacity.capacityNat (rows * width) :=
    PackedCapacity.capacity_toNat _ hCount
  have hNeed : rows * width ≤ (byteNeed width rows).toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (byteNeed width rows) hHeap hBound
  have hInputAllocated := hAllocFrame.packed hInputProtected hInput
  have hScalesAllocated := hAllocFrame.packed
    (by simpa only [quantized_scales_size] using hScalesProtected) hScales
  have hBounds := PackedAllocation.root_bounds initial heap.top (byteNeed width rows) heap.nodes hHeap.freeList hBound
  have hInputSep := hInputProtected.allocated_disjoint (byteNeed width rows) hBound
  have hScaleSep := hScalesProtected.allocated_disjoint (byteNeed width rows) hBound
  have hSpace := allocated_capacity (byteNeed width rows) heap.nodes
  rw [emitted_bytes_prefix]
  simp only [List.append_assoc]
  apply byteSizeCode_spec env initial frame width rows hParamLength hLocals hValues
    (by rw [hParams]; rfl) (by rw [hParams]; rfl) hCount
  apply PackedCapacity.program_spec 40 42 (UInt64.ofNat (rows * width)) «module» env initial
    (byteSizeFrame frame width rows)
  · simp [byteSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [byteSizeFrame, hParamLength]
  · simp [byteSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (byteSizeFrame frame width rows) 42 (byteNeed width rows)
  have hPreparedParams : prepared.params = frame.params := by
    simp [prepared, FixedArrayCapacity.capacityFrame, byteSizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 43 := by
    simp [prepared, FixedArrayCapacity.capacityFrame, byteSizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      byteSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 42 heap.top
    (byteNeed width rows) heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · simp [hPreparedParams, hParamLength, hPreparedLocals]
  · simp [prepared, FixedArrayCapacity.capacityFrame, byteSizeFrame, Locals.get, hParamLength, hLocals]
  · rw [hHeap.globals]; rfl
  · rw [hHeap.globals]; rfl
  · rw [hHeap.globals]; rfl
  · exact hHeap.freeList
  · exact fun h => ⟨(hBump h).1.le, (hBump h).2⟩
  · exact hPages
  · rfl
  intro previous current capacity next
  simp only [List.cons_append, List.nil_append]
  wp_packed_frame [PackedAllocation.allocatedFrame, FixedArraySearch.frame, hPreparedParams,
    hPreparedLocals, hParamLength, List.length_append, List.length_take, List.length_drop,
    List.getElem?_append, List.getElem?_take, show min 37 43 = 37 from rfl]
  apply byteLoop_spec env (heap.allocatePackedStore initial (byteNeed width rows)) owner ptr scalePtr
    (allocatedRoot heap.top (byteNeed width rows) heap.nodes) input width rows _
    hInputAllocated hScalesAllocated hInputSize
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · omega
  · simp [PackedByteGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame, byteSizeFrame,
      Locals.get, Locals.validIndex, hParams, parameters, hLocals]
    rfl
  · simp (config := { maxDischargeDepth := 64 }) [ByteState, prepared,
      FixedArrayCapacity.capacityFrame, byteSizeFrame, hParams, parameters, hLocals,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
    exact ⟨(List.getElem_of_getElem? hScaleOwner).choose_spec,
      (List.getElem_of_getElem? hScalePtr).choose_spec,
      by simpa using (List.getElem_of_getElem? hScaleSize).choose_spec⟩
  intro final result hReady hState hBytes hWrites
  exact hNext final result hReady hState
    (heap.packedOutput initial final (byteNeed width rows) (quantizeRows input width rows).values hHeap
      (by rw [quantized_values_size]; exact hNeed) (fun h => (hBump h).1) hPages
      (by rw [quantized_values_size]; exact hWrites) hBytes)

#print axioms bytes_spec

end Project.Gpt2QuantizedLinearRows.QuantizeRows
