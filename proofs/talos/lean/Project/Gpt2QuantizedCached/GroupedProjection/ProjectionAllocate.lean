import Project.Gpt2QuantizedCached.GroupedProjection.ProjectionSize
import Project.Gpt2QuantizedCached.GroupedProjection.ProjectionLoop

namespace Project.Gpt2QuantizedCached.GroupedProjection.Projection
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def need (outputWidth rows : Nat) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth)))

theorem emitted_allocation : (func8.drop 68).take 32 = PackedCapacity.program 95 97 ++
    PackedAllocation.program 97 ++ [.localGet 102, .localSet 96, .constI64 0, .localSet 32] ++
    (func8.drop 99).take 1 := rfl

set_option maxRecDepth 32768 in
theorem allocatedOutput_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows : Nat) (withBias : Bool) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input 64 (rows * (width / 64))).values)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input 64 (rows * (width / 64))).scales)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hBiasSize : withBias = true → biasOffset + outputWidth * 4 ≤ weights.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width)
    (hWeightProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hValueProtected : heap.Protects valuePtr.toNat (valuePtr.toNat + rows * width))
    (hScaleProtected : heap.Protects scalePtr.toNat (scalePtr.toNat + 4 * (rows * (width / 64))))
    (hCount : 4 * (rows * outputWidth) ≤ 2^32)
    (hBump : takeFirstFitFrom 0 (need outputWidth rows) heap.nodes = none →
      heap.top.toNat + 48 + (need outputWidth rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need outputWidth rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hState : OutputState (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset scaleOffset biasOffset
      width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows frame)
    (hEmpty : frame.values = []) (hLengthLocal : frame.get 95 = some (.i64 (UInt64.ofNat (4 * (rows * outputWidth)))))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) (rows * outputWidth)
        (allocatedRoot heap.top (need outputWidth rows) heap.nodes) result →
      OutputState (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset scaleOffset biasOffset
        width outputWidth rows withBias) valuePtr scalePtr width outputWidth rows result →
      heap.PackedOutput initial final (need outputWidth rows)
        (linearGroupedRows weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias) →
      wp «module» rest Q final result env) :
    wp «module» ((func8.drop 68).take 32 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hGroups, hValueOwner, hScaleOwner, hValueCopyOwner, hValuePtr,
    hValueSize, hScaleCopyOwner, hScalePtr, hScaleSizeLocal, hBytes, hTyped⟩
  have hParamLength : frame.params.length = 13 := by rw [hParams]; rfl
  have hCapacity : (need outputWidth rows).toNat = PackedCapacity.capacityNat (4 * (rows * outputWidth)) :=
    PackedCapacity.capacity_toNat _ hCount
  have hNeed : 4 * (rows * outputWidth) ≤ (need outputWidth rows).toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (need outputWidth rows) hHeap hBound
  have hWeightsAllocated := hAllocFrame.packed hWeightProtected hWeights
  have hValuesAllocated := hAllocFrame.packed
    (by simpa only [grouped_values_size input width rows hMultiple] using hValueProtected) hValues
  have hScalesAllocated := hAllocFrame.packed
    (by simpa only [grouped_scales_size] using hScaleProtected) hScales
  have hBounds := PackedAllocation.root_bounds initial heap.top (need outputWidth rows) heap.nodes hHeap.freeList hBound
  have hWeightSep := hWeightProtected.allocated_disjoint (need outputWidth rows) hBound
  have hValueSep := hValueProtected.allocated_disjoint (need outputWidth rows) hBound
  have hScaleSep := hScaleProtected.allocated_disjoint (need outputWidth rows) hBound
  have hSpace := allocated_capacity (need outputWidth rows) heap.nodes
  rw [emitted_allocation]
  simp only [List.append_assoc]
  apply PackedCapacity.program_spec 95 97 (UInt64.ofNat (4 * (rows * outputWidth))) «module» env initial frame
  · exact hLengthLocal
  · exact hEmpty
  · omega
  · simp [Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame frame 97 (need outputWidth rows)
  have hPreparedParams : prepared.params = frame.params := by
    simp [prepared, FixedArrayCapacity.capacityFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 100 := by
    simp [prepared, FixedArrayCapacity.capacityFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp only [prepared, FixedArrayCapacity.capacityFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 97 heap.top
    (need outputWidth rows) heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · simp [hPreparedParams, hParamLength, hPreparedLocals]
  · simp [prepared, FixedArrayCapacity.capacityFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 84 100 = 84 from rfl]
  apply outputLoop_spec env (heap.allocatePackedStore initial (need outputWidth rows))
    weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr (allocatedRoot heap.top (need outputWidth rows) heap.nodes)
    weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias _
    hWeightsAllocated hValuesAllocated hScalesAllocated hWeightSize hScaleSize hBiasSize hWidth hMultiple
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · omega
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame,
      Locals.get, Locals.validIndex, hParams, parameters, hLocals]
    have h := hLengthLocal
    exact ⟨by simpa [Locals.get, hParams, parameters, hLocals] using h, rfl⟩
  · simp (config := { maxDischargeDepth := 64 }) [OutputState, prepared,
      FixedArrayCapacity.capacityFrame, hParams, parameters, hLocals,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
    exact ⟨(List.getElem_of_getElem? hGroups).choose_spec,
      (List.getElem_of_getElem? hValueOwner).choose_spec,
      (List.getElem_of_getElem? hScaleOwner).choose_spec,
      (List.getElem_of_getElem? hValueCopyOwner).choose_spec,
      (List.getElem_of_getElem? hValuePtr).choose_spec,
      by simpa using (List.getElem_of_getElem? hValueSize).choose_spec,
      (List.getElem_of_getElem? hScaleCopyOwner).choose_spec,
      (List.getElem_of_getElem? hScalePtr).choose_spec,
      by simpa using (List.getElem_of_getElem? hScaleSizeLocal).choose_spec,
      by simpa using (List.getElem_of_getElem? hBytes).choose_spec⟩
  intro final result hReady hState hOutput hWrites
  exact hNext final result hReady hState
    (heap.packedOutput initial final (need outputWidth rows)
      (linearGroupedRows weights input weightOffset scaleOffset biasOffset width outputWidth rows withBias) hHeap
      (by rw [linearGroupedRows_size]; exact hNeed) (fun h => (hBump h).1) hPages
      (by rw [linearGroupedRows_size]; exact hWrites) hOutput)

#print axioms allocatedOutput_spec

end Project.Gpt2QuantizedCached.GroupedProjection.Projection
