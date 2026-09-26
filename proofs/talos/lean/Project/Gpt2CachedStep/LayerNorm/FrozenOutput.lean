import Project.Gpt2CachedStep.LayerNorm.FrozenInverses
import Project.Gpt2CachedStep.LayerNorm.FrozenOutputSize

namespace Project.Gpt2CachedStep.Frozen.LayerNorm
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def outputNeed (rows : Nat) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (4 * (rows * 768)))

def OutputBuiltState (params : List Wasm.Value) (meansPtr inversesPtr outputPtr : UInt64)
    (rows : Nat) (frame : Locals) : Prop :=
  InversesBuiltState params meansPtr inversesPtr rows frame ∧
  frame.locals[58]? = some (.i64 outputPtr) ∧ frame.locals[59]? = some (.i64 outputPtr) ∧
  frame.locals[60]? = some (.i64 (UInt64.ofNat (4 * (rows * 768))))

set_option maxRecDepth 32768 in
theorem emitted_output_prefix : (func20.drop 98).take 58 = (func20.drop 98).take 18 ++ PackedCapacity.program 70 72 ++
    PackedAllocation.program 72 ++ [.localGet 77, .localSet 71, .constI64 0, .localSet 45] ++
    (func20.drop 147).take 1 ++
    [.localGet 71, .localSet 66, .localGet 66, .localSet 67, .localGet 66, .localSet 68,
      .localGet 44, .localSet 69] := rfl

set_option maxRecDepth 32768 in
theorem output_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr meansPtr inversesPtr : UInt64) (weights input : ByteArray)
    (scaleOffset biasOffset rows : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hScaleSize : (scaleOffset + 768) * 4 ≤ weights.size)
    (hBiasSize : (biasOffset + 768) * 4 ≤ weights.size)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputSize : rows * 768 * 4 ≤ input.size)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hMeans : ByteArrayAt initial.mem meansPtr.toNat (means input rows))
    (hMeansProtected : heap.Protects meansPtr.toNat (meansPtr.toNat + (means input rows).size))
    (hInverses : ByteArrayAt initial.mem inversesPtr.toNat (inverses input rows))
    (hInversesProtected : heap.Protects inversesPtr.toNat (inversesPtr.toNat + (inverses input rows).size))
    (hCount : 4 * (rows * 768) ≤ 2^32)
    (hBump : takeFirstFitFrom 0 (outputNeed rows) heap.nodes = none →
      heap.top.toNat + 48 + (outputNeed rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (outputNeed rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hState : InversesBuiltState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input
      scaleOffset biasOffset rows) meansPtr inversesPtr rows frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      OutputBuiltState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input scaleOffset biasOffset rows)
        meansPtr inversesPtr (allocatedRoot heap.top (outputNeed rows) heap.nodes) rows result →
      heap.PackedOutput initial final (outputNeed rows) (LeanExe.Models.Gpt2.layerNorm weights input scaleOffset biasOffset rows) →
      wp «module» rest Q final result env) :
    wp «module» ((func20.drop 98).take 58 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, hMeansOwner, hMeansPointer, hMeansSize, hTyped⟩,
    hInversesOwner, hInversesPointer, hInversesSize⟩
  have hParamLength : frame.params.length = 9 := by rw [hParams]; rfl
  have hCapacity : (outputNeed rows).toNat = PackedCapacity.capacityNat (4 * (rows * 768)) :=
    PackedCapacity.capacity_toNat _ hCount
  have hNeed : 4 * (rows * 768) ≤ (outputNeed rows).toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (outputNeed rows) hHeap hBound
  have hWeightsAllocated := hAllocFrame.packed hWeightsProtected hWeights
  have hWeightsSep := hWeightsProtected.allocated_disjoint (outputNeed rows) hBound
  have hInversesAllocated := hAllocFrame.packed hInversesProtected hInverses
  have hInversesSep := hInversesProtected.allocated_disjoint (outputNeed rows) hBound
  have hInputAllocated := hAllocFrame.packed hInputProtected hInput
  have hMeansAllocated := hAllocFrame.packed hMeansProtected hMeans
  have hMeansSep := hMeansProtected.allocated_disjoint (outputNeed rows) hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top (outputNeed rows) heap.nodes hHeap.freeList hBound
  have hSep := hInputProtected.allocated_disjoint (outputNeed rows) hBound
  have hSpace := allocated_capacity (outputNeed rows) heap.nodes
  rw [emitted_output_prefix]
  simp only [List.append_assoc]
  apply outputSize_spec env initial frame rows hParamLength hLocals hValues
    (by rw [hParams]; rfl) hCount
  apply PackedCapacity.program_spec 70 72 (UInt64.ofNat (4 * (rows * 768))) «module» env initial
    (outputSizeFrame frame rows)
  · simp [outputSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [outputSizeFrame, hParamLength]
  · simp [outputSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (outputSizeFrame frame rows) 72 (outputNeed rows)
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, outputSizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 74 := by simp [prepared, FixedArrayCapacity.capacityFrame, outputSizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      outputSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 72 heap.top
    (outputNeed rows) heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
  · simp [prepared, FixedArrayCapacity.capacityFrame, outputSizeFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 63 74 = 63 from rfl]
  apply outputLoop_spec env (heap.allocatePackedStore initial (outputNeed rows))
    weightsOwner inputOwner weightsPtr inputPtr meansPtr meansPtr inversesPtr inversesPtr (allocatedRoot heap.top (outputNeed rows) heap.nodes)
    weights input scaleOffset biasOffset rows _ hWeightsAllocated hInputAllocated hMeansAllocated hInversesAllocated
    hInputSize hScaleSize hBiasSize
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · omega
  · omega
  · omega
  · simp [PackedGenerateLoop.Ready,
      prepared, FixedArrayCapacity.capacityFrame, outputSizeFrame, Locals.get, Locals.validIndex,
      hParams, parameters, hLocals]
    rfl
  · simp [hLocals] at hMeansOwner hMeansPointer hMeansSize hInversesOwner hInversesPointer hInversesSize
    simp (config := { maxDischargeDepth := 64 }) [OutputState,
      prepared,
      FixedArrayCapacity.capacityFrame, outputSizeFrame, hParams, parameters, hLocals, hMeansOwner, hMeansPointer, hMeansSize, hInversesOwner, hInversesPointer, hInversesSize,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final (outputNeed rows) (LeanExe.Models.Gpt2.layerNorm weights input scaleOffset biasOffset rows) hHeap
    (by rw [layerNorm_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [layerNorm_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hResultMeansOwner, hResultMeansPtr, hResultMeansSize,
    hResultInversesOwner, hResultInversesPtr, hResultInversesSize, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[62]? = some (.i64 (allocatedRoot heap.top (outputNeed rows) heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  simp only [parameters] at hResultParams
  wp_packed_frame [hResultParams, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [OutputBuiltState, InversesBuiltState, MeansBuiltState, parameters,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, hResultMeansOwner, hResultMeansPtr, hResultMeansSize,
      hResultInversesOwner, hResultInversesPtr, hResultInversesSize, and_self]
  · exact hOutput

#print axioms output_spec

end Project.Gpt2CachedStep.Frozen.LayerNorm
