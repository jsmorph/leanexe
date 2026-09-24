import Project.Gpt2CachedStep.Vocabulary.FrozenLoop
import Project.Gpt2CachedStep.Vocabulary.FrozenSize
import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocationFrame
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2CachedStep.Frozen.Vocabulary
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

def outputNeed : UInt64 := PackedCapacity.capacity 201028

theorem vocabularyHead_size (weights input : ByteArray) : (vocabularyHead weights input).size = 201028 := by
  rw [vocabularyHead_eq]
  exact PackedSource.generate_size ..

set_option maxRecDepth 32768 in
theorem emitted_body : func37 = func37.take 11 ++ PackedCapacity.program 28 30 ++ PackedAllocation.program 30 ++
    [.localGet 35, .localSet 29, .constI64 0, .localSet 7] ++ (func37.drop 42).take 1 ++
    [.localGet 29, .localSet 24, .localGet 24, .localSet 25, .localGet 24, .localSet 26,
     .localGet 6, .localSet 27, .localGet 25, .localGet 26, .localGet 27] := rfl

theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsSize : 50257 * 768 * 4 ≤ weights.size) (hInputSize : 3072 ≤ input.size)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hBump : takeFirstFitFrom 0 outputNeed heap.nodes = none →
      heap.top.toNat + 48 + outputNeed.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top outputNeed ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner weightsPtr inputPtr weights input)
    (hLocals : frame.locals.length = 35) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit)
    (hNext : ∀ final result,
      result.values = [.i64 201028, .i64 (allocatedRoot heap.top outputNeed heap.nodes),
        .i64 (allocatedRoot heap.top outputNeed heap.nodes)] →
      heap.PackedOutput initial final outputNeed (vocabularyHead weights input) → Q (.Fallthrough final result)) :
    wp «module» func37 Q initial frame env := by
  have hParamLength : frame.params.length = 6 := by rw [hParams]; rfl
  have hNeed : 201028 ≤ outputNeed.toNat := by decide
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial outputNeed hHeap hBound
  have hWeightsAllocated := hAllocFrame.packed hWeightsProtected hWeights
  have hInputAllocated := hAllocFrame.packed hInputProtected hInput
  have hWeightsSep := hWeightsProtected.allocated_disjoint outputNeed hBound
  have hInputSep := hInputProtected.allocated_disjoint outputNeed hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top outputNeed heap.nodes hHeap.freeList hBound
  have hSpace := allocated_capacity outputNeed heap.nodes
  rw [emitted_body]
  simp only [List.append_assoc]
  apply size_spec env initial frame hParamLength hLocals hValues
  apply PackedCapacity.program_spec 28 30 201028 «module» env initial (sizeFrame frame)
  · simp [sizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [sizeFrame, hParamLength]
  · simp [sizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (sizeFrame frame) 30 outputNeed
  have hPreparedParams : prepared.params = frame.params := rfl
  have hPreparedLocals : prepared.locals.length = 35 := by
    simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      sizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 30 heap.top outputNeed heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
  · simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 24 35 = 24 from rfl]
  apply loop_spec env (heap.allocatePackedStore initial outputNeed) weightsOwner inputOwner weightsPtr inputPtr
    (allocatedRoot heap.top outputNeed heap.nodes) weights input _ hWeightsAllocated hInputAllocated hInputSize hWeightsSize
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame, sizeFrame,
      Locals.get, Locals.validIndex, hParams, parameters, hLocals]
    rfl
  · simp (config := { maxDischargeDepth := 64 }) [OutputState, prepared, FixedArrayCapacity.capacityFrame,
      sizeFrame, hParams, parameters, hLocals, I64Values.set, I64Values.append, I64Values.cons,
      I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final outputNeed (vocabularyHead weights input) hHeap
    (by rw [vocabularyHead_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [vocabularyHead_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hByteLength, _⟩
  have hResultPointer : result.locals[23]? = some (.i64 (allocatedRoot heap.top outputNeed heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  wp_packed_frame [hResultParams, parameters, hResultLocals, hReady.1, hResultPointer, hByteLength]
  exact hNext _ _ rfl hOutput

#print axioms body_spec

end Project.Gpt2CachedStep.Frozen.Vocabulary
