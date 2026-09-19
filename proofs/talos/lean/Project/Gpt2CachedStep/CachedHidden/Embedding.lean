import Project.Gpt2CachedStep.CachedHidden.EmbeddingLoop
import Project.Gpt2CachedStep.CachedHidden.EmbeddingSize
import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocationFrame
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2

def embeddingNeed : UInt64 := PackedCapacity.capacity 3072

def EmbeddingBuiltState (params : List Wasm.Value) (ptr : UInt64) (frame : Locals) : Prop :=
  EmbeddingState params frame ∧ frame.values = [] ∧
  frame.locals[11]? = some (.i64 ptr) ∧ frame.locals[12]? = some (.i64 ptr) ∧
  frame.locals[13]? = some (.i64 3072)

set_option maxRecDepth 32768 in
theorem emitted_embeddingPrefix : func36.take 49 = func36.take 11 ++
    PackedCapacity.program 103 105 ++ PackedAllocation.program 105 ++
    [.localGet 110, .localSet 104, .constI64 0, .localSet 9] ++
    (func36.drop 42).take 1 ++
    [.localGet 104, .localSet 19, .localGet 19, .localSet 20, .localGet 8, .localSet 21] := rfl

theorem embedding_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hTokenSize : 4 * (token.toNat * 768 + 768) ≤ weights.size)
    (hPositionSize : 4 * (positionOffset + position * 768 + 768) ≤ weights.size)
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hBump : takeFirstFitFrom 0 embeddingNeed heap.nodes = none →
      heap.top.toNat + 48 + embeddingNeed.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top embeddingNeed ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
    (hLocals : frame.locals.length = 119) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      EmbeddingBuiltState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        (allocatedRoot heap.top embeddingNeed heap.nodes) result →
      heap.PackedOutput initial final embeddingNeed (embedding weights token position) →
      wp «module» rest Q final result env) :
    wp «module» (func36.take 49 ++ rest) Q initial frame env := by
  have hParamLength : frame.params.length = 8 := by rw [hParams]; rfl
  have hNeed : 3072 ≤ embeddingNeed.toNat := by decide
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial embeddingNeed hHeap hBound
  have hWeightsAllocated := hAllocFrame.packed hWeightsProtected hWeights
  have hSep := hWeightsProtected.allocated_disjoint embeddingNeed hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top embeddingNeed heap.nodes hHeap.freeList hBound
  have hSpace := allocated_capacity embeddingNeed heap.nodes
  rw [emitted_embeddingPrefix]
  simp only [List.append_assoc]
  apply embeddingSize_spec env initial frame hParamLength hLocals hValues
  apply PackedCapacity.program_spec 103 105 3072 «module» env initial (embeddingSizeFrame frame)
  · simp [embeddingSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [embeddingSizeFrame, hParamLength]
  · simp [embeddingSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (embeddingSizeFrame frame) 105 embeddingNeed
  have hPreparedParams : prepared.params = frame.params := rfl
  have hPreparedLocals : prepared.locals.length = 119 := by
    simp [prepared, FixedArrayCapacity.capacityFrame, embeddingSizeFrame, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      embeddingSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 105 heap.top
    embeddingNeed heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
  · simp [prepared, FixedArrayCapacity.capacityFrame, embeddingSizeFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 97 119 = 97 from rfl]
  apply embeddingLoop_spec env (heap.allocatePackedStore initial embeddingNeed)
    weightsOwner weightsPtr cacheOwner cachePtr (allocatedRoot heap.top embeddingNeed heap.nodes)
    weights cache token position _ hWeightsAllocated hTokenSize hPositionSize hToken hPosition
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame,
      embeddingSizeFrame, Locals.get, Locals.validIndex, hParams, parameters, hLocals]
    rfl
  · simp (config := { maxDischargeDepth := 64 }) [EmbeddingState, prepared,
      FixedArrayCapacity.capacityFrame, embeddingSizeFrame, hParams, parameters, hLocals,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final embeddingNeed (embedding weights token position) hHeap
    (by rw [embedding_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [embedding_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[96]? = some (.i64 (allocatedRoot heap.top embeddingNeed heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  wp_packed_frame [hResultParams, parameters, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [EmbeddingBuiltState, EmbeddingState, parameters,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, hByteLength, UInt64.ofNat_uInt32ToNat, and_self]
  · exact hOutput

#print axioms embedding_spec

end Project.Gpt2CachedStep.CachedHidden
