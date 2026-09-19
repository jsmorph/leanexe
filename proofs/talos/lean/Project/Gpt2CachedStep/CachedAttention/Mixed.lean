import Project.Gpt2CachedStep.CachedAttention.Probabilities
import Project.Gpt2CachedStep.CachedAttention.MixedLoop
import Project.ProofKit.LocalPrefix

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def mixedNeed : UInt64 := PackedCapacity.capacity 3072

def MixedBuiltState (params : List Wasm.Value) (scorePtr maximumPtr exponentialPtr sumPtr probabilityPtr outputPtr : UInt64)
    (position : Nat) (frame : Locals) : Prop :=
  ProbabilitiesBuiltState params scorePtr maximumPtr exponentialPtr sumPtr probabilityPtr position frame ∧
  frame.locals[98]? = some (.i64 outputPtr) ∧ frame.locals[99]? = some (.i64 outputPtr) ∧
  frame.locals[100]? = some (.i64 3072)

set_option maxRecDepth 32768 in
theorem emitted_mixed_prefix : (func29.drop 278).take 51 = fixedSizeCode 768 76 ++ PackedCapacity.program 109 111 ++
    PackedAllocation.program 111 ++ [.localGet 116, .localSet 110, .constI64 0, .localSet 77] ++
    (func29.drop 320).take 1 ++
    [.localGet 110, .localSet 105, .localGet 105, .localSet 106,
      .localGet 105, .localSet 107, .localGet 76, .localSet 108] := rfl

set_option maxRecDepth 32768 in
theorem mixed_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (cacheOwner qkvOwner cachePtr qkvPtr scorePtr maximumPtr exponentialPtr sumPtr probabilityPtr : UInt64)
    (cache qkv probabilityValues : ByteArray) (layer position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache) (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hProbabilities : ByteArrayAt initial.mem probabilityPtr.toNat probabilityValues)
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hProbabilitySize : probabilityValues.size = 4 * (12 * (position + 1)))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hQkvProtected : heap.Protects qkvPtr.toNat (qkvPtr.toNat + qkv.size))
    (hProbabilityProtected : heap.Protects probabilityPtr.toNat (probabilityPtr.toNat + probabilityValues.size))
    (hBump : takeFirstFitFrom 0 mixedNeed heap.nodes = none →
      heap.top.toNat + 48 + mixedNeed.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top mixedNeed ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hState : ProbabilitiesBuiltState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
      scorePtr maximumPtr exponentialPtr sumPtr probabilityPtr position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      MixedBuiltState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
        scorePtr maximumPtr exponentialPtr sumPtr probabilityPtr (allocatedRoot heap.top mixedNeed heap.nodes) position result →
      heap.PackedOutput initial final mixedNeed (mixed cache qkv probabilityValues layer position) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 278).take 51 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨⟨⟨⟨hParams, hLocals, hValues, hSize, hScoreOwner, hScorePointer, hScoreBytes, hTyped⟩,
    hMaximumOwner, hMaximumPointer, hMaximumBytes⟩, hExponentialOwner, hExponentialPointer, hExponentialBytes⟩,
    hSumOwner, hSumPointer, hSumBytes⟩, hProbabilityOwner, hProbabilityPointer, hProbabilityBytes⟩
  have hParamLength : frame.params.length = 8 := by rw [hParams]; rfl
  have hNeed : 3072 ≤ mixedNeed.toNat := by decide
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial mixedNeed hHeap hBound
  have hProbabilitiesAllocated := hAllocFrame.packed hProbabilityProtected hProbabilities
  have hCacheAllocated := hAllocFrame.packed hCacheProtected hCache
  have hQkvAllocated := hAllocFrame.packed hQkvProtected hQkv
  have hCacheSep := hCacheProtected.allocated_disjoint mixedNeed hBound
  have hQkvSep := hQkvProtected.allocated_disjoint mixedNeed hBound
  have hScoreSep := hProbabilityProtected.allocated_disjoint mixedNeed hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top mixedNeed heap.nodes hHeap.freeList hBound
  have hSpace := allocated_capacity mixedNeed heap.nodes
  rw [emitted_mixed_prefix]
  simp only [List.append_assoc]
  apply fixedSize_spec env initial frame 768 76 hParamLength hLocals hValues
    (by decide) (by decide) (by decide)
  apply PackedCapacity.program_spec 109 111 3072 «module» env initial (fixedSizeFrame frame 768 76)
  · simp [fixedSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [fixedSizeFrame, hParamLength]
  · simp [fixedSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (fixedSizeFrame frame 768 76) 111 mixedNeed
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, fixedSizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 114 := by simp [prepared, FixedArrayCapacity.capacityFrame, fixedSizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      fixedSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 111 heap.top
    mixedNeed heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
  · simp [prepared, FixedArrayCapacity.capacityFrame, fixedSizeFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 103 114 = 103 from rfl]
  apply mixedLoop_spec env (heap.allocatePackedStore initial mixedNeed)
    cacheOwner qkvOwner cachePtr qkvPtr probabilityPtr (allocatedRoot heap.top mixedNeed heap.nodes)
    cache qkv probabilityValues (frame.locals.take 68) layer position _ hCacheAllocated hQkvAllocated hProbabilitiesAllocated
    hLayer hPosition hCacheSize hQkvSize (by rw [hProbabilitySize])
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · omega
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame, fixedSizeFrame,
      Locals.get, Locals.validIndex, hParams, parameters, hLocals]
    rfl
  · simp [hLocals] at hSize hProbabilityOwner hProbabilityPointer hProbabilityBytes
    simp (config := { maxDischargeDepth := 64 }) [MixedState, prepared,
      FixedArrayCapacity.capacityFrame, fixedSizeFrame, hParams, parameters, hLocals,
      hSize, hProbabilityOwner, hProbabilityPointer, hProbabilityBytes, hProbabilitySize,
      List.take_set_of_le, List.take_append, List.take_take,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final mixedNeed (mixed cache qkv probabilityValues layer position) hHeap
    (by rw [mixed_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [mixed_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hResultSize,
    hResultProbabilityOwner, hResultProbabilityPtr, hResultProbabilityBytes, hByteLength, hResultTyped, hPrefix⟩
  have hResultPointer : result.locals[102]? = some (.i64 (allocatedRoot heap.top mixedNeed heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  wp_packed_frame [hResultParams, parameters, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [MixedBuiltState, ProbabilitiesBuiltState, SumsBuiltState, ExponentialsBuiltState, MaximaBuiltState, ScoresBuiltState, parameters,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, Frame.local_of_take_eq hPrefix,
      hSize, hScoreOwner, hScorePointer, hScoreBytes, hMaximumOwner, hMaximumPointer, hMaximumBytes,
      hExponentialOwner, hExponentialPointer, hExponentialBytes, hSumOwner, hSumPointer, hSumBytes,
      hProbabilityOwner, hProbabilityPointer, hProbabilityBytes, and_self]
  · exact hOutput

#print axioms mixed_spec

end Project.Gpt2CachedStep.CachedAttention
