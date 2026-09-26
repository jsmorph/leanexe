import Project.Gpt2CachedStep.CachedAttention.FrozenScoresSize
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def scoresNeed (position : Nat) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (4 * (12 * (position + 1))))

def ScoresBuiltState (params : List Wasm.Value) (pointer : UInt64) (position : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 114 ∧ frame.values = [] ∧
  frame.locals[0]? = some (.i64 (UInt64.ofNat (position + 1))) ∧
  frame.locals[14]? = some (.i64 pointer) ∧ frame.locals[15]? = some (.i64 pointer) ∧
  frame.locals[16]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1))))) ∧ I64Values frame.locals

set_option maxRecDepth 32768 in
theorem emitted_scores_prefix : func29.take 68 = func29.take 30 ++ PackedCapacity.program 109 111 ++
    PackedAllocation.program 111 ++ [.localGet 116, .localSet 110, .constI64 0, .localSet 10] ++
    (func29.drop 61).take 1 ++
    [.localGet 110, .localSet 22, .localGet 22, .localSet 23, .localGet 9, .localSet 24] := rfl

set_option maxRecDepth 32768 in
theorem scores_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache) (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hQkvProtected : heap.Protects qkvPtr.toNat (qkvPtr.toNat + qkv.size))
    (hBump : takeFirstFitFrom 0 (scoresNeed position) heap.nodes = none →
      heap.top.toNat + 48 + (scoresNeed position).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (scoresNeed position) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
    (hLocals : frame.locals.length = 114) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      ScoresBuiltState (parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position)
        (allocatedRoot heap.top (scoresNeed position) heap.nodes) position result →
      heap.PackedOutput initial final (scoresNeed position) (scores cache qkv layer position) →
      wp «module» rest Q final result env) :
    wp «module» (func29.take 68 ++ rest) Q initial frame env := by
  have hCount : 4 * (12 * (position + 1)) ≤ 2^32 := by omega
  have hParamLength : frame.params.length = 8 := by rw [hParams]; rfl
  have hCapacity : (scoresNeed position).toNat = PackedCapacity.capacityNat (4 * (12 * (position + 1))) :=
    PackedCapacity.capacity_toNat _ hCount
  have hNeed : 4 * (12 * (position + 1)) ≤ (scoresNeed position).toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (scoresNeed position) hHeap hBound
  have hCacheAllocated := hAllocFrame.packed hCacheProtected hCache
  have hQkvAllocated := hAllocFrame.packed hQkvProtected hQkv
  have hBounds := PackedAllocation.root_bounds initial heap.top (scoresNeed position) heap.nodes hHeap.freeList hBound
  have hCacheSep := hCacheProtected.allocated_disjoint (scoresNeed position) hBound
  have hQkvSep := hQkvProtected.allocated_disjoint (scoresNeed position) hBound
  have hSpace := allocated_capacity (scoresNeed position) heap.nodes
  rw [emitted_scores_prefix]
  simp only [List.append_assoc]
  apply scoresSize_spec env initial frame position hParamLength hLocals hValues
    (by rw [hParams]; rfl) hPosition
  apply PackedCapacity.program_spec 109 111 (UInt64.ofNat (4 * (12 * (position + 1)))) «module» env initial
    (scoresSizeFrame frame position)
  · simp [scoresSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [scoresSizeFrame, hParamLength]
  · simp [scoresSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (scoresSizeFrame frame position) 111 (scoresNeed position)
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, scoresSizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 114 := by simp [prepared, FixedArrayCapacity.capacityFrame, scoresSizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      scoresSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 111 heap.top
    (scoresNeed position) heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
  · simp [prepared, FixedArrayCapacity.capacityFrame, scoresSizeFrame, Locals.get, hParamLength, hLocals]
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
  apply scoresLoop_spec env (heap.allocatePackedStore initial (scoresNeed position))
    cacheOwner qkvOwner cachePtr qkvPtr (allocatedRoot heap.top (scoresNeed position) heap.nodes)
    cache qkv layer position _ hCacheAllocated hQkvAllocated hLayer hPosition hCacheSize hQkvSize
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · omega
  · simp [PackedGenerateLoop.Ready,
      prepared, FixedArrayCapacity.capacityFrame, scoresSizeFrame, Locals.get, Locals.validIndex,
      hParams, parameters, hLocals]
    rfl
  · simp (config := { maxDischargeDepth := 64 }) [ScoresState,
      prepared,
      FixedArrayCapacity.capacityFrame, scoresSizeFrame, hParams, parameters, hLocals,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final (scoresNeed position) (scores cache qkv layer position) hHeap
    (by rw [scores_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [scores_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hSize, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[102]? = some (.i64 (allocatedRoot heap.top (scoresNeed position) heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  simp only [parameters] at hResultParams
  wp_packed_frame [hResultParams, hResultLocals, hReady.1, hResultPointer, hByteLength, hSize]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [ScoresBuiltState, parameters,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      hSize, I64Values.set, hResultTyped, and_self]
  · exact hOutput

#print axioms scores_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
