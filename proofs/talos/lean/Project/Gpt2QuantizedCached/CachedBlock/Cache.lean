import Project.Gpt2QuantizedCached.CachedBlock.CacheLoop
import Project.Gpt2QuantizedCached.CachedBlock.CacheSize
import Project.Gpt2QuantizedCached.CachedBlock.Resources
import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocationFrame
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2QuantizedCached.CachedBlock
open Project.Gpt2CachedStep.CachedBlock (cacheUpdate cacheUpdate_size)
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def BeforeCacheState (params : List Wasm.Value) (qkvOwner qkvPtr hiddenPtr : UInt64)
    (qkv : ByteArray) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 193 ∧ frame.values = [] ∧
  frame.locals[37]? = some (.i64 qkvOwner) ∧ frame.locals[38]? = some (.i64 qkvPtr) ∧
  frame.locals[39]? = some (.i64 (UInt64.ofNat qkv.size)) ∧
  frame.locals[179]? = some (.i64 hiddenPtr) ∧ frame.locals[180]? = some (.i64 hiddenPtr) ∧
  frame.locals[181]? = some (.i64 3072) ∧ frame.locals[178]? = some (.i64 0) ∧ I64Values frame.locals

def CacheBuiltState (params saved : List Wasm.Value) (qkvOwner qkvPtr hiddenPtr outputPtr : UInt64)
    (qkv : ByteArray) (frame : Locals) : Prop :=
  BeforeCacheState params qkvOwner qkvPtr hiddenPtr qkv frame ∧
  frame.locals[182]? = some (.i64 outputPtr) ∧ frame.locals[183]? = some (.i64 outputPtr) ∧
  frame.locals[184]? = some (.i64 6144) ∧ frame.locals.take 171 = saved

set_option maxRecDepth 32768 in
theorem emitted_cache_prefix : (activatedSuccess.drop 109).take 49 = (activatedSuccess.drop 109).take 11 ++
    PackedCapacity.program 196 198 ++ PackedAllocation.program 198 ++
    [.localGet 203, .localSet 197, .constI64 0, .localSet 183] ++
    (activatedSuccess.drop 151).take 1 ++
    [.localGet 197, .localSet 193, .localGet 193, .localSet 194, .localGet 182, .localSet 195] := rfl

set_option maxRecDepth 32768 in
theorem cache_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Wasm.Value) (qkvOwner qkvPtr hiddenPtr : UInt64) (qkv : ByteArray) (frame : Locals)
    (hHeap : heap.At initial) (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hQkvSize : 9216 ≤ qkv.size)
    (hQkvProtected : heap.Protects qkvPtr.toNat (qkvPtr.toNat + qkv.size))
    (hBump : takeFirstFitFrom 0 cacheNeed heap.nodes = none →
      heap.top.toNat + 48 + cacheNeed.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top cacheNeed ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) (hParamsLength : params.length = 11)
    (hState : BeforeCacheState params qkvOwner qkvPtr hiddenPtr qkv frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      CacheBuiltState params (frame.locals.take 171) qkvOwner qkvPtr hiddenPtr
        (allocatedRoot heap.top cacheNeed heap.nodes) qkv result →
      heap.PackedOutput initial final cacheNeed (cacheUpdate qkv) →
      wp «module» rest Q final result env) :
    wp «module» ((activatedSuccess.drop 109).take 49 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hQkvOwner, hQkvPtr, hQkvBytes,
    hHiddenOwner, hHiddenPtr, hHiddenBytes, hStatus, hTyped⟩
  have hParamLength : frame.params.length = 11 := by rw [hParams, hParamsLength]
  have hNeed : 6144 ≤ cacheNeed.toNat := by decide
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial cacheNeed hHeap hBound
  have hQkvAllocated := hAllocFrame.packed hQkvProtected hQkv
  have hQkvSep := hQkvProtected.allocated_disjoint cacheNeed hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top cacheNeed heap.nodes hHeap.freeList hBound
  have hSpace := allocated_capacity cacheNeed heap.nodes
  rw [emitted_cache_prefix]
  simp only [List.append_assoc]
  apply cacheSize_spec env initial frame hParamLength hLocals hValues
  apply PackedCapacity.program_spec 196 198 6144 «module» env initial (cacheSizeFrame frame)
  · simp [cacheSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [cacheSizeFrame, hParamLength]
  · simp [cacheSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (cacheSizeFrame frame) 198 cacheNeed
  have hPreparedParams : prepared.params = frame.params := by
    simp [prepared, FixedArrayCapacity.capacityFrame, cacheSizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 193 := by
    simp [prepared, FixedArrayCapacity.capacityFrame, cacheSizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      cacheSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 198 heap.top
    cacheNeed heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]
  · simp [prepared, FixedArrayCapacity.capacityFrame, cacheSizeFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 187 193 = 187 from rfl]
  apply cacheLoop_spec env (heap.allocatePackedStore initial cacheNeed)
    params (frame.locals.take 171) qkvOwner qkvPtr hiddenPtr
    (allocatedRoot heap.top cacheNeed heap.nodes) qkv _ hQkvAllocated hQkvSize
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame, cacheSizeFrame,
      Locals.get, Locals.validIndex, hParams, hParamsLength, hLocals]
    rfl
  · simp [hLocals] at hQkvOwner hQkvPtr hQkvBytes hHiddenOwner hHiddenPtr hHiddenBytes hStatus
    simp (config := { maxDischargeDepth := 64 }) [CacheState, prepared,
      FixedArrayCapacity.capacityFrame, cacheSizeFrame, hParams, hParamsLength, hLocals,
      hQkvOwner, hQkvPtr, hQkvBytes, hHiddenOwner, hHiddenPtr, hHiddenBytes, hStatus,
      List.take_set_of_le, List.take_append, List.take_take,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final cacheNeed (cacheUpdate qkv) hHeap
    (by rw [cacheUpdate_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [cacheUpdate_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultParamLength, hResultLocals,
    hResultQkvOwner, hResultQkvPtr, hResultQkvBytes, hResultHiddenOwner, hResultHiddenPtr,
    hResultHiddenBytes, hResultStatus, hByteLength, hResultTyped, hPrefix⟩
  have hResultPointer : result.locals[186]? = some (.i64 (allocatedRoot heap.top cacheNeed heap.nodes)) := by
    simpa [Locals.get, hResultParamLength, hResultLocals] using hReady.2.2.2.1
  wp_packed_frame [hResultParams, hParamsLength, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [CacheBuiltState, BeforeCacheState,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, hResultQkvOwner, hResultQkvPtr, hResultQkvBytes,
      hResultHiddenOwner, hResultHiddenPtr, hResultHiddenBytes, hResultStatus,
      List.take_set_of_le, Nat.reduceLeDiff, hPrefix, and_self]
  · exact hOutput

#print axioms cache_spec

end Project.Gpt2QuantizedCached.CachedBlock
