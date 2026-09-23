import Project.Gpt2QuantizedCached.CachedBlock.Release
import Project.Gpt2QuantizedCached.CachedBlock.Status
import Project.Gpt2QuantizedCached.CachedBlock.CacheResult

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open PackedReleaseMany (Owners Bindings)

def tailHeap (heap : Heap) (position : Nat) : Heap :=
  (cacheHeap heap position).release (projected2Node heap position)

theorem tail_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat) (frame : Locals)
    (hHeap : (activatedHeap heap position).At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hWeightsProtected : (activatedHeap heap position).Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hQkv : (activatedHeap heap position).OwnsPacked initial (qkvNode heap)
      (tensors weights input cache layer position).qkv)
    (hResidual : (activatedHeap heap position).OwnsPacked initial (residualNode heap position)
      (tensors weights input cache layer position).residual)
    (hActivated : (activatedHeap heap position).OwnsPacked initial (activatedNode heap position)
      (tensors weights input cache layer position).activated)
    (hExtent : blocksOffset + layer * blockBytes + blockBytes ≤ weights.size)
    (hInputSize : input.size = 3072)
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLength : frame.locals.length = 193) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (hBase : frame.locals[0]? = some (.i64 (UInt64.ofNat (blocksOffset + layer * blockBytes))))
    (hQkvOwner : frame.locals[37]? = some (.i64 (qkvNode heap).root))
    (hQkvPtr : frame.locals[38]? = some (.i64 (qkvNode heap).root))
    (hQkvSize : frame.locals[39]? = some (.i64 9216))
    (hResidualOwner : frame.locals[87]? = some (.i64 (residualNode heap position).root))
    (hResidualPtr : frame.locals[88]? = some (.i64 (residualNode heap position).root))
    (hResidualSize : frame.locals[89]? = some (.i64 3072))
    (hActivatedOwner : frame.locals[135]? = some (.i64 (activatedNode heap position).root))
    (hActivatedPtr : frame.locals[136]? = some (.i64 (activatedNode heap position).root))
    (hActivatedSize : frame.locals[137]? = some (.i64 12288))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      ResultState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 143) 143 true
        (hiddenNode heap position).root (cacheNode heap position).root result →
      Completion (activatedHeap heap position) initial (tailHeap heap position) final true
        (hiddenNode heap position) (cacheNode heap position)
        (tensors weights input cache layer position).hidden
        (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (tensors weights input cache layer position).qkv) →
      wp «module» rest Q final result env) :
    wp «module» (activatedSuccess ++ rest) Q initial frame env := by
  let values := tensors weights input cache layer position
  let params := parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position
  have hSizes : values.Sizes := tensors_sizes weights input cache layer position hInputSize
  rw [activatedSuccess_shape]
  simp only [List.append_assoc]
  apply projected2_spec env initial (activatedHeap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (activatedNode heap position).root
    weights input cache values.activated layer position (blocksOffset + layer * blockBytes) frame
    hHeap hWeights hActivated.buffer.values hWeightsProtected hActivated.payload_protects
    hSizes.activated hExtent hResources.projected2 hPages hParams hLength hValues hBase hTyped
    hActivatedOwner hActivatedPtr hActivatedSize
  intro store9 frame9 hState9 hOutput9
  have hFresh9 := GroupedProjection.Projection.outputNode_fresh hResources.projected2
  let item : PackedReleaseMany.Item := ⟨167, projected2Node heap position, values.projected2⟩
  have hOwners9 : Owners (activatedHeap heap position) (projected2Heap heap position) store9 [item] :=
    (Owners.nil (activatedHeap heap position) (activatedHeap heap position) initial).cons
      (Heap.Frame.refl _ _) hOutput9.frame hOutput9.heapAt item hOutput9.owned hFresh9
  have hBinding9 : Bindings [item] frame9 :=
    (by simp only [Bindings, List.not_mem_nil, false_implies, implies_true] : Bindings [] frame9).cons
      item (hState9.owner_get (by decide))
  rcases hState9 with ⟨hParams9, hLength9, hValues9, hTyped9, hPrefix9,
    hOwner9, hPtr9, hSize9, hCopyOwner9, hCopyPtr9, hCopySize9⟩
  apply successFrame_spec env store9 frame9 (by rw [hParams9]; rfl) hLength9 hValues9
  have hResource10 : Gpt2CachedStep.LayerNorm.AllocationFits (projected2Heap heap position)
      residualNeed (store9.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [← memoryCap_eq_fp32, hOutput9.memoryCap]
    exact hResources.hidden
  have read9 (index : Nat) (hi : index < 143) :
      (successFrame frame9).locals[index]? = frame.locals[index]? := by
    simp only [successFrame, List.getElem?_set, hLength9,
      show 178 ≠ index from by omega, reduceIte]
    exact Frame.local_of_take_eq hPrefix9 hi
  apply hidden_spec env store9 (projected2Heap heap position) params
    (residualNode heap position).root (projected2Node heap position).root values.residual values.projected2
    (successFrame frame9) hOutput9.heapAt (hOutput9.frame.packed hResidual.payload_protects hResidual.buffer.values)
    hOutput9.owned.buffer.values (hOutput9.frame.protects _ _ hResidual.payload_protects)
    hOutput9.owned.payload_protects hSizes.residual hSizes.projected2 hResource10 hOutput9.pages
    hParams9 rfl (by simp only [successFrame, List.length_set, hLength9]) hValues9
    (I64Values.set hTyped9 _ _) ((read9 87 (by decide)).trans hResidualOwner)
    ((read9 88 (by decide)).trans hResidualPtr) ((read9 89 (by decide)).trans hResidualSize)
  · simpa only [successFrame, projected2Node, List.getElem?_set, hLength9, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, show UInt64.ofNat 3072 = 3072 from rfl] using hCopyOwner9
  · simpa only [successFrame, projected2Node, List.getElem?_set, hLength9, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, show UInt64.ofNat 3072 = 3072 from rfl] using hCopyPtr9
  · simpa only [successFrame, projected2Node, List.getElem?_set, hLength9, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, reduceIte, show UInt64.ofNat 3072 = 3072 from rfl] using hCopySize9
  intro store10 frame10 hState10 hStatus10 hHeap10 hOwned10 hStep10 hPages10 hCap10
  have hFrame10 := hOutput9.frame.trans hStep10
  have hCapacity10 : store10.memoryCap «module» 0 = initial.memoryCap «module» 0 := by
    rw [memoryCap_eq_fp32, hCap10, ← memoryCap_eq_fp32, hOutput9.memoryCap]
  have hFresh10 := (projected2Heap heap position).freshNode_allocated residualNeed
    (fun h => (hResources.hidden h).1.le)
  have hOwners10 := hOwners9.frame hStep10 hHeap10
  have hHiddenSep := hOwners9.disjoint_fresh hOwned10 hFresh10
  rcases hState10 with ⟨hParams10, hLength10, hValues10, hTyped10, hPrefix10,
    hOwner10, hPtr10, hSize10, hCopyOwner10, hCopyPtr10, hCopySize10⟩
  have read10 (index : Nat) (hi : index < 143) : frame10.locals[index]? = frame.locals[index]? :=
    (Frame.local_of_take_eq hPrefix10 (by omega)).trans (read9 index hi)
  have hResource11 : Gpt2CachedStep.LayerNorm.AllocationFits (hiddenHeap heap position)
      cacheNeed (store10.memoryCap «module» 0) := by rw [hCapacity10]; exact hResources.cache
  have hQkv10 := hFrame10.ownsPacked hHeap10 hQkv
  apply cache_spec env store10 (hiddenHeap heap position) params (qkvNode heap).root (qkvNode heap).root
    (hiddenNode heap position).root values.qkv frame10 hHeap10 hQkv10.buffer.values
    (by rw [hSizes.qkv]) hQkv10.payload_protects hResource11 hPages10 rfl
    ⟨hParams10, hLength10, hValues10, (read10 37 (by decide)).trans hQkvOwner,
      (read10 38 (by decide)).trans hQkvPtr, by rw [hSizes.qkv]; exact (read10 39 (by decide)).trans hQkvSize,
      hCopyOwner10, hCopyPtr10, hCopySize10, by simpa only [successFrame, List.getElem?_set_self,
        hLength9, Nat.reduceLT, reduceIte] using hStatus10, hTyped10⟩
  intro store11 frame11 hState11 hOutput11
  have hOwners11 := hOwners10.frame hOutput11.frame hOutput11.heapAt
  have hHidden11 := hOutput11.frame.ownsPacked hOutput11.heapAt hOwned10
  have hFresh11 := (hiddenHeap heap position).freshNode_allocated cacheNeed
    (fun h => (hResources.cache h).1.le)
  have hCacheSep := hOwners10.disjoint_fresh hOutput11.owned hFresh11
  have hOutputSep := hOwned10.allocation_disjoint cacheNeed (fun h => (hResources.cache h).1.le)
  have hSaved : (frame10.locals.take 171).take 143 = frame.locals.take 143 := by
    have h10 := congrArg (List.take 143) hPrefix10
    simp only [List.take_take, show min 143 162 = 143 from rfl, successFrame,
      List.take_set_of_le (by decide : 143 ≤ 178)] at h10
    simpa only [List.take_take, show min 143 171 = 143 from rfl] using h10.trans hPrefix9
  have hResult11 : ResultState params (frame.locals.take 143) 143 true
      (hiddenNode heap position).root (cacheNode heap position).root frame11 := by
    rw [cacheNode_root]
    exact hState11.resultState (by decide) hSaved
  rcases hState11 with ⟨⟨hParams11, hLength11, hValues11, _, _, _, hHiddenOwner11, hHiddenPtr11,
    hHiddenBytes11, hStatus11, hTyped11⟩, hCacheOwner11, hCachePtr11, hCacheBytes11, hPrefix11⟩
  have hOutput : Completion (activatedHeap heap position) initial (cacheHeap heap position) store11 true
      (hiddenNode heap position) (cacheNode heap position) values.hidden
      (Project.Gpt2CachedStep.CachedBlock.cacheUpdate values.qkv) :=
    ⟨hOutput11.heapAt, hFrame10.trans hOutput11.frame, hOutput11.pages,
      (hOutput11.memoryCap «module» 0).trans hCapacity10,
      fun _ => ⟨hHidden11, hOutput11.owned⟩,
      fun _ => ⟨hOutput9.frame.freshNode hFresh10, hFrame10.freshNode hFresh11⟩, fun _ => hOutputSep⟩
  have hBinding10 : Bindings [item] frame10 := by
    apply hBinding9.prefix (hParams10.trans hParams9.symm) (count := 162)
    · simpa only [successFrame, List.take_set_of_le (by decide : 162 ≤ 178)] using hPrefix10
    · rw [hLength9]; decide
    · rw [hLength10]; decide
    · simp [item, hParams9, parameters]
  have hBinding11 : Bindings [item] frame11 :=
    hBinding10.prefix (hParams11.trans hParams10.symm) hPrefix11
      (by rw [hLength10]; decide) (by rw [hLength11]; decide) (by simp [item, hParams10, params, parameters])
  apply release_spec env (activatedHeap heap position) (cacheHeap heap position) initial store11
    params (frame.locals.take 143) 143 true (hiddenNode heap position) (cacheNode heap position)
    values.hidden (Project.Gpt2CachedStep.CachedBlock.cacheUpdate values.qkv) frame11 [item]
    hOutput hOwners11 hBinding11 (fun _ => hHiddenSep) (fun _ => hCacheSep) hResult11 rfl
  intro hFinal
  exact hNext _ _ hResult11 hFinal

#print axioms tail_spec
end Project.Gpt2QuantizedCached.CachedBlock
