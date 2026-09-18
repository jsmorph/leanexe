import Project.Gpt2CachedStep.CachedBlock.Front
import Project.Gpt2CachedStep.CachedBlock.CompositionState

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2
open PackedReleaseMany (Owners Bindings)

set_option maxRecDepth 32768 in
theorem body_shape : func33 = func33.take 163 ++ (func33.drop 163).take 63 ++
    (func33.drop 226).take 28 ++ (func33.drop 254).take 57 ++ (func33.drop 311).take 63 ++
    (func33.drop 374).take 19 ++ (func33.drop 393).take 63 ++ (func33.drop 456).take 28 ++
    (func33.drop 484).take 49 ++ func33.drop 533 := rfl

theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hInputSize : input.size = 3072) (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hWeightsSize : (blocksOffset + layer * blockWords + blockWords) * 4 ≤ weights.size)
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit)
    (hNext : ∀ final result,
      result.values = [.i64 6144, .i64 (cacheNode heap position).root, .i64 (cacheNode heap position).root,
        .i64 3072, .i64 (hiddenNode heap position).root, .i64 (hiddenNode heap position).root] →
      (finalHeap heap position).At final →
      (finalHeap heap position).OwnsPacked final (hiddenNode heap position)
        (cachedBlock weights input cache layer position).hidden →
      (finalHeap heap position).OwnsPacked final (cacheNode heap position)
        (cachedBlock weights input cache layer position).cache →
      heap.Frame initial (finalHeap heap position) final →
      heap.FreshNode (hiddenNode heap position) → heap.FreshNode (cacheNode heap position) →
      regionsDisjoint (hiddenNode heap position).region (cacheNode heap position).region →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      Q (.Fallthrough final result)) :
    wp «module» func33 Q initial frame env := by
  let values := tensors weights input cache layer position
  let params := parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position
  have hSizes : values.Sizes := tensors_sizes weights input cache layer position hInputSize
  have hExtents := weightExtents weights (blocksOffset + layer * blockWords) hWeightsSize
  rw [body_shape]
  simp only [List.append_assoc]
  apply front_spec env initial heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position frame hHeap hWeights hInput hCache hWeightsProtected hInputProtected
    hCacheProtected hLayer hPosition hInputSize hCacheSize hExtents hResources hPages hParams hLocals hValues hTyped
  intro store3 frame3 hFront3 hHeap3 hOwners3 hBindings3 hFrame3 hPages3 hCap3
  let items3 := frontItems heap position values
  have hOwned3 := hOwners3.owned ⟨52, attentionNode heap position, values.mixed⟩ (List.mem_cons_self)
  rcases hFront3.1.1 with ⟨hParams3, hLocals3, hValues3, hBase3, _, _, _, _, _, _, hTyped3⟩
  rcases hFront3.2 with ⟨_, _, _, hCopyOwner3, hCopyPtr3, hCopySize3⟩
  have hResource4 : LayerNorm.AllocationFits (attentionHeap heap position) projectionNeed
      (store3.memoryCap «module» 0) := by
    rw [hCap3]
    exact hResources.projection
  apply projection_spec env store3 (attentionHeap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (attentionNode heap position).root
    weights input cache values.mixed layer position (blocksOffset + layer * blockWords) frame3 hHeap3
    (hFrame3.packed hWeightsProtected hWeights) hOwned3.buffer.values
    (hFrame3.protects _ _ hWeightsProtected) hOwned3.payload_protects hSizes.mixed hExtents.projection
    hResource4 hPages3 hParams3 hLocals3 hValues3 hBase3 hTyped3 hCopyOwner3 hCopyPtr3 hCopySize3
  intro store4 frame4 hState4 hHeap4 hOwned4 hStep4 hPages4 hStepCap4
  have hFrame4 := hFrame3.trans hStep4
  have hCap4 := hStepCap4.trans hCap3
  have hFresh4 : (attentionHeap heap position).FreshNode (projectionNode heap position) :=
    (attentionHeap heap position).freshNode_allocated projectionNeed (fun h => (hResources.projection h).1.le)
  let item4 : PackedReleaseMany.Item := ⟨69, projectionNode heap position, values.projected⟩
  let items4 := item4 :: items3
  have hOwners4 : Owners heap (projectionHeap heap position) store4 items4 :=
    hOwners3.cons hFrame3 hStep4 hHeap4 item4 hOwned4 hFresh4
  have hBindings4 : Bindings items4 frame4 :=
    (hState4.bindings hBindings3 hParams3 hLocals3 (by decide)
      (by simp [frontItems, parameters])).cons item4 (hState4.owner_get (by decide))
  have hFront4 := hState4.preserveAttention (by decide) hFront3
  rcases hState4 with ⟨hParams4, hLocals4, hValues4, hTyped4, hPrefix4,
    hOwner4, hPtr4, hSize4, hCopyOwner4, hCopyPtr4, hCopySize4⟩
  have hBase4 := hFront4.1.1.2.2.2.1
  have hResource5 : LayerNorm.AllocationFits (projectionHeap heap position) projectionNeed
      (store4.memoryCap «module» 0) := by
    rw [hCap4]
    exact hResources.residual
  apply residual_spec env store4 (projectionHeap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (projectionNode heap position).root
    weights input cache values.projected layer position frame4 hHeap4
    (hFrame4.packed hInputProtected hInput) hOwned4.buffer.values
    (hFrame4.protects _ _ hInputProtected) hOwned4.payload_protects hInputSize hSizes.projected
    hResource5 hPages4 hParams4 hLocals4 hValues4 hTyped4 hCopyOwner4 hCopyPtr4 hCopySize4
  intro store5 frame5 hState5 hHeap5 hOwned5 hStep5 hPages5 hStepCap5
  have hFrame5 := hFrame4.trans hStep5
  have hCap5 := hStepCap5.trans hCap4
  have hFresh5 : (projectionHeap heap position).FreshNode (residualNode heap position) :=
    (projectionHeap heap position).freshNode_allocated projectionNeed (fun h => (hResources.residual h).1.le)
  let item5 : PackedReleaseMany.Item := ⟨81, residualNode heap position, values.residual⟩
  let items5 := item5 :: items4
  have hOwners5 : Owners heap (residualHeap heap position) store5 items5 :=
    hOwners4.cons hFrame4 hStep5 hHeap5 item5 hOwned5 hFresh5
  have hBindings5 : Bindings items5 frame5 :=
    (hState5.bindings hBindings4 hParams4 hLocals4 (by decide)
      (by simp [items4, items3, item4, frontItems, parameters])).cons item5 (hState5.owner_get (by decide))
  have hFront5 := hState5.preserveAttention (by decide) hFront4
  rcases hState5 with ⟨hParams5, hLocals5, hValues5, hTyped5, hPrefix5,
    hOwner5, hPtr5, hSize5, hCopyOwner5, hCopyPtr5, hCopySize5⟩
  have hBase5 := hFront5.1.1.2.2.2.1
  have hResource6 : LayerNorm.Resources (residualHeap heap position) 1
      (store5.memoryCap «module» 0) := by
    rw [hCap5]
    exact hResources.normalized2
  apply normalized2_spec env store5 (residualHeap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (residualNode heap position).root
    weights input cache values.residual layer position (blocksOffset + layer * blockWords) frame5 hHeap5
    (hFrame5.packed hWeightsProtected hWeights) hOwned5.buffer.values
    (hFrame5.protects _ _ hWeightsProtected) hOwned5.payload_protects hSizes.residual hExtents.normalized2
    hResource6 hPages5 hParams5 hLocals5 hValues5 hBase5 hTyped5 hCopyOwner5 hCopyPtr5 hCopySize5
  intro store6 frame6 hState6 hHeap6 hOwned6 hStep6 hPages6 hStepCap6
  have hFrame6 := hFrame5.trans hStep6
  have hCap6 := hStepCap6.trans hCap5
  have hFresh6 : (residualHeap heap position).FreshNode (normalized2Node heap position) :=
    LayerNorm.outputNode_fresh hResources.normalized2
  let item6 : PackedReleaseMany.Item := ⟨96, normalized2Node heap position, values.normalized2⟩
  let items6 := item6 :: items5
  have hOwners6 : Owners heap (normalized2Heap heap position) store6 items6 :=
    hOwners5.cons hFrame5 hStep6 hHeap6 item6 hOwned6 hFresh6
  have hBindings6 : Bindings items6 frame6 :=
    (hState6.bindings hBindings5 hParams5 hLocals5 (by decide)
      (by simp [items5, items4, items3, item5, item4, frontItems, parameters])).cons item6 (hState6.owner_get (by decide))
  have hFront6 := hState6.preserveAttention (by decide) hFront5
  rcases hState6 with ⟨hParams6, hLocals6, hValues6, hTyped6, hPrefix6,
    hOwner6, hPtr6, hSize6, hCopyOwner6, hCopyPtr6, hCopySize6⟩
  have hBase6 := hFront6.1.1.2.2.2.1
  have hResource7 : LayerNorm.AllocationFits (normalized2Heap heap position) expandedNeed
      (store6.memoryCap «module» 0) := by
    rw [hCap6]
    exact hResources.expanded
  apply expanded_spec env store6 (normalized2Heap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (normalized2Node heap position).root
    weights input cache values.normalized2 layer position (blocksOffset + layer * blockWords) frame6 hHeap6
    (hFrame6.packed hWeightsProtected hWeights) hOwned6.buffer.values
    (hFrame6.protects _ _ hWeightsProtected) hOwned6.payload_protects hSizes.normalized2 hExtents.expanded
    hResource7 hPages6 hParams6 hLocals6 hValues6 hBase6 hTyped6 hCopyOwner6 hCopyPtr6 hCopySize6
  intro store7 frame7 hState7 hHeap7 hOwned7 hStep7 hPages7 hStepCap7
  have hFrame7 := hFrame6.trans hStep7
  have hCap7 := hStepCap7.trans hCap6
  have hFresh7 : (normalized2Heap heap position).FreshNode (expandedNode heap position) :=
    (normalized2Heap heap position).freshNode_allocated expandedNeed (fun h => (hResources.expanded h).1.le)
  let item7 : PackedReleaseMany.Item := ⟨113, expandedNode heap position, values.expanded⟩
  let items7 := item7 :: items6
  have hOwners7 : Owners heap (expandedHeap heap position) store7 items7 :=
    hOwners6.cons hFrame6 hStep7 hHeap7 item7 hOwned7 hFresh7
  have hBindings7 : Bindings items7 frame7 :=
    (hState7.bindings hBindings6 hParams6 hLocals6 (by decide)
      (by simp [items6, items5, items4, items3, item6, item5, item4, frontItems, parameters])).cons item7 (hState7.owner_get (by decide))
  have hFront7 := hState7.preserveAttention (by decide) hFront6
  rcases hState7 with ⟨hParams7, hLocals7, hValues7, hTyped7, hPrefix7,
    hOwner7, hPtr7, hSize7, hCopyOwner7, hCopyPtr7, hCopySize7⟩
  have hBase7 := hFront7.1.1.2.2.2.1
  have hResource8 : LayerNorm.AllocationFits (expandedHeap heap position) expandedNeed
      (store7.memoryCap «module» 0) := by
    rw [hCap7]
    exact hResources.activated
  apply activated_spec env store7 (expandedHeap heap position) params (expandedNode heap position).root
    values.expanded frame7 hHeap7 hOwned7.buffer.values hOwned7.payload_protects hSizes.expanded
    hResource8 hPages7 hParams7 rfl hLocals7 hValues7 hTyped7 hCopyOwner7 hCopyPtr7 hCopySize7
  intro store8 frame8 hState8 hHeap8 hOwned8 hStep8 hPages8 hStepCap8
  have hFrame8 := hFrame7.trans hStep8
  have hCap8 := hStepCap8.trans hCap7
  have hFresh8 : (expandedHeap heap position).FreshNode (activatedNode heap position) :=
    (expandedHeap heap position).freshNode_allocated expandedNeed (fun h => (hResources.activated h).1.le)
  let item8 : PackedReleaseMany.Item := ⟨122, activatedNode heap position, values.activated⟩
  let items8 := item8 :: items7
  have hOwners8 : Owners heap (activatedHeap heap position) store8 items8 :=
    hOwners7.cons hFrame7 hStep8 hHeap8 item8 hOwned8 hFresh8
  have hBindings8 : Bindings items8 frame8 :=
    (hState8.bindings hBindings7 hParams7 hLocals7 (by decide)
      (by simp [items7, items6, items5, items4, items3, item7, item6, item5, item4, frontItems, params, parameters])).cons item8 (hState8.owner_get (by decide))
  have hFront8 := hState8.preserveAttention (by decide) hFront7
  rcases hState8 with ⟨hParams8, hLocals8, hValues8, hTyped8, hPrefix8,
    hOwner8, hPtr8, hSize8, hCopyOwner8, hCopyPtr8, hCopySize8⟩
  have hBase8 := hFront8.1.1.2.2.2.1
  have hResource9 : LayerNorm.AllocationFits (activatedHeap heap position) projected2Need
      (store8.memoryCap «module» 0) := by
    rw [hCap8]
    exact hResources.projected2
  apply projected2_spec env store8 (activatedHeap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (activatedNode heap position).root
    weights input cache values.activated layer position (blocksOffset + layer * blockWords) frame8 hHeap8
    (hFrame8.packed hWeightsProtected hWeights) hOwned8.buffer.values
    (hFrame8.protects _ _ hWeightsProtected) hOwned8.payload_protects hSizes.activated hExtents.projected2
    hResource9 hPages8 hParams8 hLocals8 hValues8 hBase8 hTyped8 hCopyOwner8 hCopyPtr8 hCopySize8
  intro store9 frame9 hState9 hHeap9 hOwned9 hStep9 hPages9 hStepCap9
  have hFrame9 := hFrame8.trans hStep9
  have hCap9 := hStepCap9.trans hCap8
  have hFresh9 : (activatedHeap heap position).FreshNode (projected2Node heap position) :=
    (activatedHeap heap position).freshNode_allocated projected2Need (fun h => (hResources.projected2 h).1.le)
  let item9 : PackedReleaseMany.Item := ⟨139, projected2Node heap position, values.projected2⟩
  let items9 := item9 :: items8
  have hOwners9 : Owners heap (projected2Heap heap position) store9 items9 :=
    hOwners8.cons hFrame8 hStep9 hHeap9 item9 hOwned9 hFresh9
  have hBindings9 : Bindings items9 frame9 :=
    (hState9.bindings hBindings8 hParams8 hLocals8 (by decide)
      (by simp [items8, items7, items6, items5, items4, items3, item8, item7, item6, item5, item4, frontItems, parameters])).cons item9 (hState9.owner_get (by decide))
  have hFront9 := hState9.preserveAttention (by decide) hFront8
  rcases hState9 with ⟨hParams9, hLocals9, hValues9, hTyped9, hPrefix9,
    hOwner9, hPtr9, hSize9, hCopyOwner9, hCopyPtr9, hCopySize9⟩
  have hBase9 := hFront9.1.1.2.2.2.1
  have hResidual9 := hOwners9.owned ⟨81, residualNode heap position, values.residual⟩
    (by simp [items9, items8, items7, items6, items5, item5])
  have hResource10 : LayerNorm.AllocationFits (projected2Heap heap position) projectionNeed
      (store9.memoryCap «module» 0) := by rw [hCap9]; exact hResources.hidden
  have residualRead (index : Nat) (hi : index < 76) : frame9.locals[index]? = frame5.locals[index]? :=
    (Frame.local_of_take_eq hPrefix9 (by omega)).trans
      ((Frame.local_of_take_eq hPrefix8 (by omega)).trans
        ((Frame.local_of_take_eq hPrefix7 (by omega)).trans (Frame.local_of_take_eq hPrefix6 hi)))
  apply hidden_spec env store9 (projected2Heap heap position) params
    (residualNode heap position).root (projected2Node heap position).root values.residual values.projected2 frame9
    hHeap9 hResidual9.buffer.values hOwned9.buffer.values hResidual9.payload_protects hOwned9.payload_protects
    hSizes.residual hSizes.projected2 hResource10 hPages9 hParams9 rfl hLocals9 hValues9 hTyped9
    ((residualRead 73 (by decide)).trans hCopyOwner5) ((residualRead 74 (by decide)).trans hCopyPtr5)
    ((residualRead 75 (by decide)).trans hCopySize5) hCopyOwner9 hCopyPtr9 hCopySize9
  intro store10 frame10 hState10 hHeap10 hOwned10 hStep10 hPages10 hStepCap10
  have hFrame10 := hFrame9.trans hStep10
  have hCap10 := hStepCap10.trans hCap9
  have hFresh10 := (projected2Heap heap position).freshNode_allocated projectionNeed
    (fun h => (hResources.hidden h).1.le)
  have hHiddenSep := hOwners9.disjoint_fresh hOwned10 hFresh10
  have hOwners10 := hOwners9.frame hStep10 hHeap10
  have hBindings10 : Bindings items9 frame10 :=
    hState10.bindings hBindings9 hParams9 hLocals9 (by decide)
      (by simp [items9, items8, items7, items6, items5, items4, items3,
        item9, item8, item7, item6, item5, item4, frontItems, params, parameters])
  have hFront10 := hState10.preserveAttention (by decide) hFront9
  rcases hState10 with ⟨hParams10, hLocals10, hValues10, hTyped10, hPrefix10,
    hOwner10, hPtr10, hSize10, hCopyOwner10, hCopyPtr10, hCopySize10⟩
  have hQkv10 := hOwners10.owned ⟨38, qkvNode heap, values.qkv⟩
    (by simp [items9, items8, items7, items6, items5, items4, items3, frontItems])
  have hResource11 : LayerNorm.AllocationFits (hiddenHeap heap position) cacheNeed
      (store10.memoryCap «module» 0) := by rw [hCap10]; exact hResources.cache
  rcases hFront10.1.2 with ⟨_, _, _, hQkvOwner10, hQkvPtr10, hQkvBytes10⟩
  apply cache_spec env store10 (hiddenHeap heap position) params (qkvNode heap).root (qkvNode heap).root
    (hiddenNode heap position).root values.qkv frame10 hHeap10 hQkv10.buffer.values
    (by rw [hSizes.qkv]) hQkv10.payload_protects hResource11 hPages10 rfl
    ⟨hParams10, hLocals10, hValues10, hQkvOwner10, hQkvPtr10, by rw [hSizes.qkv]; exact hQkvBytes10,
      hCopyOwner10, hCopyPtr10, hCopySize10, hTyped10⟩
  intro store11 frame11 hState11 hOutput11
  have hFrame11 := hFrame10.trans hOutput11.frame
  have hOwners11 := hOwners10.frame hOutput11.frame hOutput11.heapAt
  have hHidden11 := hOutput11.frame.ownsPacked hOutput11.heapAt hOwned10
  have hFresh11 := (hiddenHeap heap position).freshNode_allocated cacheNeed
    (fun h => (hResources.cache h).1.le)
  have hCacheSep := hOwners10.disjoint_fresh hOutput11.owned hFresh11
  have hOutputSep := hOwned10.allocation_disjoint cacheNeed (fun h => (hResources.cache h).1.le)
  rcases hState11 with ⟨⟨hParams11, hLocals11, hValues11, _, _, _, hHiddenOwner11, hHiddenPtr11,
    hHiddenBytes11, _⟩, hCacheOwner11, hCachePtr11, hCacheBytes11, hPrefix11⟩
  have hBindings11 : Bindings items9 frame11 :=
    hBindings10.prefix (hParams11.trans hParams10.symm) hPrefix11
      (by rw [hLocals10]; decide) (by rw [hLocals11]; decide)
      (by simp [hParams10, params, parameters, items9, items8, items7, items6, items5, items4, items3,
        item9, item8, item7, item6, item5, item4, frontItems])
  rw [← List.append_nil (func33.drop 533)]
  apply cleanup_spec env store11 (cacheHeap heap position) heap initial frame11 items9
    (hiddenNode heap position) (cacheNode heap position) values.hidden (cacheUpdate values.qkv)
    rfl hOutput11.heapAt hOwners11.owned hHidden11 hOutput11.owned hOwners11.disjoint hHiddenSep hCacheSep
    hFrame11 hOwners11.fresh hValues11 hBindings11
  · simpa only [Locals.get, hParams11, params, parameters, hLocals11,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using hHiddenOwner11
  · simpa only [Locals.get, hParams11, params, parameters, hLocals11,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using hHiddenPtr11
  · simpa only [Locals.get, hParams11, params, parameters, hLocals11,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using hHiddenBytes11
  · simpa only [cacheNode, allocatedNode, Locals.get, hParams11, params, parameters, hLocals11,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using hCacheOwner11
  · simpa only [cacheNode, allocatedNode, Locals.get, hParams11, params, parameters, hLocals11,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using hCachePtr11
  · simpa only [Locals.get, hParams11, params, parameters, hLocals11,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using hCacheBytes11
  intro result hFinalHeap hFinalHidden hFinalCache hFinalFrame hFinalValues
  simp only [wp_nil]
  apply hNext _ result hFinalValues hFinalHeap
  · rw [cachedBlock_tensors]
    exact hFinalHidden
  · rw [cachedBlock_tensors]
    exact hFinalCache
  · exact hFinalFrame
  · exact hFrame9.freshNode hFresh10
  · exact hFrame10.freshNode hFresh11
  · exact hOutputSep
  · rw [PackedReleaseMany.finalStore_pages]
    exact hOutput11.pages
  · rw [PackedReleaseMany.finalStore_memoryCap]
    exact (hOutput11.memoryCap «module» 0).trans hCap10

#print axioms body_spec

end Project.Gpt2CachedStep.CachedBlock
