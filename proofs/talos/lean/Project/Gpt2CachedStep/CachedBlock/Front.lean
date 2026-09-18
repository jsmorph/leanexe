import Project.Gpt2CachedStep.CachedBlock.Resources

namespace Project.Gpt2CachedStep.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2
open PackedReleaseMany (Owners Bindings)

def frontItems (heap : Heap) (position : Nat) (values : Tensors) : List PackedReleaseMany.Item :=
  [⟨52, attentionNode heap position, values.mixed⟩,
   ⟨38, qkvNode heap, values.qkv⟩,
   ⟨21, normalizedNode heap, values.normalized⟩]

set_option maxRecDepth 32768 in
theorem front_shape : func33.take 163 = func33.take 19 ++ (func33.drop 19).take 47 ++
    (func33.drop 66).take 63 ++ (func33.drop 129).take 34 := rfl

theorem front_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
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
    (hExtents : WeightExtents weights (blocksOffset + layer * blockWords))
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLocals : frame.locals.length = 164) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      AttentionState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (blocksOffset + layer * blockWords)
        (normalizedNode heap).root (qkvNode heap).root (attentionNode heap position).root result →
      (attentionHeap heap position).At final →
      Owners heap (attentionHeap heap position) final
        (frontItems heap position (tensors weights input cache layer position)) →
      Bindings (frontItems heap position (tensors weights input cache layer position)) result →
      heap.Frame initial (attentionHeap heap position) final →
      final.mem.pages ≤ 65536 → final.memoryCap «module» 0 = initial.memoryCap «module» 0 →
      wp «module» rest Q final result env) :
    wp «module» (func33.take 163 ++ rest) Q initial frame env := by
  let values := tensors weights input cache layer position
  have hSizes := tensors_sizes weights input cache layer position hInputSize
  rw [front_shape]
  simp only [List.append_assoc]
  apply base_spec env initial frame layer (by rw [hParams]; rfl) hLocals hValues
    (by rw [hParams]; rfl) hLayer
  apply normalized_spec env initial heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position (blocksOffset + layer * blockWords) (baseFrame frame layer)
    hHeap hWeights hInput hWeightsProtected hInputProtected (by rw [hInputSize]) hExtents.normalized
    hResources.normalized hPages hParams
  · simpa only [baseFrame, List.length_set] using hLocals
  · rfl
  · simp only [baseFrame, List.getElem?_set, hLocals, List.length_set, Nat.reduceLT, reduceIte]
  · simp (config := { maxDischargeDepth := 16 }) only [baseFrame, I64Values.set, hTyped]
  intro first firstFrame hFirstState hFirstHeap hFirstOwned hFirstFrame hFirstPages hFirstCap
  let firstItem : PackedReleaseMany.Item := ⟨21, normalizedNode heap, values.normalized⟩
  have hFirstOwners : Owners heap (normalizedHeap heap) first [firstItem] :=
    (Owners.nil heap heap initial).cons (Heap.Frame.refl heap initial) hFirstFrame hFirstHeap firstItem
      hFirstOwned (LayerNorm.outputNode_fresh hResources.normalized)
  have hQkvResource : LayerNorm.AllocationFits (normalizedHeap heap) qkvNeed (first.memoryCap «module» 0) := by
    rw [hFirstCap]
    exact hResources.qkv
  apply qkv_spec env first (normalizedHeap heap) weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    (normalizedNode heap).root weights input cache values.normalized layer position (blocksOffset + layer * blockWords)
    firstFrame hFirstHeap (hFirstFrame.packed hWeightsProtected hWeights) hFirstOwned.buffer.values
    (hFirstFrame.protects _ _ hWeightsProtected) hFirstOwned.payload_protects hSizes.normalized
    hExtents.qkv hQkvResource hFirstPages hFirstState
  intro second secondFrame hSecondState hSecondHeap hSecondOwned hSecondFrame hSecondPages hSecondCap
  have hFrameSecond := hFirstFrame.trans hSecondFrame
  let secondItem : PackedReleaseMany.Item := ⟨38, qkvNode heap, values.qkv⟩
  have hSecondOwners : Owners heap (qkvHeap heap) second [secondItem, firstItem] :=
    hFirstOwners.cons hFirstFrame hSecondFrame hSecondHeap secondItem hSecondOwned
      ((normalizedHeap heap).freshNode_allocated qkvNeed (fun h => (hResources.qkv h).1.le))
  have hAttentionResource : CachedAttention.Resources (qkvHeap heap) position (second.memoryCap «module» 0) := by
    rw [hSecondCap, hFirstCap]
    exact hResources.attention
  apply attention_spec env second (qkvHeap heap) weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    (normalizedNode heap).root (qkvNode heap).root weights input cache values.qkv layer position
    (blocksOffset + layer * blockWords) secondFrame hSecondHeap (hFrameSecond.packed hCacheProtected hCache)
    hSecondOwned.buffer.values (hFrameSecond.protects _ _ hCacheProtected) hSecondOwned.payload_protects
    hLayer hPosition hCacheSize hSizes.qkv hAttentionResource hSecondPages hSecondState
  intro third thirdFrame hThirdState hThirdHeap hThirdOwned hThirdFrame hThirdPages hThirdCap
  have hThirdOwners : Owners heap (attentionHeap heap position) third (frontItems heap position values) :=
    hSecondOwners.cons hFrameSecond hThirdFrame hThirdHeap
      ⟨52, attentionNode heap position, values.mixed⟩ hThirdOwned
      (CachedAttention.outputNode_fresh hResources.attention)
  apply hNext third thirdFrame hThirdState hThirdHeap hThirdOwners
  · rcases hThirdState with ⟨⟨⟨hParams, hLocals, _, _, hNormalized, _⟩, hQkv, _⟩, hAttention, _⟩
    intro item hItem
    simp only [frontItems, List.mem_cons, List.not_mem_nil, or_false] at hItem
    rcases hItem with rfl | rfl | rfl <;>
      simp only [Locals.get, hParams, parameters, List.length_cons, List.length_nil,
        hLocals, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] <;> assumption
  · exact hFrameSecond.trans hThirdFrame
  · exact hThirdPages
  · exact hThirdCap.trans (hSecondCap.trans hFirstCap)

#print axioms front_spec

end Project.Gpt2CachedStep.CachedBlock
