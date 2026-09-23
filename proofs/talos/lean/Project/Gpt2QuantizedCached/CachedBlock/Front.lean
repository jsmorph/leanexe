import Project.Gpt2QuantizedCached.CachedBlock.PostAttention

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open PackedReleaseMany (Owners Bindings)

def frontAccepted (values : Tensors) : Bool :=
  finiteWords values.mixed 0 768 && postAttentionAccepted values

def frontHeap (heap : Heap) (position : Nat) (values : Tensors) : Heap :=
  ((if finiteWords values.mixed 0 768 then postAttentionHeap heap position values
    else attentionHeap heap position).release (attentionNode heap position)).release (qkvNode heap)

theorem front_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat) (frame : Locals)
    (hHeap : (normalizedHeap heap).At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : (normalizedHeap heap).Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : (normalizedHeap heap).Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCacheProtected : (normalizedHeap heap).Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hNormalized : (normalizedHeap heap).OwnsPacked initial (normalizedNode heap)
      (tensors weights input cache layer position).normalized)
    (hLayer : layer < 12) (hPosition : position < 128)
    (hExtent : blocksOffset + layer * blockBytes + blockBytes ≤ weights.size)
    (hInputSize : input.size = 3072) (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : NormalizedState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position) (blocksOffset + layer * blockBytes) (normalizedNode heap).root frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      ResultState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 21) 21
        (frontAccepted (tensors weights input cache layer position))
        (hiddenNode heap position).root (cacheNode heap position).root result →
      Completion (normalizedHeap heap) initial
        (frontHeap heap position (tensors weights input cache layer position)) final
        (frontAccepted (tensors weights input cache layer position))
        (hiddenNode heap position) (cacheNode heap position)
        (tensors weights input cache layer position).hidden
        (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (tensors weights input cache layer position).qkv) →
      wp «module» rest Q final result env) :
    wp «module» (normalizedSuccess ++ rest) Q initial frame env := by
  let values := tensors weights input cache layer position
  let params := parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position
  have hSizes : values.Sizes := tensors_sizes weights input cache layer position hInputSize
  rw [normalizedSuccess_shape]
  simp only [List.append_assoc]
  apply qkv_spec env initial (normalizedHeap heap)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (normalizedNode heap).root
    weights input cache values.normalized layer position (blocksOffset + layer * blockBytes) frame
    hHeap hWeights hNormalized.buffer.values hWeightsProtected hNormalized.payload_protects
    hSizes.normalized hExtent hResources.qkv hPages hState
  intro store2 frame2 hState2 hPrefix2 hOutput2
  let item2 : PackedReleaseMany.Item := ⟨45, qkvNode heap, values.qkv⟩
  have hOwners2 : Owners (normalizedHeap heap) (qkvHeap heap) store2 [item2] :=
    (Owners.nil (normalizedHeap heap) (normalizedHeap heap) initial).cons
      (Heap.Frame.refl _ _) hOutput2.frame hOutput2.heapAt item2 hOutput2.owned
      (GroupedProjection.Projection.outputNode_fresh hResources.qkv)
  have hResource3 : Gpt2CachedStep.CachedAttention.Resources (qkvHeap heap) position
      (store2.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [← memoryCap_eq_fp32, hOutput2.memoryCap]
    exact hResources.attention
  apply attention_spec env store2 (qkvHeap heap)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (normalizedNode heap).root (qkvNode heap).root
    weights input cache values.qkv layer position (blocksOffset + layer * blockBytes) frame2 hOutput2.heapAt
    (hOutput2.frame.packed hCacheProtected hCache) hOutput2.owned.buffer.values
    (hOutput2.frame.protects _ _ hCacheProtected) hOutput2.owned.payload_protects hLayer hPosition
    hCacheSize hSizes.qkv hResource3 hOutput2.pages hState2
  intro store3 frame3 hState3 hPrefix3 hHeap3 hOwned3 hStep3 hPages3 hStepCap3
  have hFrame3 := hOutput2.frame.trans hStep3
  have hCap3 : store3.memoryCap «module» 0 = initial.memoryCap «module» 0 := by
    rw [memoryCap_eq_fp32, hStepCap3, ← memoryCap_eq_fp32, hOutput2.memoryCap]
  let item3 : PackedReleaseMany.Item := ⟨59, attentionNode heap position, values.mixed⟩
  have hOwners3 : Owners (normalizedHeap heap) (attentionHeap heap position) store3 [item3, item2] :=
    hOwners2.cons hOutput2.frame hStep3 hHeap3 item3 hOwned3
      (Gpt2CachedStep.CachedAttention.outputNode_fresh hResources.attention)
  rcases hState3 with ⟨⟨⟨hParams3, hLength3, hValues3, hBase3, _, _, _, _, _, _, hTyped3⟩,
    hQkvOwner3, _, _, hQkvCopyOwner3, hQkvCopyPtr3, hQkvCopySize3⟩,
    hMixedOwner3, _, _, hCopyOwner3, hCopyPtr3, hCopySize3⟩
  have hBindings3 : Bindings [item3, item2] frame3 := by
    intro item hItem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hItem
    rcases hItem with rfl | rfl <;>
      simp only [item3, item2, Locals.get, hParams3, parameters, List.length_cons, List.length_nil,
        hLength3, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] <;> assumption
  have hResources3 : Resources heap position (store3.memoryCap «module» 0) := by rw [hCap3]; exact hResources
  apply guardedRelease_spec env (normalizedHeap heap) (attentionHeap heap position)
    (postAttentionHeap heap position values) initial store3 params frame3 [item3, item2]
    (hiddenNode heap position) (cacheNode heap position) values.hidden
    (Project.Gpt2CachedStep.CachedBlock.cacheUpdate values.qkv)
    (attentionNode heap position).root (attentionNode heap position).root values.mixed 768 51
    attentionSuccess (postAttentionAccepted values)
    hHeap3 hFrame3 hPages3 hCap3 hOwners3 hBindings3 (by simp [item3, item2]) hOwned3.buffer.values
    (by rw [hSizes.mixed]) (by simp) hParams3 rfl hLength3 hValues3 hCopyOwner3 hCopyPtr3
    (by rw [hSizes.mixed]; exact hCopySize3) hTyped3
  · intro prepared hPreparedParams hPreparedLength hPreparedTyped hPreparedPrefix hPreparedValues R hDone
    have readPrepared (index : Nat) (hi : index < 54) : prepared.locals[index]? = frame3.locals[index]? :=
      Frame.local_of_take_eq hPreparedPrefix hi
    rw [← List.append_nil attentionSuccess]
    apply postAttention_spec env store3 heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position prepared hHeap3 (hFrame3.packed hWeightsProtected hWeights)
      (hFrame3.packed hInputProtected hInput) (hFrame3.protects _ _ hWeightsProtected)
      (hFrame3.protects _ _ hInputProtected) (hStep3.ownsPacked hHeap3 hOutput2.owned)
      hOwned3 hExtent hInputSize hResources3 hPages3
      (hPreparedParams.trans hParams3) hPreparedLength hPreparedValues hPreparedTyped
      ((readPrepared 0 (by decide)).trans hBase3)
      ((readPrepared 37 (by decide)).trans hQkvCopyOwner3) ((readPrepared 38 (by decide)).trans hQkvCopyPtr3)
      ((readPrepared 39 (by decide)).trans hQkvCopySize3) ((readPrepared 51 (by decide)).trans hCopyOwner3)
      ((readPrepared 52 (by decide)).trans hCopyPtr3) ((readPrepared 53 (by decide)).trans hCopySize3)
    intro final result hResult hOutput
    simp only [wp_nil]
    apply hDone final result (hResult.narrow (by decide : 54 ≤ 59) ?_) hOutput
    simpa only [List.take_take, show min 54 59 = 54 from rfl] using hPreparedPrefix
  · intro final result hResult hOutput
    apply hNext final result (hResult.narrow (by decide : 21 ≤ 54) ?_) hOutput
    have h3 := congrArg (List.take 21) hPrefix3
    simp only [List.take_take, show min 21 40 = 21 from rfl] at h3
    simpa only [List.take_take, show min 21 54 = 21 from rfl] using h3.trans hPrefix2

#print axioms front_spec
end Project.Gpt2QuantizedCached.CachedBlock
