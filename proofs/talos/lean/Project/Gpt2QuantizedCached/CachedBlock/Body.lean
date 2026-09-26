import Project.Gpt2QuantizedCached.CachedBlock.Front

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open PackedReleaseMany (Owners Bindings)

def executionHeap (heap : Heap) (position : Nat) (values : Tensors) : Heap :=
  (if finiteWords values.normalized 0 768 then frontHeap heap position values
    else normalizedHeap heap).release (normalizedNode heap)

def resultValues (accepted : Bool) (hidden cache : UInt64) : List Value :=
  [.i64 (if accepted then 6144 else 0), .i64 (if accepted then cache else 0),
   .i64 (if accepted then cache else 0), .i64 (if accepted then 3072 else 0),
   .i64 (if accepted then hidden else 0), .i64 (if accepted then hidden else 0),
   .i64 (if accepted then 0 else 4)]

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
    (hExtent : blocksOffset + layer * blockBytes + blockBytes ≤ weights.size)
    (hInputSize : input.size = 3072) (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position)
    (hLength : frame.locals.length = 193) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit)
    (hNext : ∀ final result,
      result.values = resultValues (tensors weights input cache layer position).accepted
        (hiddenNode heap position).root (cacheNode heap position).root →
      Completion heap initial (executionHeap heap position (tensors weights input cache layer position)) final
        (tensors weights input cache layer position).accepted
        (hiddenNode heap position) (cacheNode heap position)
        (tensors weights input cache layer position).hidden
        (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (tensors weights input cache layer position).qkv) →
      Q (.Fallthrough final result)) :
    wp «module» func54 Q initial frame env := by
  let values := tensors weights input cache layer position
  let params := parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position
  have hSizes : values.Sizes := tensors_sizes weights input cache layer position hInputSize
  have hNormalizedExtent : ((blocksOffset + layer * blockBytes) / 4 + 1536) * 4 ≤ weights.size := by
    have := Nat.div_mul_le_self (blocksOffset + layer * blockBytes) 4
    have : 6144 ≤ blockBytes := by decide
    omega
  have hResource1 : Gpt2CachedStep.LayerNorm.Resources heap 1
      (initial.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [← memoryCap_eq_fp32]
    exact hResources.normalized
  rw [block_shape]
  simp only [List.append_assoc]
  apply base_spec env initial frame layer (by rw [hParams]; rfl) hLength hValues
    (by rw [hParams]; rfl) hLayer
  apply normalized_spec env initial heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position (blocksOffset + layer * blockBytes) (baseFrame frame layer)
    hHeap hWeights hInput hWeightsProtected hInputProtected (by rw [hInputSize]) hNormalizedExtent
    hResource1 hPages hParams
  · simpa only [baseFrame, List.length_set] using hLength
  · rfl
  · simp only [baseFrame, List.getElem?_set, hLength, List.length_set, Nat.reduceLT, reduceIte]
  · simp (config := { maxDischargeDepth := 16 }) only [baseFrame, I64Values.set, hTyped]
  intro store1 frame1 hState1 hHeap1 hOwned1 hFrame1 hPages1 hStepCap1
  have hCap1 : store1.memoryCap «module» 0 = initial.memoryCap «module» 0 := by
    simpa only [memoryCap_eq_fp32] using hStepCap1
  let item1 : PackedReleaseMany.Item := ⟨21, normalizedNode heap, values.normalized⟩
  have hOwners1 : Owners heap (normalizedHeap heap) store1 [item1] :=
    (Owners.nil heap heap initial).cons (Heap.Frame.refl _ _) hFrame1 hHeap1 item1 hOwned1
      (Gpt2CachedStep.LayerNorm.outputNode_fresh hResources.normalized)
  have hNormalizedState := hState1
  rcases hState1 with ⟨hParams1, hLength1, hValues1, _, hOwner1, _, _,
    hCopyOwner1, hCopyPtr1, hCopySize1, hTyped1⟩
  have hBindings1 : Bindings [item1] frame1 := by
    intro item hItem
    have : item = item1 := by simpa only [List.mem_singleton] using hItem
    subst item
    simpa only [item1, normalizedNode, Locals.get, hParams1, parameters, List.length_cons, List.length_nil,
      hLength1, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, reduceIte] using hOwner1
  have hResources1 : Resources heap position (store1.memoryCap «module» 0) := by rw [hCap1]; exact hResources
  apply guardedRelease_spec env heap (normalizedHeap heap) (frontHeap heap position values)
    initial store1 params frame1 [item1] (hiddenNode heap position) (cacheNode heap position)
    values.hidden (Project.Gpt2CachedStep.CachedBlock.cacheUpdate values.qkv)
    (normalizedNode heap).root (normalizedNode heap).root values.normalized 768 13
    normalizedSuccess (frontAccepted values) hHeap1 hFrame1 hPages1 hCap1 hOwners1 hBindings1
    (by simp [item1]) hOwned1.buffer.values (by rw [hSizes.normalized]) (by simp)
    hParams1 rfl hLength1 hValues1 hCopyOwner1 hCopyPtr1
    (by rw [hSizes.normalized]; exact hCopySize1) hTyped1
  · intro prepared hPreparedParams hPreparedLength hPreparedTyped hPreparedPrefix hPreparedValues R hDone
    rw [← List.append_nil normalizedSuccess]
    apply front_spec env store1 heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position prepared hHeap1 (hFrame1.packed hWeightsProtected hWeights)
      (hFrame1.packed hInputProtected hInput) (hFrame1.packed hCacheProtected hCache)
      (hFrame1.protects _ _ hWeightsProtected) (hFrame1.protects _ _ hInputProtected)
      (hFrame1.protects _ _ hCacheProtected) hOwned1 hLayer hPosition hExtent hInputSize hCacheSize
      hResources1 hPages1
      (hNormalizedState.transfer hPreparedParams hPreparedLength hPreparedValues hPreparedTyped hPreparedPrefix (by decide))
    intro final result hResult hOutput
    simp only [wp_nil]
    apply hDone final result (hResult.narrow (by decide : 16 ≤ 21) ?_) hOutput
    simpa only [List.take_take, show min 16 21 = 16 from rfl] using hPreparedPrefix
  · intro final result hResult hOutput
    have hAccepted : (finiteWords values.normalized 0 768 && frontAccepted values) = values.accepted := by
      simp only [frontAccepted, postAttentionAccepted, Tensors.accepted, Bool.and_assoc]
    rw [hAccepted] at hResult hOutput
    simp only [returnCode]
    wp_packed_frame [hResult.paramsEq, params, parameters, hResult.length, hResult.values,
      hResult.status, hResult.hiddenOwner, hResult.hiddenPtr, hResult.hiddenSize,
      hResult.cacheOwner, hResult.cachePtr, hResult.cacheSize]
    exact hNext _ _ rfl hOutput

#print axioms body_spec
end Project.Gpt2QuantizedCached.CachedBlock
