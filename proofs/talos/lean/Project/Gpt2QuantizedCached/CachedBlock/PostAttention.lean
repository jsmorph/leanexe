import Project.Gpt2QuantizedCached.CachedBlock.FeedForward

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open PackedReleaseMany (Owners Bindings)

def postAttentionAccepted (values : Tensors) : Bool :=
  finiteWords values.normalized2 0 768 && finiteWords values.activated 0 3072

def postAttentionHeap (heap : Heap) (position : Nat) (values : Tensors) : Heap :=
  (((if finiteWords values.normalized2 0 768 then feedForwardHeap heap position values
    else normalized2Heap heap position).release (normalized2Node heap position)).release
    (residualNode heap position)).release (projectionNode heap position)

theorem postAttention_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat) (frame : Locals)
    (hHeap : (attentionHeap heap position).At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hWeightsProtected : (attentionHeap heap position).Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : (attentionHeap heap position).Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hQkv : (attentionHeap heap position).OwnsPacked initial (qkvNode heap)
      (tensors weights input cache layer position).qkv)
    (hMixed : (attentionHeap heap position).OwnsPacked initial (attentionNode heap position)
      (tensors weights input cache layer position).mixed)
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
    (hMixedOwner : frame.locals[51]? = some (.i64 (attentionNode heap position).root))
    (hMixedPtr : frame.locals[52]? = some (.i64 (attentionNode heap position).root))
    (hMixedSize : frame.locals[53]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      ResultState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 59) 59
        (postAttentionAccepted (tensors weights input cache layer position))
        (hiddenNode heap position).root (cacheNode heap position).root result →
      Completion (attentionHeap heap position) initial
        (postAttentionHeap heap position (tensors weights input cache layer position)) final
        (postAttentionAccepted (tensors weights input cache layer position))
        (hiddenNode heap position) (cacheNode heap position)
        (tensors weights input cache layer position).hidden
        (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (tensors weights input cache layer position).qkv) →
      wp «module» rest Q final result env) :
    wp «module» (attentionSuccess ++ rest) Q initial frame env := by
  let values := tensors weights input cache layer position
  let params := parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position
  have hSizes : values.Sizes := tensors_sizes weights input cache layer position hInputSize
  rw [attentionSuccess_shape]
  simp only [List.append_assoc]
  apply projection_spec env initial (attentionHeap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (attentionNode heap position).root
    weights input cache values.mixed layer position (blocksOffset + layer * blockBytes) frame
    hHeap hWeights hMixed.buffer.values hWeightsProtected hMixed.payload_protects
    hSizes.mixed hExtent hResources.projection hPages hParams hLength hValues hBase hTyped
    hMixedOwner hMixedPtr hMixedSize
  intro store4 frame4 hState4 hOutput4
  let item4 : PackedReleaseMany.Item := ⟨83, projectionNode heap position, values.projected⟩
  have hOwners4 : Owners (attentionHeap heap position) (projectionHeap heap position) store4 [item4] :=
    (Owners.nil (attentionHeap heap position) (attentionHeap heap position) initial).cons
      (Heap.Frame.refl _ _) hOutput4.frame hOutput4.heapAt item4 hOutput4.owned
      (GroupedProjection.Projection.outputNode_fresh hResources.projection)
  have hBindings4 : Bindings [item4] frame4 :=
    (by simp only [Bindings, List.not_mem_nil, false_implies, implies_true] : Bindings [] frame4).cons
      item4 (hState4.owner_get (by decide))
  rcases hState4 with ⟨hParams4, hLength4, hValues4, hTyped4, hPrefix4,
    hOwner4, hPtr4, hSize4, hCopyOwner4, hCopyPtr4, hCopySize4⟩
  have hResource5 : Gpt2CachedStep.LayerNorm.AllocationFits (projectionHeap heap position)
      residualNeed (store4.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [← memoryCap_eq_fp32, hOutput4.memoryCap]
    exact hResources.residual
  apply residual_spec env store4 (projectionHeap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (projectionNode heap position).root
    weights input cache values.projected layer position frame4 hOutput4.heapAt
    (hOutput4.frame.packed hInputProtected hInput) hOutput4.owned.buffer.values
    (hOutput4.frame.protects _ _ hInputProtected) hOutput4.owned.payload_protects hInputSize hSizes.projected
    hResource5 hOutput4.pages hParams4 hLength4 hValues4 hTyped4 hCopyOwner4 hCopyPtr4 hCopySize4
  intro store5 frame5 hState5 hHeap5 hOwned5 hStep5 hPages5 hStepCap5
  have hFrame5 := hOutput4.frame.trans hStep5
  have hCap5 : store5.memoryCap «module» 0 = initial.memoryCap «module» 0 := by
    rw [memoryCap_eq_fp32, hStepCap5, ← memoryCap_eq_fp32, hOutput4.memoryCap]
  let item5 : PackedReleaseMany.Item := ⟨95, residualNode heap position, values.residual⟩
  have hOwners5 : Owners (attentionHeap heap position) (residualHeap heap position) store5 [item5, item4] :=
    hOwners4.cons hOutput4.frame hStep5 hHeap5 item5 hOwned5
      ((projectionHeap heap position).freshNode_allocated residualNeed (fun h => (hResources.residual h).1.le))
  have hBindings5 : Bindings [item5, item4] frame5 :=
    (hState5.bindings hBindings4 hParams4 hLength4 (by decide)
      (by simp [item4, params, parameters])).cons item5 (hState5.owner_get (by decide))
  rcases hState5 with ⟨hParams5, hLength5, hValues5, hTyped5, hPrefix5,
    hOwner5, hPtr5, hSize5, hCopyOwner5, hCopyPtr5, hCopySize5⟩
  have read5 (index : Nat) (hi : index < 59) : frame5.locals[index]? = frame.locals[index]? :=
    (Frame.local_of_take_eq hPrefix5 (by omega)).trans (Frame.local_of_take_eq hPrefix4 hi)
  have hResource6 : Gpt2CachedStep.LayerNorm.Resources (residualHeap heap position) 1
      (store5.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [← memoryCap_eq_fp32, hCap5]
    exact hResources.normalized2
  apply normalized2_spec env store5 (residualHeap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (residualNode heap position).root
    weights input cache values.residual layer position (blocksOffset + layer * blockBytes) frame5 hHeap5
    (hFrame5.packed hWeightsProtected hWeights) hOwned5.buffer.values
    (hFrame5.protects _ _ hWeightsProtected) hOwned5.payload_protects hSizes.residual hExtent
    hResource6 hPages5 hParams5 hLength5 hValues5 ((read5 0 (by decide)).trans hBase)
    hTyped5 hCopyOwner5 hCopyPtr5 hCopySize5
  intro store6 frame6 hState6 hHeap6 hOwned6 hStep6 hPages6 hStepCap6
  have hFrame6 := hFrame5.trans hStep6
  have hCap6 : store6.memoryCap «module» 0 = initial.memoryCap «module» 0 := by
    rw [memoryCap_eq_fp32, hStepCap6, ← memoryCap_eq_fp32, hCap5]
  let item6 : PackedReleaseMany.Item := ⟨110, normalized2Node heap position, values.normalized2⟩
  have hOwners6 : Owners (attentionHeap heap position) (normalized2Heap heap position) store6 [item6, item5, item4] :=
    hOwners5.cons hFrame5 hStep6 hHeap6 item6 hOwned6 (Gpt2CachedStep.LayerNorm.outputNode_fresh hResources.normalized2)
  have hBindings6 : Bindings [item6, item5, item4] frame6 :=
    (hState6.bindings hBindings5 hParams5 hLength5 (by decide)
      (by simp [item5, item4, params, parameters])).cons item6 (hState6.owner_get (by decide))
  rcases hState6 with ⟨hParams6, hLength6, hValues6, hTyped6, hPrefix6,
    hOwner6, hPtr6, hSize6, hCopyOwner6, hCopyPtr6, hCopySize6⟩
  have hResources6 : Resources heap position (store6.memoryCap «module» 0) := by rw [hCap6]; exact hResources
  apply guardedRelease_spec env (attentionHeap heap position) (normalized2Heap heap position)
    (feedForwardHeap heap position values) initial store6 params frame6 [item6, item5, item4]
    (hiddenNode heap position) (cacheNode heap position) values.hidden
    (Project.Gpt2CachedStep.CachedBlock.cacheUpdate values.qkv)
    (normalized2Node heap position).root (normalized2Node heap position).root values.normalized2 768 102
    normalized2Success (finiteWords values.activated 0 3072)
    hHeap6 hFrame6 hPages6 hCap6 hOwners6 hBindings6 (by simp [item6, item5, item4]) hOwned6.buffer.values
    (by rw [hSizes.normalized2]) (by simp) hParams6 rfl hLength6 hValues6 hCopyOwner6 hCopyPtr6
    (by rw [hSizes.normalized2]; exact hCopySize6) hTyped6
  · intro prepared hPreparedParams hPreparedLength hPreparedTyped hPreparedPrefix hPreparedValues R hDone
    have readPrepared (index : Nat) (hi : index < 59) : prepared.locals[index]? = frame.locals[index]? :=
      (Frame.local_of_take_eq hPreparedPrefix (by omega)).trans
        ((Frame.local_of_take_eq hPrefix6 (by omega)).trans (read5 index hi))
    have readResidual (index : Nat) (hi : index < 90) : prepared.locals[index]? = frame5.locals[index]? :=
      (Frame.local_of_take_eq hPreparedPrefix (by omega)).trans (Frame.local_of_take_eq hPrefix6 hi)
    rw [← List.append_nil normalized2Success]
    apply feedForward_spec env store6 heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position prepared hHeap6 (hFrame6.packed hWeightsProtected hWeights)
      (hFrame6.protects _ _ hWeightsProtected) (hFrame6.ownsPacked hHeap6 hQkv)
      (hStep6.ownsPacked hHeap6 hOwned5) hOwned6 hExtent hInputSize hResources6 hPages6
      (hPreparedParams.trans hParams6) hPreparedLength hPreparedValues hPreparedTyped
      ((readPrepared 0 (by decide)).trans hBase)
      ((readPrepared 37 (by decide)).trans hQkvOwner) ((readPrepared 38 (by decide)).trans hQkvPtr)
      ((readPrepared 39 (by decide)).trans hQkvSize) ((readResidual 87 (by decide)).trans hCopyOwner5)
      ((readResidual 88 (by decide)).trans hCopyPtr5) ((readResidual 89 (by decide)).trans hCopySize5)
      ((Frame.local_of_take_eq hPreparedPrefix (by decide : 102 < 102 + 3)).trans hCopyOwner6)
      ((Frame.local_of_take_eq hPreparedPrefix (by decide : 103 < 102 + 3)).trans hCopyPtr6)
      ((Frame.local_of_take_eq hPreparedPrefix (by decide : 104 < 102 + 3)).trans hCopySize6)
    intro final result hResult hOutput
    simp only [wp_nil]
    apply hDone final result (hResult.narrow (by decide : 105 ≤ 110) ?_) hOutput
    simpa only [List.take_take, show min 105 110 = 105 from rfl] using hPreparedPrefix
  · intro final result hResult hOutput
    apply hNext final result (hResult.narrow (by decide : 59 ≤ 105) ?_) hOutput
    have h6 := congrArg (List.take 59) hPrefix6
    have h5 := congrArg (List.take 59) hPrefix5
    simp only [List.take_take, show min 59 90 = 59 from rfl] at h6
    simp only [List.take_take, show min 59 78 = 59 from rfl] at h5
    simpa only [List.take_take, show min 59 105 = 59 from rfl] using h6.trans (h5.trans hPrefix4)

#print axioms postAttention_spec
end Project.Gpt2QuantizedCached.CachedBlock
