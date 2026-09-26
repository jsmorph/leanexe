import Project.Gpt2QuantizedCached.CachedBlock.Tail
import Project.Gpt2QuantizedCached.CachedBlock.GuardedRelease

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open PackedReleaseMany (Owners Bindings)

def feedForwardHeap (heap : Heap) (position : Nat) (values : Tensors) : Heap :=
  ((if finiteWords values.activated 0 3072 then tailHeap heap position else activatedHeap heap position).release
    (activatedNode heap position)).release (expandedNode heap position)

theorem feedForward_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat) (frame : Locals)
    (hHeap : (normalized2Heap heap position).At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hWeightsProtected : (normalized2Heap heap position).Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hQkv : (normalized2Heap heap position).OwnsPacked initial (qkvNode heap)
      (tensors weights input cache layer position).qkv)
    (hResidual : (normalized2Heap heap position).OwnsPacked initial (residualNode heap position)
      (tensors weights input cache layer position).residual)
    (hNormalized2 : (normalized2Heap heap position).OwnsPacked initial (normalized2Node heap position)
      (tensors weights input cache layer position).normalized2)
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
    (hNormalizedOwner : frame.locals[102]? = some (.i64 (normalized2Node heap position).root))
    (hNormalizedPtr : frame.locals[103]? = some (.i64 (normalized2Node heap position).root))
    (hNormalizedSize : frame.locals[104]? = some (.i64 3072))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      ResultState (parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position) (frame.locals.take 110) 110
        (finiteWords (tensors weights input cache layer position).activated 0 3072)
        (hiddenNode heap position).root (cacheNode heap position).root result →
      Completion (normalized2Heap heap position) initial
        (feedForwardHeap heap position (tensors weights input cache layer position)) final
        (finiteWords (tensors weights input cache layer position).activated 0 3072)
        (hiddenNode heap position) (cacheNode heap position)
        (tensors weights input cache layer position).hidden
        (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (tensors weights input cache layer position).qkv) →
      wp «module» rest Q final result env) :
    wp «module» (normalized2Success ++ rest) Q initial frame env := by
  let values := tensors weights input cache layer position
  let params := parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position
  have hSizes : values.Sizes := tensors_sizes weights input cache layer position hInputSize
  rw [normalized2Success_shape]
  simp only [List.append_assoc]
  apply expanded_spec env initial (normalized2Heap heap position)
    weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr (normalized2Node heap position).root
    weights input cache values.normalized2 layer position (blocksOffset + layer * blockBytes) frame
    hHeap hWeights hNormalized2.buffer.values hWeightsProtected hNormalized2.payload_protects
    hSizes.normalized2 hExtent hResources.expanded hPages hParams hLength hValues hBase hTyped
    hNormalizedOwner hNormalizedPtr hNormalizedSize
  intro store7 frame7 hState7 hOutput7
  let item7 : PackedReleaseMany.Item := ⟨134, expandedNode heap position, values.expanded⟩
  have hOwners7 : Owners (normalized2Heap heap position) (expandedHeap heap position) store7 [item7] :=
    (Owners.nil (normalized2Heap heap position) (normalized2Heap heap position) initial).cons
      (Heap.Frame.refl _ _) hOutput7.frame hOutput7.heapAt item7 hOutput7.owned
      (GroupedProjection.Projection.outputNode_fresh hResources.expanded)
  have hBindings7 : Bindings [item7] frame7 :=
    (by simp only [Bindings, List.not_mem_nil, false_implies, implies_true] : Bindings [] frame7).cons
      item7 (hState7.owner_get (by decide))
  rcases hState7 with ⟨hParams7, hLength7, hValues7, hTyped7, hPrefix7,
    hOwner7, hPtr7, hSize7, hCopyOwner7, hCopyPtr7, hCopySize7⟩
  have hResource8 : Gpt2CachedStep.LayerNorm.AllocationFits (expandedHeap heap position)
      activatedNeed (store7.memoryCap Project.Gpt2CachedStep.«module» 0) := by
    rw [← memoryCap_eq_fp32, hOutput7.memoryCap]
    exact hResources.activated
  apply activated_spec env store7 (expandedHeap heap position) params (expandedNode heap position).root
    values.expanded frame7 hOutput7.heapAt hOutput7.owned.buffer.values hOutput7.owned.payload_protects
    hSizes.expanded hResource8 hOutput7.pages hParams7 rfl hLength7 hValues7 hTyped7
    hCopyOwner7 hCopyPtr7 hCopySize7
  intro store8 frame8 hState8 hHeap8 hOwned8 hStep8 hPages8 hStepCap8
  have hFrame8 := hOutput7.frame.trans hStep8
  have hCap8 : store8.memoryCap «module» 0 = initial.memoryCap «module» 0 := by
    rw [memoryCap_eq_fp32, hStepCap8, ← memoryCap_eq_fp32, hOutput7.memoryCap]
  let item8 : PackedReleaseMany.Item := ⟨143, activatedNode heap position, values.activated⟩
  have hOwners8 : Owners (normalized2Heap heap position) (activatedHeap heap position) store8 [item8, item7] :=
    hOwners7.cons hOutput7.frame hStep8 hHeap8 item8 hOwned8
      ((expandedHeap heap position).freshNode_allocated activatedNeed (fun h => (hResources.activated h).1.le))
  have hBindings8 : Bindings [item8, item7] frame8 :=
    (hState8.bindings hBindings7 hParams7 hLength7 (by decide)
      (by simp [item7, params, parameters])).cons item8 (hState8.owner_get (by decide))
  rcases hState8 with ⟨hParams8, hLength8, hValues8, hTyped8, hPrefix8,
    hOwner8, hPtr8, hSize8, hCopyOwner8, hCopyPtr8, hCopySize8⟩
  have hResources8 : Resources heap position (store8.memoryCap «module» 0) := by rw [hCap8]; exact hResources
  have read8 (index : Nat) (hi : index < 110) : frame8.locals[index]? = frame.locals[index]? :=
    (Frame.local_of_take_eq hPrefix8 (by omega)).trans (Frame.local_of_take_eq hPrefix7 hi)
  apply guardedRelease_spec env (normalized2Heap heap position) (activatedHeap heap position)
    (tailHeap heap position) initial store8 params frame8 [item8, item7]
    (hiddenNode heap position) (cacheNode heap position) values.hidden
    (Project.Gpt2CachedStep.CachedBlock.cacheUpdate values.qkv)
    (activatedNode heap position).root (activatedNode heap position).root values.activated 3072 135 activatedSuccess true
    hHeap8 hFrame8 hPages8 hCap8 hOwners8 hBindings8 (by simp [item8, item7]) hOwned8.buffer.values
    (by rw [hSizes.activated]) (by simp) hParams8 rfl hLength8 hValues8 hCopyOwner8 hCopyPtr8
    (by rw [hSizes.activated]; exact hCopySize8) hTyped8
  · intro prepared hPreparedParams hPreparedLength hPreparedTyped hPreparedPrefix hPreparedValues R hDone
    have readPrepared (index : Nat) (hi : index < 110) : prepared.locals[index]? = frame.locals[index]? :=
      (Frame.local_of_take_eq hPreparedPrefix (by omega)).trans (read8 index hi)
    rw [← List.append_nil activatedSuccess]
    apply tail_spec env store8 heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
      weights input cache layer position prepared hHeap8 (hFrame8.packed hWeightsProtected hWeights)
      (hFrame8.protects _ _ hWeightsProtected) (hFrame8.ownsPacked hHeap8 hQkv)
      (hFrame8.ownsPacked hHeap8 hResidual) hOwned8 hExtent hInputSize hResources8 hPages8
      (hPreparedParams.trans hParams8) hPreparedLength hPreparedValues hPreparedTyped
      ((readPrepared 0 (by decide)).trans hBase)
      ((readPrepared 37 (by decide)).trans hQkvOwner) ((readPrepared 38 (by decide)).trans hQkvPtr)
      ((readPrepared 39 (by decide)).trans hQkvSize) ((readPrepared 87 (by decide)).trans hResidualOwner)
      ((readPrepared 88 (by decide)).trans hResidualPtr) ((readPrepared 89 (by decide)).trans hResidualSize)
      ((Frame.local_of_take_eq hPreparedPrefix (by decide : 135 < 135 + 3)).trans hCopyOwner8)
      ((Frame.local_of_take_eq hPreparedPrefix (by decide : 136 < 135 + 3)).trans hCopyPtr8)
      ((Frame.local_of_take_eq hPreparedPrefix (by decide : 137 < 135 + 3)).trans hCopySize8)
    intro final result hResult hOutput
    simp only [wp_nil]
    apply hDone final result (hResult.narrow (by decide : 138 ≤ 143) ?_) hOutput
    simpa only [List.take_take, show min 138 143 = 138 from rfl] using hPreparedPrefix
  · intro final result hResult hOutput
    simp only [Bool.and_true] at hResult hOutput
    apply hNext final result (hResult.narrow (by decide : 110 ≤ 138) ?_) hOutput
    have hTake := congrArg (List.take 110) hPrefix8
    simp only [List.take_take, show min 110 129 = 110 from rfl] at hTake
    simpa only [List.take_take, show min 110 138 = 110 from rfl] using hTake.trans hPrefix7

#print axioms feedForward_spec
end Project.Gpt2QuantizedCached.CachedBlock
