import Project.Gpt2QuantizedCached.CachedHidden.LayerPrepare
import Project.Gpt2QuantizedCached.CachedBlock.Spec

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

structure CalledFrame (params : List Value) (embedding input updates hidden cache : UInt64)
    (inputSize updateBytes : Nat) (inputStatus : UInt64) (layer : Nat) (output : HiddenResult)
    (frame : Locals) : Prop
    extends LayerFrame params embedding input updates inputSize updateBytes inputStatus layer frame where
  cacheOwner : frame.locals[49]? = some (.i64 cache)
  outputHiddenOwner : frame.locals[60]? = some (.i64 hidden)
  outputHiddenPtr : frame.locals[61]? = some (.i64 hidden)
  outputHiddenSize : frame.locals[62]? = some (.i64 (UInt64.ofNat output.hidden.size))
  outputStatus : frame.locals[59]? = some (.i64 output.status)
  oldSize : frame.locals[64]? = some (.i64 (UInt64.ofNat updateBytes))
  blockSize : frame.locals[66]? = some (.i64 (UInt64.ofNat output.cache.size))
  leftPtr : frame.locals[122]? = some (.i64 updates)
  leftSize : frame.locals[123]? = some (.i64 (UInt64.ofNat updateBytes))
  rightPtr : frame.locals[124]? = some (.i64 cache)
  rightSize : frame.locals[125]? = some (.i64 (UInt64.ofNat output.cache.size))

theorem layerCall_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr embeddingPtr inputPtr updatesPtr : UInt64)
    (weights input cache : ByteArray) (token : UInt32) (position layer updatesSize : Nat)
    (status : UInt64) (frame : Locals)
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
    (hResources : CachedBlock.Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hState : PreparedFrame (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      embeddingPtr inputPtr updatesPtr input.size updatesSize status layer frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      let output := cachedBlock weights input cache layer position
      CalledFrame (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        embeddingPtr inputPtr updatesPtr
        (if output.status = 0 then (CachedBlock.hiddenNode heap position).root else 0)
        (if output.status = 0 then (CachedBlock.cacheNode heap position).root else 0)
        input.size updatesSize status layer output result →
      CachedBlock.Completion heap initial
        (CachedBlock.executionHeap heap position (CachedBlock.tensors weights input cache layer position)) final
        (CachedBlock.tensors weights input cache layer position).accepted
        (CachedBlock.hiddenNode heap position) (CachedBlock.cacheNode heap position)
        (CachedBlock.tensors weights input cache layer position).hidden
        (Project.Gpt2CachedStep.CachedBlock.cacheUpdate (CachedBlock.tensors weights input cache layer position).qkv) →
      wp «module» rest Q final result env) :
    wp «module» (layerCallCode ++ rest) Q initial frame env := by
  simp only [layerCallCode, List.cons_append, List.nil_append]
  wp_packed_frame [hState.paramsEq, parameters, hState.length, hState.values,
    hState.layerCopy, hState.hiddenOwnerCopy, hState.hiddenPtrCopy, hState.hiddenSizeCopy]
  refine wp_call_tw (CachedBlock.Spec.cachedBlock_exact env initial heap weightsOwner inputPtr cacheOwner
    weightsPtr inputPtr cachePtr weights input cache layer position hHeap hWeights hInput hCache
    hWeightsProtected hInputProtected hCacheProtected hLayer hPosition hExtent hInputSize hCacheSize
    hResources hPages) ?_
  rintro final returned ⟨hReturned, hCompletion⟩
  subst returned
  simp only [CachedBlock.Spec.sourceResultValues]
  wp_packed_frame [hState.paramsEq, parameters, hState.length, hState.updatesPtrCopy, hState.updatesSizeCopy]
  apply hNext
  · constructor
    · constructor <;>
        simp (config := { maxDischargeDepth := 64 }) only [parameters, hState.length,
          List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
          I64Values.set, hState.typed, hState.embeddingOwner, hState.embeddingPtr,
          hState.embeddingSize, hState.protectedEmbedding, hState.protectedUpdates,
          hState.hiddenOwner, hState.hiddenPtr, hState.hiddenSize, hState.updatesOwner,
          hState.updatesPtr, hState.updatesSize, hState.status, hState.counter,
          hState.limit, hState.step, hState.flag]
    all_goals simp only [hState.length, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte]
  · exact hCompletion

#print axioms layerCall_spec
end Project.Gpt2QuantizedCached.CachedHidden
