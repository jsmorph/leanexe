import Project.Gpt2QuantizedCached.CachedHidden.LayerLoop
import Project.Gpt2QuantizedCached.CachedHidden.TraversalFinish
import Project.Gpt2QuantizedCached.CachedHidden.FinishTail
import Project.Gpt2QuantizedCached.CachedHidden.Plan

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open Project.Gpt2CachedStep.LayerNorm (AllocationFits)

set_option maxRecDepth 32768 in
theorem emitted_body : func58 = embeddingCode ++ (func58.drop 57).take 1 ++
    (func58.drop 58).take 48 ++ func58.drop 106 := rfl

theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hScaleSize : tokenScaleOffset + token.toNat * 4 + 4 ≤ weights.size)
    (hTokenSize : tokenWeightOffset + token.toNat * 768 + 768 ≤ weights.size)
    (hPositionSize : positionOffset + (position * 768 + 768) * 4 ≤ weights.size)
    (hWeightsSize : blocksOffset + 12 * blockBytes ≤ weights.size)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hAppendSize : cache.size + 73728 ≤ 4294967296)
    (hResources : Resources heap weights cache token position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
    (hLocals : frame.locals.length = 141) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit)
    (hNext : ∀ (final : Store Unit) (result : Locals),
      let source := layerPrefix weights cache token position 12
      let output := finishValue source.2.2 source.1 cache source.2.1
      result.values = resultValues source.2.2 (traversed heap weights cache token position).hidden
        (cacheNode heap weights cache token position) output.hidden.size output.cache.size →
      Completion heap initial (finalHeap heap weights cache token position) final source.2.2
        (traversed heap weights cache token position).hidden (cacheNode heap weights cache token position)
        output.hidden output.cache → Q (.Fallthrough final result)) :
    wp «module» func58 Q initial frame env := by
  have hEmbeddingFresh := heap.freshNode_allocated Embedding.need (fun h => (hResources.embedding h).1.le)
  rw [emitted_body]
  simp only [List.append_assoc]
  apply embedding_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position frame
    hHeap hWeights hScaleSize hTokenSize hPositionSize hToken hPosition hWeightsProtected hResources.embedding hPages
    hParams hLocals hValues hTyped
  intro embeddingStore embeddingFrame
  dsimp only
  intro hEmbeddingState hEmbeddingHeap hEmbeddingOutput hEmbeddingFrame hEmbeddingPages hEmbeddingCapacity
  have hLayers : TraversalResources (embeddingHeap heap) (embeddingNode heap) weights cache token position
      (embeddingStore.memoryCap «module» 0) := by
    rw [hEmbeddingCapacity]
    exact hResources.layers
  apply layerLoop_spec env embeddingStore (embeddingHeap heap) (embeddingNode heap)
    weightsOwner weightsPtr cacheOwner cachePtr weights cache token position embeddingFrame
    hEmbeddingHeap hEmbeddingOutput
    (hEmbeddingFrame.packed hWeightsProtected hWeights) (hEmbeddingFrame.packed hCacheProtected hCache)
    (hEmbeddingFrame.protects _ _ hWeightsProtected) (hEmbeddingFrame.protects _ _ hCacheProtected)
    hPosition hCacheSize hWeightsSize hLayers hEmbeddingPages hEmbeddingState
  intro traversedStore traversedFrame hTraversal
  apply traversalFinish_spec env initial embeddingStore traversedStore heap (embeddingHeap heap)
    (embeddingNode heap) (embedding weights token position) cache cachePtr
    (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
    (layerPrefix weights cache token position 12) (traversed heap weights cache token position) traversedFrame
    rfl rfl rfl hEmbeddingFrame hEmbeddingCapacity hEmbeddingOutput hEmbeddingFresh hCache hCacheProtected
    (layerPrefix_valid weights cache token position 12) hAppendSize hResources.cache hTraversal
  exact hNext

#print axioms body_spec
end Project.Gpt2QuantizedCached.CachedHidden
