import Project.Gpt2QuantizedCached.Entry.OutputMemory
import Project.Gpt2QuantizedCached.GroupedProjection.Fresh

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def vocabularyNode (heap : Heap) : FreeNode := GroupedProjection.Projection.outputNode heap 768 50257 1

def vocabularyHeap (heap : Heap) (cache : FreeNode) (weights outputCache normalized : ByteArray) (position : Nat) : Heap :=
  outputHeap (GroupedProjection.Projection.outputHeap heap 768 50257 1) cache (vocabularyNode heap)
    (outputRejected outputCache (vocabulary weights normalized) position)

theorem vocabularyStage_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (hiddenNode cacheNode normalizedNode : FreeNode)
    (weights cache hidden outputCache normalized : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hHidden : heap.OwnsPacked initial hiddenNode hidden) (hCache : heap.OwnsPacked initial cacheNode outputCache)
    (hNormalized : heap.OwnsPacked initial normalizedNode normalized)
    (hCacheFresh : before.FreshNode cacheNode)
    (hHiddenCache : regionsDisjoint hiddenNode.region cacheNode.region)
    (hNormalizedCache : regionsDisjoint normalizedNode.region cacheNode.region)
    (hFrame : before.Frame original heap initial)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hHeader : validHeader weights = true) (hNormalizedSize : normalized.size = 3072)
    (hCacheSize : (position + 1) * cachePositionWords * 4 ≤ outputCache.size) (hPosition : position < 128)
    (hResources : GroupedProjection.Projection.Resources heap 768 50257 1 (initial.memoryCap «module» 0))
    (hState : NormalizedState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
      hiddenNode.root cacheNode.root normalizedNode.root outputCache.size frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      let output := outputResult outputCache (vocabulary weights normalized) position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status cacheNode) (statusRoot output.status (vocabularyNode heap))
        output.cache.size output.logits.size result →
      result.locals[17]? = some (.i64 hiddenNode.root) → result.locals[39]? = some (.i64 normalizedNode.root) →
      Completion before original (vocabularyHeap heap cacheNode weights outputCache normalized position) final
        output.status cacheNode (vocabularyNode heap) output.cache output.logits →
      (vocabularyHeap heap cacheNode weights outputCache normalized position).OwnsPacked final hiddenNode hidden →
      (vocabularyHeap heap cacheNode weights outputCache normalized position).OwnsPacked final normalizedNode normalized →
      (output.status = 0 → regionsDisjoint hiddenNode.region (vocabularyNode heap).region) →
      (output.status = 0 → regionsDisjoint normalizedNode.region (vocabularyNode heap).region) →
      wp «module» rest Q final result env) :
    wp «module» (normalizedBody ++ rest) Q initial frame env := by
  rw [emitted_normalizedBody]
  simp only [List.append_assoc]
  apply logits_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr hiddenNode.root cacheNode.root
    normalizedNode.root weights cache normalized token position outputCache.size frame hHeap hWeights
    hNormalized.buffer.values hWeightsProtected hNormalized.payload_protects hHeader hNormalizedSize
    hResources hPages hState
  intro projected prepared hPrepared hOutput
  have hFresh := GroupedProjection.Projection.outputNode_fresh hResources
  have hCache' := hOutput.frame.ownsPacked hOutput.heapAt hCache
  have hHidden' := hOutput.frame.ownsPacked hOutput.heapAt hHidden
  have hNormalized' := hOutput.frame.ownsPacked hOutput.heapAt hNormalized
  have hCacheLogits := regionsDisjoint_symm (hFresh.owns_disjoint hOutput.owned.buffer.rootBound hCache)
  have hHiddenLogits := regionsDisjoint_symm (hFresh.owns_disjoint hOutput.owned.buffer.rootBound hHidden)
  have hNormalizedLogits := regionsDisjoint_symm (hFresh.owns_disjoint hOutput.owned.buffer.rootBound hNormalized)
  apply outputResult_spec env original projected before (GroupedProjection.Projection.outputHeap heap 768 50257 1)
    weightsOwner weightsPtr cacheOwner cachePtr hiddenNode.root normalizedNode.root cacheNode (vocabularyNode heap)
    weights cache outputCache (vocabulary weights normalized) token position prepared hOutput.heapAt hCache'
    hOutput.owned hCacheFresh (hFrame.freshNode hFresh) hCacheLogits (hFrame.trans hOutput.frame)
    hOutput.pages ((hOutput.memoryCap «module» 0).trans hCap) hCacheSize
    (by unfold vocabulary; rw [GroupedProjection.linearGroupedRows_size]) hPosition hPrepared
  intro result
  dsimp only
  intro hResult hHiddenRead hNormalizedRead hMemory
  exact hNext _ result hResult hHiddenRead hNormalizedRead hMemory
    (outputOwned _ _ _ _ _ _ _ _ _ hCache' hOutput.owned hHidden' hHiddenCache hHiddenLogits)
    (outputOwned _ _ _ _ _ _ _ _ _ hCache' hOutput.owned hNormalized' hNormalizedCache hNormalizedLogits)
    (fun _ => hHiddenLogits) (fun _ => hNormalizedLogits)

#print axioms vocabularyStage_spec
end Project.Gpt2QuantizedCached.Entry
