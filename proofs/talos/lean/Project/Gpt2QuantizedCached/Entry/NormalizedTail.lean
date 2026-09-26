import Project.Gpt2QuantizedCached.Entry.VocabularyStage
import Project.Gpt2QuantizedCached.Entry.ReleaseResult

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized
open LeanExe.Models.Gpt2 (cachePositionWords)

def normalizedResult (weights outputCache normalized : ByteArray) (position : Nat) : CachedResult :=
  if finiteWords normalized 0 768 then outputResult outputCache (vocabulary weights normalized) position
  else ⟨4, .empty, .empty⟩

def normalizedTailHeap (heap : Heap) (cache normalizedNode : FreeNode)
    (weights outputCache normalized : ByteArray) (position : Nat) : Heap :=
  (if finiteWords normalized 0 768 then vocabularyHeap heap cache weights outputCache normalized position
    else heap.release cache).release normalizedNode

def normalizedTailCode : Program := finiteTestCode 42 45 768 ++ ReadOnlyDisjunction.negateProgram ++
  ReadOnlyDisjunction.canonicalProgram ++ [.iff 0 0 normalizedFailureCode normalizedBody] ++ releaseCode 47

set_option maxRecDepth 32768 in
theorem emitted_normalizedTail : hiddenBody.drop 61 = normalizedTailCode := rfl

theorem normalizedTail_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (hiddenNode cacheNode normalizedNode : FreeNode)
    (weights cache hidden outputCache normalized : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hHidden : heap.OwnsPacked initial hiddenNode hidden) (hCache : heap.OwnsPacked initial cacheNode outputCache)
    (hNormalized : heap.OwnsPacked initial normalizedNode normalized)
    (hCacheFresh : before.FreshNode cacheNode) (hNormalizedFresh : before.FreshNode normalizedNode)
    (hHiddenCache : regionsDisjoint hiddenNode.region cacheNode.region)
    (hHiddenNormalized : regionsDisjoint hiddenNode.region normalizedNode.region)
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
      let output := normalizedResult weights outputCache normalized position
      ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position)
        output.status (statusRoot output.status cacheNode) (statusRoot output.status (vocabularyNode heap))
        output.cache.size output.logits.size result →
      result.locals[17]? = some (.i64 hiddenNode.root) →
      Completion before original (normalizedTailHeap heap cacheNode normalizedNode weights outputCache normalized position)
        final output.status cacheNode (vocabularyNode heap) output.cache output.logits →
      (normalizedTailHeap heap cacheNode normalizedNode weights outputCache normalized position).OwnsPacked final hiddenNode hidden →
      (output.status = 0 → regionsDisjoint hiddenNode.region (vocabularyNode heap).region) →
      wp «module» rest Q final result env) :
    wp «module» (normalizedTailCode ++ rest) Q initial frame env := by
  simp only [normalizedTailCode, List.append_assoc]
  apply normalizedGuard_spec env initial _ hiddenNode.root cacheNode.root normalizedNode.root outputCache.size
    normalized frame (by rfl) hNormalized.buffer.values hNormalizedSize hState
  intro prepared hPrepared
  cases hFinite : finiteWords normalized 0 768
  · simp only [hFinite, Bool.false_eq_true, ite_false]
    rw [← List.append_nil normalizedFailureCode]
    apply failureCache_spec env original initial before heap _ cacheNode (vocabularyNode heap) outputCache
      prepared hHeap hCache hCacheFresh hFrame hPages hCap (by rfl) hPrepared.toState hPrepared.releaseCache
    intro result hResult hPrefix hMemory
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hRoot := hCache.buffer.rootBound
    have hRoot32 : cacheNode.root.toNat ≤ 4294967296 := by have := hCache.buffer.addressBound; omega
    have hHidden' := hHidden.released cacheNode hRoot hRoot32 hHiddenCache
    have hNormalized' := hNormalized.released cacheNode hRoot hRoot32 hNormalizedCache
    have hHiddenRead := (Frame.local_of_take_eq hPrefix (by decide : 17 < 81)).trans hPrepared.releaseHidden
    have hNormalizedRead := (Frame.local_of_take_eq hPrefix (by decide : 39 < 81)).trans hPrepared.releaseNormalized
    have hResult' : ResultState (parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position) 4 (statusRoot 4 cacheNode) (statusRoot 4 (vocabularyNode heap))
        ByteArray.empty.size ByteArray.empty.size result := by simpa only [statusRoot, show (4 : UInt64) ≠ 0 by decide,
          ite_false, ByteArray.size_empty] using hResult
    have hRun : wp «module» (releaseCode 47 ++ rest) Q (heap.releaseStore initial cacheNode) result env := by
      apply releaseResult_spec env original _ before (heap.release cacheNode) _ 4 cacheNode (vocabularyNode heap)
        normalizedNode .empty .empty normalized result 47 hMemory hNormalized' hNormalizedFresh
        (by intro h; contradiction) (by intro h; contradiction) (by rfl) hResult'
        (hResult.toState.get_local (by rfl) 39 _ (by decide) hNormalizedRead)
      intro hReleased
      have hFinalHidden := hHidden'.released normalizedNode hNormalized.buffer.rootBound
        (by have := hNormalized.buffer.addressBound; omega) hHiddenNormalized
      have hRun := hNext ((heap.release cacheNode).releaseStore (heap.releaseStore initial cacheNode) normalizedNode) result
      simp only [normalizedResult, normalizedTailHeap, hFinite, Bool.false_eq_true, ite_false,
        statusRoot, show (4 : UInt64) ≠ 0 by decide, ByteArray.size_empty] at hRun
      exact hRun hResult hHiddenRead hReleased hFinalHidden (by intro h; contradiction)
    simpa only [← hResult.values] using hRun
  · simp only [hFinite, ite_true]
    rw [← List.append_nil normalizedBody]
    apply vocabularyStage_spec env original initial before heap weightsOwner weightsPtr cacheOwner cachePtr
      hiddenNode cacheNode normalizedNode weights cache hidden outputCache normalized token position prepared
      hHeap hWeights hWeightsProtected hHidden hCache hNormalized hCacheFresh hHiddenCache hNormalizedCache
      hFrame hPages hCap hHeader hNormalizedSize hCacheSize hPosition hResources hPrepared
    intro final result
    dsimp only
    intro hResult hHiddenRead hNormalizedRead hMemory hHidden' hNormalized' hHiddenLogits hNormalizedLogits
    simp only [wp_nil, PackedReleaseFilter.afterAction]
    have hRun : wp «module» (releaseCode 47 ++ rest) Q final result env := by
      apply releaseResult_spec env original final before _ _ _ cacheNode (vocabularyNode heap) normalizedNode
        _ _ normalized result 47 hMemory hNormalized' hNormalizedFresh (fun _ => hNormalizedCache)
        hNormalizedLogits (by rfl) hResult
        (hResult.toState.get_local (by rfl) 39 _ (by decide) hNormalizedRead)
      intro hReleased
      have hFinalHidden := hHidden'.released normalizedNode hNormalized'.buffer.rootBound
        (by have := hNormalized'.buffer.addressBound; omega) hHiddenNormalized
      have hRun := hNext ((vocabularyHeap heap cacheNode weights outputCache normalized position).releaseStore final normalizedNode) result
      simp only [normalizedResult, normalizedTailHeap, hFinite, ite_true] at hRun
      exact hRun hResult hHiddenRead hReleased hFinalHidden hHiddenLogits
    simpa only [← hResult.values] using hRun

#print axioms normalizedTail_spec
end Project.Gpt2QuantizedCached.Entry
