import Project.Gpt2CachedStep.RowMean
import Project.Gpt2CachedStep.RowInvStd
import Project.Gpt2CachedStep.LinearRows.Heap
import Project.Gpt2CachedStep.Release
import Project.Gpt2CachedStep.LayerNorm.Spec
import Project.Gpt2CachedStep.CachedScore.Spec
import Project.Gpt2CachedStep.FiniteLt
import Project.Gpt2CachedStep.ExpPolynomial
import Project.Gpt2CachedStep.CachedRowSum.Spec
import Project.Gpt2CachedStep.CachedRowMaximum.Spec
import Project.Gpt2CachedStep.Gelu
import Project.Gpt2CachedStep.Activate.Spec
import Project.Gpt2CachedStep.AddRows.Spec
import Project.Gpt2CachedStep.CachedAttention.Spec
import Project.Gpt2CachedStep.CachedBlock.Cache
import Project.Gpt2CachedStep.CachedBlock.Cleanup
import Project.Gpt2CachedStep.CachedBlock.Base
import Project.Gpt2CachedStep.CachedBlock.Attention
import Project.Gpt2CachedStep.CachedBlock.Normalized2
import Project.Gpt2CachedStep.CachedBlock.Activated
import Project.Gpt2CachedStep.CachedBlock.Projected2
import Project.Gpt2CachedStep.CachedBlock.Hidden
import Project.Gpt2CachedStep.CachedBlock.Spec
import Project.Gpt2CachedStep.CachedHidden.Source
import Project.Gpt2CachedStep.CachedHidden.Code
import Project.Gpt2CachedStep.CachedHidden.Embedding
import Project.Gpt2CachedStep.CachedHidden.LayerAppend
import Project.Gpt2CachedStep.CachedHidden.LayerCacheRelease
import Project.Gpt2CachedStep.CachedHidden.LayerOldRelease
import Project.Gpt2CachedStep.CachedHidden.LayerControl
import Project.Gpt2CachedStep.CachedHidden.LayerStep
import Project.Gpt2CachedStep.CachedHidden.Traversal
import Project.Gpt2CachedStep.CachedHidden.LayerLoop
import Project.Gpt2CachedStep.CachedHidden.Spec
import Project.Gpt2CachedStep.Vocabulary.Spec
import Project.Gpt2CachedStep.Entry.Accepted
import Project.Gpt2CachedStep.Entry.Rejected
import Project.Gpt2CachedStep.Entry.Budget
import Project.Gpt2CachedStep.Session.Spec

namespace Project.Gpt2CachedStep.Spec
open Wasm Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

theorem cachedStep_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr cachePtr : UInt64) (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hPosition : position < UInt64.size)
    (hResources : Entry.Valid weights cache token position →
      Entry.Resources heap position cache.size (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := cachedStep weights cache token position
    TerminatesWith env «module» 38 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64, .i64 (UInt64.ofNat cache.size), .i64 cachePtr,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr]
      (fun final values => ∃ (outputCachePtr outputLogitsPtr : UInt64) (outputHeap : Heap),
        values = [.i64 (UInt64.ofNat output.logits.size), .i64 outputLogitsPtr,
          .i64 (UInt64.ofNat output.cache.size), .i64 outputCachePtr] ∧
        ByteArrayAt final.mem outputCachePtr.toNat output.cache ∧
        ByteArrayAt final.mem outputLogitsPtr.toNat output.logits ∧
        outputHeap.At final ∧ heap.Frame initial outputHeap final ∧
        final.mem.pages ≤ 65536 ∧ final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  by_cases hValid : Entry.Valid weights cache token position
  · refine TerminatesWith.mono (Entry.cachedStep_accepted env initial heap weightsPtr cachePtr weights cache
      token position hHeap hWeights hCache hWeightsProtected hCacheProtected hValid (hResources hValid) hPages) ?_
    rintro final values ⟨hValues, hFinalHeap, hFinalCache, hFinalLogits, hFrame, _, _, _, hFinalPages, hCapacity⟩
    exact ⟨(Entry.cacheNode heap position cache.size).root, (Entry.logitsNode heap position cache.size).root,
      Entry.finalHeap heap position cache.size, hValues, hFinalCache.buffer.values, hFinalLogits.buffer.values,
      hFinalHeap, hFrame, hFinalPages, hCapacity⟩
  · have hWeightsFit : weights.size < UInt64.size := by
      have := hWeights.1
      change weights.size < 18446744073709551616
      omega
    have hCacheFit : cache.size < UInt64.size := by
      have := hCache.1
      change cache.size < 18446744073709551616
      omega
    refine TerminatesWith.mono (Entry.cachedStep_rejected env initial weightsPtr cachePtr weights cache
      token position hWeightsFit hCacheFit hPosition hValid) ?_
    rintro final values ⟨rfl, rfl⟩
    rw [Entry.cachedStep_invalid hValid]
    refine ⟨0, 0, heap, rfl, ?_, ?_, hHeap, Heap.Frame.refl .., hPages, rfl⟩
    all_goals simp [ByteArrayAt]

#print axioms cachedStep_exact

end Project.Gpt2CachedStep.Spec
