import Project.Gpt2CachedStep.Entry.Body
import Project.Gpt2CachedStep.Entry.GuardValid

namespace Project.Gpt2CachedStep.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution LeanExe.Models.Gpt2

theorem cachedStep_accepted (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr cachePtr : UInt64) (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hValid : Valid weights cache token position)
    (hResources : Resources heap position cache.size (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := cachedStep weights cache token position
    TerminatesWith env «module» 38 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64, .i64 (UInt64.ofNat cache.size), .i64 cachePtr,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.logits.size), .i64 (logitsNode heap position cache.size).root,
          .i64 (UInt64.ofNat output.cache.size), .i64 (cacheNode heap position cache.size).root] ∧
        (finalHeap heap position cache.size).At final ∧
        (finalHeap heap position cache.size).OwnsPacked final (cacheNode heap position cache.size) output.cache ∧
        (finalHeap heap position cache.size).OwnsPacked final (logitsNode heap position cache.size) output.logits ∧
        heap.Frame initial (finalHeap heap position cache.size) final ∧
        regionsDisjoint (cacheNode heap position cache.size).region (logitsNode heap position cache.size).region ∧
        heap.FreshNode (cacheNode heap position cache.size) ∧
        heap.FreshNode (logitsNode heap position cache.size) ∧
        final.mem.pages ≤ 65536 ∧ final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func38Def) rfl ?_
  change wp «module» func38 _ initial
    { params := parameters weightsPtr cachePtr weights cache token position, locals := List.replicate 55 (.i64 0) } env
  apply guard_valid_spec env initial weightsPtr cachePtr weights cache token position _ hValid
    ⟨rfl, List.length_replicate .., rfl, I64Values.replicate _ _⟩
  intro checkedFrame hChecked
  apply body_spec env initial heap weightsPtr cachePtr weights cache token position checkedFrame
    hHeap hWeights hCache hWeightsProtected hCacheProtected hValid hResources hPages hChecked
  intro final result hResult hFinalHeap hFinalCache hFinalLogits hFrame hSeparated hCacheFresh hLogitsFresh hFinalPages hCapacity
  rcases hResult with ⟨⟨hParams, hLocals, hValues, _⟩, _, _, _, hCachePtr, hCacheSize, _, hLogitsPtr, hLogitsSize, _⟩
  simp only [FixedArrayEqNode.branchPost, returnCode]
  wp_packed_frame [hParams, parameters, hLocals, hValues, hCachePtr, hCacheSize, hLogitsPtr, hLogitsSize]
  have hPost := And.intro hFinalHeap (And.intro hFinalCache (And.intro hFinalLogits
    (And.intro hFrame (And.intro hSeparated (And.intro hCacheFresh
      (And.intro hLogitsFresh (And.intro hFinalPages hCapacity)))))))
  simpa [func38Def, Function.numParams, cachedStep_valid hValid, Vocabulary.vocabularyHead_size,
    CachedHidden.Spec.cachedHidden_cache_size] using hPost

#print axioms cachedStep_accepted

end Project.Gpt2CachedStep.Entry
