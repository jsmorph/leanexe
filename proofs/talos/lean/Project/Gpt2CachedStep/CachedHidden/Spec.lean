import Project.Gpt2CachedStep.CachedHidden.Body

namespace Project.Gpt2CachedStep.CachedHidden.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

theorem cachedHidden_hidden_size (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    (cachedHidden weights cache token position).hidden.size = 3072 := by
  rw [cachedHidden_eq]
  exact (layerPrefix_sizes weights cache token position 12).1

theorem cachedHidden_cache_size (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    (cachedHidden weights cache token position).cache.size = cache.size + 73728 := by
  rw [cachedHidden_eq]
  simp only [ByteArray.size_append, (layerPrefix_sizes weights cache token position 12).2]

theorem cachedHidden_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hTokenSize : 4 * (token.toNat * 768 + 768) ≤ weights.size)
    (hPositionSize : 4 * (positionOffset + position * 768 + 768) ≤ weights.size)
    (hWeightsSize : (blocksOffset + 12 * blockWords) * 4 ≤ weights.size)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hAppendSize : cache.size + 73728 ≤ 4294967296)
    (hResources : Resources heap position cache.size (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := cachedHidden weights cache token position
    TerminatesWith env «module» 36 initial
      [.i64 (UInt64.ofNat position), .i64 (UInt64.ofNat token.toNat),
       .i64 (UInt64.ofNat cache.size), .i64 cachePtr, .i64 cacheOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.cache.size),
          .i64 (cacheNode heap position cache.size).root, .i64 (cacheNode heap position cache.size).root,
          .i64 (UInt64.ofNat output.hidden.size),
          .i64 (traversed heap position).hidden.root, .i64 (traversed heap position).hidden.root] ∧
        (finalHeap heap position cache.size).At final ∧
        (finalHeap heap position cache.size).OwnsPacked final (traversed heap position).hidden output.hidden ∧
        (finalHeap heap position cache.size).OwnsPacked final (cacheNode heap position cache.size) output.cache ∧
        heap.Frame initial (finalHeap heap position cache.size) final ∧
        heap.FreshNode (traversed heap position).hidden ∧ heap.FreshNode (cacheNode heap position cache.size) ∧
        regionsDisjoint (traversed heap position).hidden.region (cacheNode heap position cache.size).region ∧
        final.mem.pages ≤ 65536 ∧ final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func36Def) rfl ?_
  change wp «module» func36 _ initial
    { params := parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position,
      locals := List.replicate 124 (.i64 0) } env
  apply body_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position _
    hHeap hWeights hCache hWeightsProtected hCacheProtected hToken hPosition hTokenSize hPositionSize hWeightsSize
    hCacheSize hAppendSize hResources hPages rfl (List.length_replicate ..) rfl (I64Values.replicate _ _)
  intro final result hValues hFinalHeap hHidden hCache hFrame hHiddenFresh hCacheFresh hSeparated hFinalPages hCapacity
  have hPost := And.intro hFinalHeap (And.intro hHidden (And.intro hCache (And.intro hFrame
    (And.intro hHiddenFresh (And.intro hCacheFresh (And.intro hSeparated (And.intro hFinalPages hCapacity)))))))
  simpa [func36Def, Function.numParams, hValues, cachedHidden_eq,
    (layerPrefix_sizes weights cache token position 12).1,
    (layerPrefix_sizes weights cache token position 12).2] using hPost

#print axioms cachedHidden_exact

end Project.Gpt2CachedStep.CachedHidden.Spec
