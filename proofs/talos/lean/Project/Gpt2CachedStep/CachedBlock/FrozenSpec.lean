import Project.Gpt2CachedStep.CachedBlock.FrozenBody

namespace Project.Gpt2CachedStep.Frozen.CachedBlock.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

theorem cachedBlock_hidden_size (weights input cache : ByteArray) (layer position : Nat)
    (hInput : input.size = 3072) : (cachedBlock weights input cache layer position).hidden.size = 3072 := by
  rw [cachedBlock_tensors]
  exact (tensors_sizes weights input cache layer position hInput).hidden

theorem cachedBlock_cache_size (weights input cache : ByteArray) (layer position : Nat) :
    (cachedBlock weights input cache layer position).cache.size = 6144 := by
  rw [cachedBlock_tensors]
  exact cacheUpdate_size _

theorem cachedBlock_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr : UInt64)
    (weights input cache : ByteArray) (layer position : Nat)
    (hHeap : heap.At initial)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hInputSize : input.size = 3072) (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size)
    (hWeightsSize : (blocksOffset + layer * blockWords + blockWords) * 4 ≤ weights.size)
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := cachedBlock weights input cache layer position
    TerminatesWith env «module» 33 initial
      [.i64 (UInt64.ofNat position), .i64 (UInt64.ofNat layer),
       .i64 (UInt64.ofNat cache.size), .i64 cachePtr, .i64 cacheOwner,
       .i64 (UInt64.ofNat input.size), .i64 inputPtr, .i64 inputOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.cache.size),
          .i64 (cacheNode heap position).root, .i64 (cacheNode heap position).root,
          .i64 (UInt64.ofNat output.hidden.size),
          .i64 (hiddenNode heap position).root, .i64 (hiddenNode heap position).root] ∧
        (finalHeap heap position).At final ∧
        (finalHeap heap position).OwnsPacked final (hiddenNode heap position) output.hidden ∧
        (finalHeap heap position).OwnsPacked final (cacheNode heap position) output.cache ∧
        heap.Frame initial (finalHeap heap position) final ∧
        heap.FreshNode (hiddenNode heap position) ∧ heap.FreshNode (cacheNode heap position) ∧
        regionsDisjoint (hiddenNode heap position).region (cacheNode heap position).region ∧
        final.mem.pages ≤ 65536 ∧ final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func33Def) rfl ?_
  change wp «module» func33 _ initial
    { params := parameters weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
        weights input cache layer position
      locals := List.replicate 164 (.i64 0) } env
  apply body_spec env initial heap weightsOwner inputOwner cacheOwner weightsPtr inputPtr cachePtr
    weights input cache layer position _ hHeap hWeights hInput hCache hWeightsProtected hInputProtected
    hCacheProtected hLayer hPosition hInputSize hCacheSize hWeightsSize hResources hPages
    rfl (List.length_replicate ..) rfl (I64Values.replicate _ _)
  intro final result hValues hFinalHeap hHidden hCache hFrame hHiddenFresh hCacheFresh hSeparated hFinalPages hCapacity
  have hPost := And.intro hFinalHeap (And.intro hHidden (And.intro hCache (And.intro hFrame
    (And.intro hHiddenFresh (And.intro hCacheFresh (And.intro hSeparated (And.intro hFinalPages hCapacity)))))))
  simpa [func33Def, Function.numParams, hValues, cachedBlock_cache_size,
    cachedBlock_hidden_size weights input cache layer position hInputSize] using hPost

#print axioms cachedBlock_exact

end Project.Gpt2CachedStep.Frozen.CachedBlock.Spec
