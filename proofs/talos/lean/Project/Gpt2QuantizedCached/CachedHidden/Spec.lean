import Project.Gpt2QuantizedCached.CachedHidden.Body

namespace Project.Gpt2QuantizedCached.CachedHidden.Spec
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem cachedHidden_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat)
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
    (hPages : initial.mem.pages ≤ 65536) :
    let output := cachedHidden weights cache token position
    TerminatesWith env «module» 58 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64,
       .i64 (UInt64.ofNat cache.size), .i64 cachePtr, .i64 cacheOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final returned =>
        returned = resultValues output.status (traversed heap weights cache token position).hidden
          (cacheNode heap weights cache token position) output.hidden.size output.cache.size ∧
        Completion heap initial (finalHeap heap weights cache token position) final output.status
          (traversed heap weights cache token position).hidden (cacheNode heap weights cache token position)
          output.hidden output.cache) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func58Def) rfl ?_
  change wp «module» func58 _ initial
    { params := parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position,
      locals := List.replicate 141 (.i64 0) } env
  apply body_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position _
    hHeap hWeights hCache hWeightsProtected hCacheProtected hToken hPosition hScaleSize hTokenSize
    hPositionSize hWeightsSize hCacheSize hAppendSize hResources hPages
    rfl (List.length_replicate ..) rfl (I64Values.replicate _ _)
  intro final result
  dsimp only
  intro hValues hOutput
  have hValues' : result.values = resultValues (cachedHidden weights cache token position).status
      (traversed heap weights cache token position).hidden (cacheNode heap weights cache token position)
      (cachedHidden weights cache token position).hidden.size (cachedHidden weights cache token position).cache.size := by
    rw [cachedHidden_finish, finishValue_status]
    exact hValues
  have hOutput' : Completion heap initial (finalHeap heap weights cache token position) final
      (cachedHidden weights cache token position).status (traversed heap weights cache token position).hidden
      (cacheNode heap weights cache token position) (cachedHidden weights cache token position).hidden
      (cachedHidden weights cache token position).cache := by
    rw [cachedHidden_finish, finishValue_status]
    exact hOutput
  simpa only [func58Def, Function.numParams, hValues', resultValues, List.length_cons,
    List.length_nil, Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.append_nil, true_and] using hOutput'

#print axioms cachedHidden_exact
end Project.Gpt2QuantizedCached.CachedHidden.Spec
