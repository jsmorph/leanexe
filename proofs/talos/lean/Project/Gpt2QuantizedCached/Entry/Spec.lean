import Project.Gpt2QuantizedCached.Entry.Front

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def resultValues (status : UInt64) (cache logits : FreeNode) (cacheSize logitsSize : Nat) : List Value :=
  [.i64 (UInt64.ofNat logitsSize), .i64 (statusRoot status logits), .i64 (statusRoot status logits),
   .i64 (UInt64.ofNat cacheSize), .i64 (statusRoot status cache), .i64 (statusRoot status cache), .i64 status]

theorem cachedStep_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner weightsPtr cacheOwner cachePtr : UInt64) (weights cache : ByteArray)
    (token : UInt32) (position : Nat)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hCacheFit : cache.size < UInt64.size) (hPositionFit : position < UInt64.size)
    (hResources : invalidInput cache token position = false →
      Resources heap weights cache token position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := cachedStep weights cache token position
    TerminatesWith env «module» 59 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64,
       .i64 (UInt64.ofNat cache.size), .i64 cachePtr, .i64 cacheOwner,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr, .i64 weightsOwner]
      (fun final returned =>
        returned = resultValues output.status (outputCacheNode heap weights cache token position)
          (outputLogitsNode heap weights cache token position) output.cache.size output.logits.size ∧
        Completion heap initial (finalHeap heap weights cache token position) final output.status
          (outputCacheNode heap weights cache token position) (outputLogitsNode heap weights cache token position)
          output.cache output.logits) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func59Def) rfl ?_
  change wp «module» func59 _ initial
    { params := parameters weightsOwner weightsPtr cacheOwner cachePtr weights cache token position,
      locals := List.replicate 93 (.i64 0) } env
  rw [← List.take_append_drop 22 func59, emitted_return]
  apply front_spec env initial heap weightsOwner weightsPtr cacheOwner cachePtr weights cache token position _
    hHeap hWeights hCache hWeightsProtected hCacheProtected hCacheFit hPositionFit hResources hPages
    ⟨rfl, List.length_replicate .., rfl, I64Values.replicate _ _⟩
  intro final result
  dsimp only
  intro hState hMemory
  apply return_spec env final _ _ _ _ _ _ result rfl hState
  simpa only [func59Def, Function.numParams, resultValues, List.length_cons,
    List.length_nil, Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.append_nil, true_and] using hMemory

#print axioms cachedStep_exact
end Project.Gpt2QuantizedCached.Entry
