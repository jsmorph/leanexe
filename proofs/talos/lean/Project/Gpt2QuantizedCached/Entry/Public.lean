import Project.Gpt2QuantizedCached.Entry.Spec

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem tokenMask (token : UInt64) : token &&& 4294967295 = token.toUInt32.toUInt64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_and, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  exact Nat.and_two_pow_sub_one_eq_mod token.toNat 32

def publicValues (status : UInt64) (cache logits : FreeNode) (cacheSize logitsSize : Nat) : List Value :=
  [.i64 (UInt64.ofNat logitsSize), .i64 (statusRoot status logits),
   .i64 (UInt64.ofNat cacheSize), .i64 (statusRoot status cache), .i64 status]

theorem publicStep_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsPtr cachePtr : UInt64) (weights cache : ByteArray) (token position : UInt64)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hWeightsProtected : heap.Protects weightsPtr.toNat (weightsPtr.toNat + weights.size))
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hCacheFit : cache.size < UInt64.size)
    (hResources : invalidInput cache token.toUInt32 position.toNat = false →
      Resources heap weights cache token.toUInt32 position.toNat (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := cachedStep weights cache token.toUInt32 position.toNat
    TerminatesWith env «module» 61 initial
      [.i64 position, .i64 token, .i64 (UInt64.ofNat cache.size), .i64 cachePtr,
       .i64 (UInt64.ofNat weights.size), .i64 weightsPtr]
      (fun final returned =>
        returned = publicValues output.status (outputCacheNode heap weights cache token.toUInt32 position.toNat)
          (outputLogitsNode heap weights cache token.toUInt32 position.toNat) output.cache.size output.logits.size ∧
        Completion heap initial (finalHeap heap weights cache token.toUInt32 position.toNat) final output.status
          (outputCacheNode heap weights cache token.toUInt32 position.toNat)
          (outputLogitsNode heap weights cache token.toUInt32 position.toNat) output.cache output.logits) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func61Def) rfl ?_
  change wp «module» func61 _ initial
    { params := [.i64 weightsPtr, .i64 (UInt64.ofNat weights.size), .i64 cachePtr,
        .i64 (UInt64.ofNat cache.size), .i64 token, .i64 position],
      locals := List.replicate 7 (.i64 0) } env
  simp only [func61]
  wp_packed_frame []
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, tokenMask]
  have hCall := cachedStep_exact env initial heap 0 weightsPtr 0 cachePtr weights cache token.toUInt32 position.toNat
    hHeap hWeights hCache hWeightsProtected hCacheProtected hCacheFit position.toNat_lt hResources hPages
  simp only [UInt64.ofNat_toNat] at hCall
  refine wp_call_tw hCall ?_
  rintro final returned ⟨rfl, hMemory⟩
  simp only [resultValues]
  wp_packed_frame []
  simpa only [func61Def, Function.numParams, publicValues, List.length_cons,
    List.length_nil, Nat.reduceAdd, List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.append_nil, true_and] using hMemory

#print axioms publicStep_exact
end Project.Gpt2QuantizedCached.Entry
