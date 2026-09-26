import Project.Gpt2QuantizedCached.CachedBlock.Completion

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit

theorem CacheBuiltState.resultState {params saved wanted : List Value} {bound : Nat}
    {qkvOwner qkvPtr hiddenPtr outputPtr : UInt64} {qkv : ByteArray} {frame : Locals}
    (h : CacheBuiltState params saved qkvOwner qkvPtr hiddenPtr outputPtr qkv frame)
    (hBound : bound ≤ 171) (hSaved : saved.take bound = wanted) :
    ResultState params wanted bound true hiddenPtr outputPtr frame := by
  rcases h with ⟨⟨hParams, hLength, hValues, _, _, _, hHiddenOwner, hHiddenPtr,
    hHiddenBytes, hStatus, hTyped⟩, hCacheOwner, hCachePtr, hCacheBytes, hPrefix⟩
  refine ⟨hParams, hLength, hValues, hTyped, ?_, hStatus, hHiddenOwner, hHiddenPtr,
    hHiddenBytes, hCacheOwner, hCachePtr, hCacheBytes⟩
  have hTake := congrArg (List.take bound) hPrefix
  simpa only [List.take_take, Nat.min_eq_left hBound, hSaved] using hTake

#print axioms CacheBuiltState.resultState
end Project.Gpt2QuantizedCached.CachedBlock
