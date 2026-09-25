import Project.Gpt2QuantizedCached.CachedBlock.Completion

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

theorem ResultState.narrow {params saved wanted : List Value} {bound count : Nat} {accepted : Bool}
    {hidden cache : UInt64} {frame : Locals}
    (h : ResultState params saved bound accepted hidden cache frame)
    (hCount : count ≤ bound) (hSaved : saved.take count = wanted) :
    ResultState params wanted count accepted hidden cache frame := by
  refine ⟨h.paramsEq, h.length, h.values, h.typed, ?_, h.status, h.hiddenOwner, h.hiddenPtr,
    h.hiddenSize, h.cacheOwner, h.cachePtr, h.cacheSize⟩
  have hTake := congrArg (List.take count) h.savedEq
  simpa only [List.take_take, Nat.min_eq_left hCount, hSaved] using hTake

theorem Completion.failure (heap : Heap) (initial : Store Unit)
    (hidden cache : FreeNode) (hiddenBytes cacheBytes : ByteArray)
    (hHeap : heap.At initial) (hPages : initial.mem.pages ≤ 65536) :
    Completion heap initial heap initial false hidden cache hiddenBytes cacheBytes :=
  ⟨hHeap, Heap.Frame.refl heap initial, hPages, rfl, by simp, by simp, by simp⟩

#print axioms ResultState.narrow
#print axioms Completion.failure
end Project.Gpt2QuantizedCached.CachedBlock
