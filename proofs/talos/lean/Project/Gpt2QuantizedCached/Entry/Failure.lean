import Project.Gpt2QuantizedCached.Entry.Structure

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

theorem failureCache_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (cache logits : FreeNode) (cacheBytes : ByteArray) (frame : Locals)
    (hHeap : heap.At initial) (hCache : heap.OwnsPacked initial cache cacheBytes)
    (hFresh : before.FreshNode cache) (hFrame : before.Frame original heap initial)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hParams : params.length = 8) (hState : State params frame)
    (hRead : frame.locals[20]? = some (.i64 cache.root))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, ResultState params 4 0 0 0 0 result →
      result.locals.take 81 = frame.locals.take 81 →
      Completion before original (heap.release cache) (heap.releaseStore initial cache)
        4 cache logits .empty .empty →
      wp «module» rest Q (heap.releaseStore initial cache) result env) :
    wp «module» (normalizedFailureCode ++ rest) Q initial frame env := by
  simp only [normalizedFailureCode, List.append_assoc]
  apply failureResult_spec env initial params 4 (.constI64 4) frame hParams hState (Or.inl rfl)
  intro result hResult hPrefix
  have hCacheRead : result.get 28 = some (.i64 cache.root) := by
    simp only [Locals.get, hResult.paramsEq, hParams, hResult.length, Nat.reduceLT, Nat.reduceAdd,
      Nat.reduceSub, reduceIte]
    rw [Frame.local_of_take_eq hPrefix (by decide)]
    exact hRead
  have hRetained : ∀ entry ∈ ([(90, 0), (93, 0)] : List (Nat × UInt64)),
      result.get entry.1 = some (.i64 entry.2) := by
    intro entry hEntry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl
    all_goals simp only [Locals.get, hResult.paramsEq, hParams, hResult.length, Nat.reduceLT,
      Nat.reduceAdd, Nat.reduceSub, reduceIte, hResult.cacheOwner, hResult.logitsOwner]
  have hNonzero : cache.root ≠ 0 := by
    intro hZero
    have := hCache.buffer.rootBound
    rw [hZero] at this
    contradiction
  change wp «module» (PackedReleaseFilter.program 28 ([90, 93]) [.localGet 28, .call 65] ++ rest) _ _ _ _
  apply release_spec env original initial before heap 4 cache logits cache ByteArray.empty ByteArray.empty
    cacheBytes result 28 [(90, 0), (93, 0)]
    (Completion.failure before heap original initial 4 cache logits (by decide) hHeap hFrame hPages hCap)
    hCache hFresh (by intro h; contradiction) (by intro h; contradiction) hResult.values hCacheRead hRetained
  · intro entry hEntry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl <;> exact hNonzero
  · exact hNext result hResult hPrefix

#print axioms failureCache_spec
end Project.Gpt2QuantizedCached.Entry
