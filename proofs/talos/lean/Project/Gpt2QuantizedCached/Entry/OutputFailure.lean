import Project.Gpt2QuantizedCached.Entry.Failure

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

theorem failureOutput_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (hidden normalized : UInt64) (cache logits : FreeNode)
    (cacheBytes logitsBytes : ByteArray) (frame : Locals)
    (hHeap : heap.At initial) (hCache : heap.OwnsPacked initial cache cacheBytes)
    (hLogits : heap.OwnsPacked initial logits logitsBytes)
    (hCacheFresh : before.FreshNode cache) (hLogitsFresh : before.FreshNode logits)
    (hSeparated : regionsDisjoint cache.region logits.region)
    (hFrame : before.Frame original heap initial)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.memoryCap «module» 0 = original.memoryCap «module» 0)
    (hParams : params.length = 8)
    (hState : LogitsState params hidden cache.root normalized logits.root cacheBytes.size frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, ResultState params 4 0 0 0 0 result →
      result.locals.take 81 = frame.locals.take 81 →
      Completion before original ((heap.release logits).release cache)
        ((heap.release logits).releaseStore (heap.releaseStore initial logits) cache)
        4 cache logits .empty .empty →
      wp «module» rest Q ((heap.release logits).releaseStore (heap.releaseStore initial logits) cache) result env) :
    wp «module» (outputFailureCode ++ rest) Q initial frame env := by
  simp only [outputFailureCode, List.append_assoc]
  apply failureResult_spec env initial params 4 (.constI64 4) frame hParams hState.toState (Or.inl rfl)
  intro result hResult hPrefix
  have hCacheRead : result.get 28 = some (.i64 cache.root) := by
    simp only [Locals.get, hResult.paramsEq, hParams, hResult.length, Nat.reduceLT, Nat.reduceAdd,
      Nat.reduceSub, reduceIte]
    rw [Frame.local_of_take_eq hPrefix (by decide)]
    exact hState.releaseCache
  have hLogitsRead : result.get 73 = some (.i64 logits.root) := by
    simp only [Locals.get, hResult.paramsEq, hParams, hResult.length, Nat.reduceLT, Nat.reduceAdd,
      Nat.reduceSub, reduceIte]
    rw [Frame.local_of_take_eq hPrefix (by decide)]
    exact hState.releaseLogits
  have hRetained : ∀ entry ∈ ([(90, 0), (93, 0)] : List (Nat × UInt64)),
      result.get entry.1 = some (.i64 entry.2) := by
    intro entry hEntry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl
    all_goals simp only [Locals.get, hResult.paramsEq, hParams, hResult.length, Nat.reduceLT,
      Nat.reduceAdd, Nat.reduceSub, reduceIte, hResult.cacheOwner, hResult.logitsOwner]
  have hCacheNonzero : cache.root ≠ 0 := by
    intro hZero
    have := hCache.buffer.rootBound
    rw [hZero] at this
    contradiction
  have hLogitsNonzero : logits.root ≠ 0 := by
    intro hZero
    have := hLogits.buffer.rootBound
    rw [hZero] at this
    contradiction
  change wp «module» (PackedReleaseFilter.program 73 [90, 93] [.localGet 73, .call 65] ++ _) _ _ _ _
  apply release_spec env original initial before heap 4 cache logits logits .empty .empty
    logitsBytes result 73 [(90, 0), (93, 0)]
    (Completion.failure before heap original initial 4 cache logits (by decide) hHeap hFrame hPages hCap)
    hLogits hLogitsFresh (by intro h; contradiction) (by intro h; contradiction)
    hResult.values hLogitsRead hRetained
  · intro entry hEntry
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
    rcases hEntry with rfl | rfl <;> exact hLogitsNonzero
  · intro hReleased
    have hCacheAfter := hCache.released logits hLogits.buffer.rootBound
      (by have := hLogits.buffer.addressBound; omega) hSeparated
    change wp «module» (PackedReleaseFilter.program 28 [73, 90, 93] [.localGet 28, .call 65] ++ _) _ _ _ _
    apply release_spec env original (heap.releaseStore initial logits) before (heap.release logits) 4
      cache logits cache .empty .empty cacheBytes result 28 [(73, logits.root), (90, 0), (93, 0)]
      hReleased hCacheAfter hCacheFresh (by intro h; contradiction) (by intro h; contradiction)
      hResult.values hCacheRead
    · intro entry hEntry
      simp only [List.mem_cons] at hEntry
      rcases hEntry with rfl | hEntry
      · exact hLogitsRead
      · exact hRetained entry (by simpa only [List.mem_cons] using hEntry)
    · intro entry hEntry
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hEntry
      rcases hEntry with rfl | rfl | rfl
      · exact hCache.root_ne hSeparated
      all_goals exact hCacheNonzero
    · exact hNext result hResult hPrefix

#print axioms failureOutput_spec
end Project.Gpt2QuantizedCached.Entry
