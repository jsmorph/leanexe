import Project.Gpt2QuantizedCached.CachedHidden.AppendedMemory
import Project.Gpt2QuantizedCached.CachedHidden.LayerRelease

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem cacheRelease_enabled {before heap : Heap} {original initial : Store Unit}
    {hidden update cache : FreeNode} {updates : ByteArray} {output : HiddenResult}
    (h : AppendedMemory before original heap initial hidden update cache updates output) :
    PackedReleaseCounted.enabled (statusRoot output.status cache)
      [(79, statusRoot output.status hidden), (82, update.root)] = decide (output.status = 0) := by
  by_cases hZero : output.status = 0
  · have hCache := h.cache.owned hZero
    have hNonzero : cache.root ≠ 0 := by
      intro hRoot
      have := hCache.buffer.rootBound
      rw [hRoot] at this
      contradiction
    have hHiddenNe := hCache.root_ne (regionsDisjoint_symm (h.hiddenCacheSep hZero))
    have hUpdateNe := hCache.root_ne (regionsDisjoint_symm (h.updatesCacheSep hZero))
    simp [PackedReleaseCounted.enabled, statusRoot, hZero, hNonzero, hHiddenNe, hUpdateNe]
  · simp [PackedReleaseCounted.enabled, statusRoot, hZero]

theorem cacheRelease_spec (env : HostEnv Unit) (original initial : Store Unit) (before heap : Heap)
    (params : List Value) (embedding input oldUpdates : UInt64)
    (inputSize : Nat) (updates : ByteArray) (status : UInt64) (layer : Nat)
    (hidden update cache : FreeNode) (output : HiddenResult) (frame : Locals)
    (hParams : params.length = 8)
    (hMemory : AppendedMemory before original heap initial hidden update cache updates output)
    (hState : AppendedFrame params embedding input oldUpdates (statusRoot output.status hidden)
      (statusRoot output.status cache) update.root inputSize updates.size status layer output frame)
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final result,
      SelectedFrame params embedding input oldUpdates (statusRoot output.status hidden) update.root
        inputSize updates.size status layer output.hidden.size (updates.size + output.cache.size) output.status result →
      PendingOutput before original (if output.status = 0 then heap.release cache else heap)
        final output.status hidden update output.hidden (updates ++ output.cache) →
      wp «module» rest Q final result env) :
    wp «module» (cacheReleaseCode ++ rest) Q initial frame env := by
  have hEnabled := cacheRelease_enabled hMemory
  have hSource : frame.get 57 = some (.i64 (statusRoot output.status cache)) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.cacheOwner
  have hHidden : frame.get 79 = some (.i64 (statusRoot output.status hidden)) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.outputHiddenOwner
  have hUpdate : frame.get 82 = some (.i64 update.root) := by
    simpa [Locals.get, hState.paramsEq, hParams, hState.length] using hState.outputUpdatesOwner
  unfold cacheReleaseCode
  apply selectedRelease_spec env initial heap params embedding input oldUpdates
    (statusRoot output.status hidden) update.root inputSize updates.size status layer
    output.hidden.size (updates.size + output.cache.size) output.status frame cache output.cache
    (statusRoot output.status cache) 57 87 [(79, statusRoot output.status hidden), (82, update.root)]
    hParams (Or.inl rfl) hMemory.heapAt
  · intro hTaken
    have hZero : output.status = 0 := of_decide_eq_true (hEnabled ▸ hTaken)
    exact ⟨by simp [statusRoot, hZero], hMemory.cache.owned hZero⟩
  · exact hState.selected
  · exact hSource
  · intro entry hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact hHidden
    · exact hUpdate
  intro hSelected hHeap
  apply hNext _ _ hSelected
  simp only [PackedReleaseCounted.filteredHeap, PackedReleaseCounted.filteredStore, hEnabled] at hHeap ⊢
  by_cases hZero : output.status = 0
  · simp only [hZero, decide_true, ite_true] at hHeap ⊢
    simpa only [hZero] using hMemory.toPendingOutput.released cache output.cache (hMemory.cache.owned hZero)
      (hMemory.cacheFresh hZero) hMemory.hiddenCacheSep (hMemory.updatesCacheSep hZero) hHeap
  · simpa only [hZero, decide_false, Bool.false_eq_true, ite_false] using hMemory.toPendingOutput

#print axioms cacheRelease_enabled
#print axioms cacheRelease_spec
end Project.Gpt2QuantizedCached.CachedHidden
