import Project.Gpt2QuantizedCached.Session.Close

namespace Project.Gpt2QuantizedCached.Session
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem success_continue (env : HostEnv Unit) (weights cache : ByteArray) (position : Nat)
    (initial final : Store Unit) (heap outputHeap : Heap) (weightNode oldCache newCache logits : FreeNode)
    (output : CachedResult) (hReady : Ready weights cache position initial heap weightNode oldCache)
    (hMemory : Entry.Completion heap initial outputHeap final output.status newCache logits output.cache output.logits)
    (hZero : output.status = 0) (hSize : output.cache.size = (position + 1) * 73728)
    (hTop : outputHeap.top.toNat ≤ 134217728 + (position + 1) * 16777216)
    (Q : Store Unit → Prop)
    (hNext : ∀ next nextHeap, Ready weights output.cache (position + 1) next nextHeap weightNode newCache → Q next) :
    releaseThen env oldCache.root final (fun released => releaseThen env logits.root released Q) := by
  have hWeights := hMemory.frame.ownsPacked hMemory.heapAt hReady.weightOwner
  have hCache := hMemory.cache.owned hZero
  have hLogits := hMemory.logits.owned hZero
  have hCacheWeights := (hMemory.cacheFresh hZero).owns_disjoint hCache.buffer.rootBound hReady.weightOwner
  have hLogitsWeights := (hMemory.logitsFresh hZero).owns_disjoint hLogits.buffer.rootBound hReady.weightOwner
  have hSeparated := hMemory.separated hZero
  have hFinish (current : Store Unit) (currentHeap : Heap)
      (hHeap : currentHeap.At current)
      (hW : currentHeap.OwnsPacked current weightNode weights)
      (hC : currentHeap.OwnsPacked current newCache output.cache)
      (hL : currentHeap.OwnsPacked current logits output.logits)
      (hBound : currentHeap.top.toNat ≤ 134217728 + (position + 1) * 16777216)
      (hP : current.mem.pages ≤ 65536) (hCap : current.memoryCap «module» 0 = 65536) :
      releaseThen env logits.root current Q := by
    have hNonzero : logits.root ≠ 0 := by
      intro h
      have hr := hL.buffer.rootBound
      rw [h] at hr
      contradiction
    rw [releaseThen, releaseThenFor, ite_eq_right hNonzero]
    apply (Release.release_owned env current currentHeap logits output.logits hHeap hL).mono
    rintro next returned ⟨rfl, rfl, hReleased⟩
    refine ⟨rfl, hNext _ (currentHeap.release logits) ?_⟩
    have hRoot := hL.buffer.rootBound
    have hRoot32 : logits.root.toNat ≤ 4294967296 := by have := hL.buffer.addressBound; omega
    exact ⟨hReleased, hW.released logits hRoot hRoot32 (regionsDisjoint_symm hLogitsWeights),
      hReady.weightSize, hSize, fun h => by omega,
      fun _ => hC.released logits hRoot hRoot32 hSeparated,
      fun _ => regionsDisjoint_symm hCacheWeights, hBound, hP, hCap⟩
  by_cases hNull : oldCache.root = 0
  · rw [releaseThen, releaseThenFor, ite_eq_left hNull]
    exact hFinish final outputHeap hMemory.heapAt hWeights hCache hLogits hTop hMemory.pages
      (hMemory.capacity.trans hReady.capacity)
  · rw [releaseThen, releaseThenFor, ite_eq_right hNull]
    have hNonzero : position ≠ 0 := fun h => hNull (hReady.empty h)
    have hOld := hMemory.frame.ownsPacked hMemory.heapAt (hReady.cache hNonzero)
    have hCacheOld := (hMemory.cacheFresh hZero).owns_disjoint hCache.buffer.rootBound (hReady.cache hNonzero)
    have hLogitsOld := (hMemory.logitsFresh hZero).owns_disjoint hLogits.buffer.rootBound (hReady.cache hNonzero)
    apply (Release.release_owned env final outputHeap oldCache cache hMemory.heapAt hOld).mono
    rintro released returned ⟨rfl, rfl, hReleased⟩
    have hRoot := hOld.buffer.rootBound
    have hRoot32 : oldCache.root.toNat ≤ 4294967296 := by have := hOld.buffer.addressBound; omega
    exact ⟨rfl, hFinish _ (outputHeap.release oldCache) hReleased
      (hWeights.released oldCache hRoot hRoot32 (hReady.separated hNonzero))
      (hCache.released oldCache hRoot hRoot32 hCacheOld)
      (hLogits.released oldCache hRoot hRoot32 hLogitsOld) hTop hMemory.pages
      (hMemory.capacity.trans hReady.capacity)⟩

#print axioms success_continue
end Project.Gpt2QuantizedCached.Session
