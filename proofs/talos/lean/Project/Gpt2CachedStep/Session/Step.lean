import Project.Gpt2CachedStep.Session.State

namespace Project.Gpt2CachedStep.Session
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution LeanExe.Models.Gpt2

theorem step (env : HostEnv Unit) (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (initial : Store Unit) (heap : Heap) (weightNode oldCache : FreeNode)
    (hReady : Ready weights cache position initial heap weightNode oldCache)
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (Q : Store Unit → Prop)
    (hNext : ∀ next nextHeap,
      Ready weights (cachedStep weights cache token position).cache (position + 1) next nextHeap
        weightNode (Entry.cacheNode heap position cache.size) → Q next) :
    let output := cachedStep weights cache token position
    TerminatesWith env «module» 38 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64, .i64 (UInt64.ofNat cache.size), .i64 oldCache.root,
       .i64 (UInt64.ofNat weights.size), .i64 weightNode.root]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.logits.size), .i64 (Entry.logitsNode heap position cache.size).root,
          .i64 (UInt64.ofNat output.cache.size), .i64 (Entry.cacheNode heap position cache.size).root] ∧
        ByteArrayAt final.mem (Entry.cacheNode heap position cache.size).root.toNat output.cache ∧
        releaseThen env oldCache.root final (fun released =>
          ByteArrayAt released.mem (Entry.logitsNode heap position cache.size).root.toNat output.logits ∧
          TerminatesWith env «module» 42 released [.i64 (Entry.logitsNode heap position cache.size).root]
            (fun next returned => returned = [] ∧ Q next))) := by
  dsimp only
  have hValid : Entry.Valid weights cache token position :=
    ⟨hReady.weightSize, hToken, hPosition, hReady.cacheSize⟩
  obtain ⟨hResources, hGrowth⟩ := Entry.budget heap position cache.size hPosition hReady.cacheSize (by
    have := hReady.top
    omega)
  have hResources' : Entry.Resources heap position cache.size (initial.memoryCap «module» 0) := by
    rw [hReady.capacity]
    exact hResources
  have hSize : (cachedStep weights cache token position).cache.size = (position + 1) * 73728 := by
    rw [Entry.cachedStep_valid hValid, CachedHidden.Spec.cachedHidden_cache_size, hReady.cacheSize]
    omega
  refine (Entry.cachedStep_accepted env initial heap weightNode.root oldCache.root weights cache token position
    hReady.heapAt hReady.weightOwner.buffer.values hReady.cache_at hReady.weightOwner.payload_protects
    hReady.cache_protected hValid hResources' hReady.pages).mono ?_
  rintro final values ⟨hValues, hFinalHeap, hCache, hLogits, hFrame, hSeparated,
    hCacheFresh, hLogitsFresh, hPages, hCap⟩
  have hWeights := hFrame.ownsPacked hFinalHeap hReady.weightOwner
  have hCacheWeights := hCacheFresh.owns_disjoint hCache.buffer.rootBound hReady.weightOwner
  have hLogitsWeights := hLogitsFresh.owns_disjoint hLogits.buffer.rootBound hReady.weightOwner
  have hTop : (Entry.finalHeap heap position cache.size).top.toNat ≤ 536870912 + (position + 1) * 16777216 := by
    have := hReady.top
    omega
  have hFinish (current : Store Unit) (currentHeap : Heap)
      (hHeap : currentHeap.At current)
      (hW : currentHeap.OwnsPacked current weightNode weights)
      (hC : currentHeap.OwnsPacked current (Entry.cacheNode heap position cache.size)
        (cachedStep weights cache token position).cache)
      (hL : currentHeap.OwnsPacked current (Entry.logitsNode heap position cache.size)
        (cachedStep weights cache token position).logits)
      (hBound : currentHeap.top.toNat ≤ 536870912 + (position + 1) * 16777216)
      (hP : current.mem.pages ≤ 65536) (hCap : current.memoryCap «module» 0 = 65536) :
      ByteArrayAt current.mem (Entry.logitsNode heap position cache.size).root.toNat
        (cachedStep weights cache token position).logits ∧
      TerminatesWith env «module» 42 current [.i64 (Entry.logitsNode heap position cache.size).root]
        (fun next returned => returned = [] ∧ Q next) := by
    refine ⟨hL.buffer.values, (Release.release_owned env current currentHeap _ _ hHeap hL).mono ?_⟩
    rintro next returned ⟨rfl, rfl, hReleased⟩
    refine ⟨rfl, hNext _ (currentHeap.release (Entry.logitsNode heap position cache.size)) ?_⟩
    have hRoot := hL.buffer.rootBound
    have hRoot32 : (Entry.logitsNode heap position cache.size).root.toNat ≤ 4294967296 := by
      have := hL.buffer.addressBound
      omega
    exact ⟨hReleased, hW.released _ hRoot hRoot32 (regionsDisjoint_symm hLogitsWeights),
      hReady.weightSize, hSize, fun h => by omega,
      fun _ => hC.released _ hRoot hRoot32 hSeparated,
      fun _ => regionsDisjoint_symm hCacheWeights, hBound, hP, hCap⟩
  refine ⟨hValues, hCache.buffer.values, ?_⟩
  by_cases hNull : oldCache.root = 0
  · rw [releaseThen, releaseThenFor, ite_eq_left hNull]
    exact hFinish final _ hFinalHeap hWeights hCache hLogits hTop hPages (hCap.trans hReady.capacity)
  · rw [releaseThen, releaseThenFor, ite_eq_right hNull]
    have hNonzero : position ≠ 0 := fun h => hNull (hReady.empty h)
    have hOld := hFrame.ownsPacked hFinalHeap (hReady.cache hNonzero)
    have hCacheOld := hCacheFresh.owns_disjoint hCache.buffer.rootBound (hReady.cache hNonzero)
    have hLogitsOld := hLogitsFresh.owns_disjoint hLogits.buffer.rootBound (hReady.cache hNonzero)
    refine (Release.release_owned env final _ oldCache cache hFinalHeap hOld).mono ?_
    rintro released returned ⟨rfl, rfl, hReleased⟩
    have hRoot := hOld.buffer.rootBound
    have hRoot32 : oldCache.root.toNat ≤ 4294967296 := by
      have := hOld.buffer.addressBound
      omega
    exact ⟨rfl, hFinish _ ((Entry.finalHeap heap position cache.size).release oldCache) hReleased
      (hWeights.released oldCache hRoot hRoot32 (hReady.separated hNonzero))
      (hCache.released oldCache hRoot hRoot32 hCacheOld)
      (hLogits.released oldCache hRoot hRoot32 hLogitsOld)
      (by simpa only [Heap.release_top] using hTop) hPages (hCap.trans hReady.capacity)⟩

#print axioms step

end Project.Gpt2CachedStep.Session
