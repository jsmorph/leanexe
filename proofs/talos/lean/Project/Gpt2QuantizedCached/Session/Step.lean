import Project.Gpt2QuantizedCached.Session.Success
import Project.Gpt2QuantizedCached.Session.Failure

namespace Project.Gpt2QuantizedCached.Session
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

theorem step (env : HostEnv Unit) (weights cache : ByteArray) (token : UInt32) (position : Nat)
    (initial : Store Unit) (heap : Heap) (weightNode oldCache : FreeNode)
    (hReady : Ready weights cache position initial heap weightNode oldCache) (hPosition : position < 128)
    (Q : Store Unit → Prop)
    (hNext : (cachedStep weights cache token position).status = 0 → ∀ next nextHeap,
      Ready weights (cachedStep weights cache token position).cache (position + 1) next nextHeap
        weightNode (Entry.outputCacheNode heap weights cache token position) → Q next) :
    let output := cachedStep weights cache token position
    TerminatesWith env «module» 61 initial
      [.i64 (UInt64.ofNat position), .i64 token.toUInt64, .i64 (UInt64.ofNat cache.size), .i64 oldCache.root,
       .i64 (UInt64.ofNat weights.size), .i64 weightNode.root]
      (fun final values =>
        values = Entry.publicValues output.status (Entry.outputCacheNode heap weights cache token position)
          (Entry.outputLogitsNode heap weights cache token position) output.cache.size output.logits.size ∧
        ByteArrayAt final.mem (statusRoot output.status (Entry.outputCacheNode heap weights cache token position)).toNat output.cache ∧
        ByteArrayAt final.mem (statusRoot output.status (Entry.outputLogitsNode heap weights cache token position)).toNat output.logits ∧
        releaseThen env oldCache.root final (fun released =>
          releaseThen env (statusRoot output.status (Entry.outputLogitsNode heap weights cache token position)) released
            (fun next => if output.status = 0 then Q next else Close env weightNode.root 0 next))) := by
  dsimp only
  have hBound : heap.top.toNat + Entry.stepBudget cache.size < 4294967296 := by
    rw [Entry.stepBudget_value, hReady.cacheSize]
    have := hReady.top
    omega
  obtain ⟨hResources, hGrowth⟩ := Entry.budget heap weights cache token position hBound
  have hPositionFit : position < UInt64.size := by change position < 18446744073709551616; omega
  have hPositionWord : (UInt64.ofNat position).toNat = position := Nat.mod_eq_of_lt hPositionFit
  have hCacheFit : cache.size < UInt64.size := by
    rw [hReady.cacheSize]
    change position * 73728 < 18446744073709551616
    omega
  have hCall := Entry.publicStep_exact env initial heap weightNode.root oldCache.root weights cache
    token.toUInt64 (UInt64.ofNat position) hReady.heapAt hReady.weightOwner.buffer.values hReady.cache_at
    hReady.weightOwner.payload_protects hReady.cache_protected hCacheFit
    (by simpa only [UInt32.toUInt32_toUInt64, hPositionWord, hReady.capacity] using hResources) hReady.pages
  simp only [UInt32.toUInt32_toUInt64, hPositionWord] at hCall
  apply hCall.mono
  rintro final values ⟨hValues, hMemory⟩
  refine ⟨hValues, hMemory.cache.values, hMemory.logits.values, ?_⟩
  by_cases hZero : (cachedStep weights cache token position).status = 0
  · simp only [hZero, statusRoot, ite_true]
    apply success_continue env weights cache position initial final heap _ weightNode oldCache _ _ _ hReady hMemory hZero
    · have hSize := (Entry.cachedStep_sizes weights cache token position).success hZero
      rw [hReady.cacheSize] at hSize
      omega
    · rw [Entry.stepBudget_value, hReady.cacheSize] at hGrowth
      have := hReady.top
      omega
    · exact hNext hZero
  · have hContinue := failure_continue env weights cache position initial final heap _ weightNode oldCache _ _ _
      hReady hMemory hZero
    simpa only [hZero, statusRoot, ite_false] using hContinue

#print axioms step
end Project.Gpt2QuantizedCached.Session
