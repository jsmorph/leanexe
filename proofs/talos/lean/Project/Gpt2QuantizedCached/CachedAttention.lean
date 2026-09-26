import Project.Gpt2QuantizedCached.FP32Region
import Project.Gpt2CachedStep.CachedAttention.Spec

namespace Project.Gpt2QuantizedCached.CachedAttention
open Wasm Project.Runtime Project.ProofKit PackedMemory Project.EulerRiemann.Execution
open Project.Gpt2CachedStep.CachedAttention

theorem cachedAttention_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position : Nat)
    (hHeap : heap.At initial)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache) (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hQkvProtected : heap.Protects qkvPtr.toNat (qkvPtr.toNat + qkv.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hResources : Resources heap position (initial.memoryCap Project.Gpt2CachedStep.«module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := LeanExe.Models.Gpt2.cachedAttention cache qkv layer position
    TerminatesWith env Project.Gpt2QuantizedCached.«module» 50 initial
      [.i64 (UInt64.ofNat position), .i64 (UInt64.ofNat layer),
       .i64 (UInt64.ofNat qkv.size), .i64 qkvPtr, .i64 qkvOwner,
       .i64 (UInt64.ofNat cache.size), .i64 cachePtr, .i64 cacheOwner]
      (fun final values =>
        values = [.i64 (UInt64.ofNat output.size),
          .i64 (outputNode heap position).root, .i64 (outputNode heap position).root] ∧
        (finalHeap heap position).At final ∧
        (finalHeap heap position).OwnsPacked final (outputNode heap position) output ∧
        heap.Frame initial (finalHeap heap position) final ∧
        final.mem.pages ≤ 65536 ∧
        final.memoryCap Project.Gpt2CachedStep.«module» 0 = initial.memoryCap Project.Gpt2CachedStep.«module» 0) := by
  exact Project.FunctionRegion.terminatesWith FP32Region.shift 29
    (by simp [FP32Region.domain]) (Project.Gpt2CachedStep.CachedAttention.Spec.cachedAttention_exact
      env initial heap cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position hHeap hCache hQkv hCacheProtected hQkvProtected hLayer hPosition hCacheSize hQkvSize hResources hPages)

#print axioms cachedAttention_exact
end Project.Gpt2QuantizedCached.CachedAttention
