import Project.Gpt2CachedStep.CachedAttention.FrozenBody

namespace Project.Gpt2CachedStep.Frozen.CachedAttention.Spec
open Wasm Project.ProofKit PackedMemory Project.EulerRiemann.Execution

@[simp] theorem cachedAttention_size (cache qkv : ByteArray) (layer position : Nat) :
    (LeanExe.Models.Gpt2.cachedAttention cache qkv layer position).size = 3072 := by
  rw [cachedAttention_eq]
  exact mixed_size ..

theorem cachedAttention_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position : Nat)
    (hHeap : heap.At initial)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache) (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hCacheProtected : heap.Protects cachePtr.toNat (cachePtr.toNat + cache.size))
    (hQkvProtected : heap.Protects qkvPtr.toNat (qkvPtr.toNat + qkv.size))
    (hLayer : layer < 12) (hPosition : position < 128)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size)
    (hResources : Resources heap position (initial.memoryCap «module» 0))
    (hPages : initial.mem.pages ≤ 65536) :
    let output := LeanExe.Models.Gpt2.cachedAttention cache qkv layer position
    TerminatesWith env «module» 29 initial
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
        final.memoryCap «module» 0 = initial.memoryCap «module» 0) := by
  dsimp only
  refine TerminatesWith.of_wp_entry_for (f := func29Def) rfl ?_
  change wp «module» func29 _ initial
    { params := parameters cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position
      locals := List.replicate 114 (.i64 0) } env
  apply body_spec env initial heap cacheOwner qkvOwner cachePtr qkvPtr cache qkv layer position _
    hHeap hCache hQkv hCacheProtected hQkvProtected hLayer hPosition hCacheSize hQkvSize
    hResources hPages rfl (by simp) rfl (I64Values.replicate _ _)
  intro final result hValues hFinalHeap hOutput hFrame hFinalPages hCapacity
  have hPost := And.intro hFinalHeap (And.intro hOutput (And.intro hFrame (And.intro hFinalPages hCapacity)))
  simpa [func29Def, Function.numParams, hValues, cachedAttention_size] using hPost

#print axioms cachedAttention_exact

end Project.Gpt2CachedStep.Frozen.CachedAttention.Spec
