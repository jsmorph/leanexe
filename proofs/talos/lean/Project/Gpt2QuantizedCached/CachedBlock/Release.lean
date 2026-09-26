import Project.Gpt2QuantizedCached.CachedBlock.Completion

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
open PackedReleaseMany (Owners Bindings)

theorem releaseCode_items (items : List PackedReleaseMany.Item) :
    releaseCode (items.map (·.ownerLocal)) = PackedReleaseMany.program items 190 193 65 := by
  simp only [releaseCode, PackedReleaseMany.program, List.flatMap_map, Function.comp_def]

theorem release_spec (env : HostEnv Unit) (before heap : Heap) (original initial : Store Unit)
    (params saved : List Value) (bound : Nat) (accepted : Bool) (hidden cache : FreeNode)
    (hiddenBytes cacheBytes : ByteArray) (frame : Locals) (items : List PackedReleaseMany.Item)
    (hOutput : Completion before original heap initial accepted hidden cache hiddenBytes cacheBytes)
    (hOwners : Owners before heap initial items) (hBindings : Bindings items frame)
    (hHiddenSep : accepted = true → ∀ item ∈ items, regionsDisjoint item.node.region hidden.region)
    (hCacheSep : accepted = true → ∀ item ∈ items, regionsDisjoint item.node.region cache.region)
    (hState : ResultState params saved bound accepted hidden.root cache.root frame)
    (hParams : params.length = 11)
    (Q : Assertion Unit) (rest : Program)
    (hNext : Completion before original (PackedReleaseMany.finalHeap heap items)
      (PackedReleaseMany.finalStore heap initial items) accepted hidden cache hiddenBytes cacheBytes →
      wp «module» rest Q (PackedReleaseMany.finalStore heap initial items) frame env) :
    wp «module» (releaseCode (items.map (·.ownerLocal)) ++ rest) Q initial frame env := by
  have hHidden : frame.get 190 = some (.i64 (if accepted then hidden.root else 0)) := by
    simpa only [Locals.get, hState.paramsEq, hParams, hState.length, Nat.reduceLT,
      Nat.reduceAdd, Nat.reduceSub, reduceIte] using hState.hiddenOwner
  have hCache : frame.get 193 = some (.i64 (if accepted then cache.root else 0)) := by
    simpa only [Locals.get, hState.paramsEq, hParams, hState.length, Nat.reduceLT,
      Nat.reduceAdd, Nat.reduceSub, reduceIte] using hState.cacheOwner
  rw [releaseCode_items]
  cases accepted
  · apply PackedReleaseAll.program_spec env «module» 65 initial heap before original frame items
      190 193 (typeIdx := some 65) rfl rfl hOutput.heapAt hOwners hOutput.frame
      hState.values hBindings hHidden hCache
    intro hHeap hFrame
    apply hNext
    exact ⟨hHeap, hFrame, by rw [PackedReleaseMany.finalStore_pages]; exact hOutput.pages,
      by rw [PackedReleaseMany.finalStore_memoryCap]; exact hOutput.memoryCap,
      by simp, by simp, by simp⟩
  · apply PackedReleaseMany.program_spec env «module» 65 initial heap before original frame items
      hidden cache hiddenBytes cacheBytes 190 193 (typeIdx := some 65) rfl rfl
      hOutput.heapAt hOwners.owned (hOutput.outputs rfl).1 (hOutput.outputs rfl).2
      hOwners.disjoint (hHiddenSep rfl) (hCacheSep rfl) hOutput.frame hOwners.fresh
      hState.values hBindings hHidden hCache
    intro hHeap hHiddenOutput hCacheOutput hFrame
    apply hNext
    exact ⟨hHeap, hFrame, by rw [PackedReleaseMany.finalStore_pages]; exact hOutput.pages,
      by rw [PackedReleaseMany.finalStore_memoryCap]; exact hOutput.memoryCap,
      fun _ => ⟨hHiddenOutput, hCacheOutput⟩, hOutput.fresh, hOutput.separated⟩

#print axioms release_spec
end Project.Gpt2QuantizedCached.CachedBlock
