import Project.Gpt2QuantizedCached.CachedHidden.PendingOutput

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

structure Completion (before : Heap) (initial : Store Unit) (heap : Heap) (final : Store Unit)
    (status : UInt64) (hiddenNode cacheNode : FreeNode) (hiddenBytes cacheBytes : ByteArray) : Prop where
  heapAt : heap.At final
  hidden : heap.StatusPacked final status hiddenNode hiddenBytes
  cache : heap.StatusPacked final status cacheNode cacheBytes
  frame : before.Frame initial heap final
  hiddenFresh : status = 0 → before.FreshNode hiddenNode
  cacheFresh : status = 0 → before.FreshNode cacheNode
  separated : status = 0 → regionsDisjoint hiddenNode.region cacheNode.region
  pages : final.mem.pages ≤ 65536
  capacity : final.memoryCap «module» 0 = initial.memoryCap «module» 0

theorem Completion.released {before heap : Heap} {initial store : Store Unit}
    {status : UInt64} {hidden cache : FreeNode} {hiddenBytes cacheBytes : ByteArray}
    (h : Completion before initial heap store status hidden cache hiddenBytes cacheBytes)
    (node : FreeNode) (bytes : ByteArray) (hNode : heap.OwnsPacked store node bytes)
    (hFresh : before.FreshNode node)
    (hHiddenSep : status = 0 → regionsDisjoint hidden.region node.region)
    (hCacheSep : status = 0 → regionsDisjoint cache.region node.region)
    (hHeap : (heap.release node).At (heap.releaseStore store node)) :
    Completion before initial (heap.release node) (heap.releaseStore store node)
      status hidden cache hiddenBytes cacheBytes := by
  have hRoot := hNode.buffer.rootBound
  have hRoot32 : node.root.toNat ≤ 4294967296 := by
    have := hNode.buffer.addressBound
    omega
  exact ⟨hHeap, h.hidden.released node hRoot hRoot32 hHiddenSep,
    h.cache.released node hRoot hRoot32 hCacheSep,
    h.frame.released node hRoot hRoot32 hFresh,
    h.hiddenFresh, h.cacheFresh, h.separated,
    by simpa only [Heap.releaseStore, releasedStore_pages] using h.pages,
    by simpa only [Heap.releaseStore, releasedStore_memoryCap] using h.capacity⟩

theorem Completion.trans {before middle heap : Heap} {initial intermediate final : Store Unit}
    {status : UInt64} {hidden cache : FreeNode} {hiddenBytes cacheBytes : ByteArray}
    (h : Completion middle intermediate heap final status hidden cache hiddenBytes cacheBytes)
    (hFrame : before.Frame initial middle intermediate)
    (hCap : intermediate.memoryCap «module» 0 = initial.memoryCap «module» 0) :
    Completion before initial heap final status hidden cache hiddenBytes cacheBytes :=
  ⟨h.heapAt, h.hidden, h.cache, hFrame.trans h.frame,
    fun hZero => hFrame.freshNode (h.hiddenFresh hZero),
    fun hZero => hFrame.freshNode (h.cacheFresh hZero), h.separated, h.pages, h.capacity.trans hCap⟩

theorem Completion.failure (before heap : Heap) (initial final : Store Unit) (status : UInt64)
    (hidden cache : FreeNode) (hStatus : status ≠ 0) (hHeap : heap.At final)
    (hFrame : before.Frame initial heap final) (hPages : final.mem.pages ≤ 65536)
    (hCapacity : final.memoryCap «module» 0 = initial.memoryCap «module» 0) :
    Completion before initial heap final status hidden cache .empty .empty := by
  refine ⟨hHeap, ⟨?_, fun _ => rfl⟩, ⟨?_, fun _ => rfl⟩, hFrame, ?_, ?_, ?_, hPages, hCapacity⟩
  all_goals intro h; exact False.elim (hStatus h)

#print axioms Completion.released
#print axioms Completion.trans
#print axioms Completion.failure
end Project.Gpt2QuantizedCached.CachedHidden
