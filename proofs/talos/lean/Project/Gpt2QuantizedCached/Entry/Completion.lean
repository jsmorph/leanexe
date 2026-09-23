import Project.Gpt2QuantizedCached.Entry.Result

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

structure Completion (before : Heap) (initial : Store Unit) (heap : Heap) (final : Store Unit)
    (status : UInt64) (cacheNode logitsNode : FreeNode) (cacheBytes logitsBytes : ByteArray) : Prop where
  heapAt : heap.At final
  cache : heap.StatusPacked final status cacheNode cacheBytes
  logits : heap.StatusPacked final status logitsNode logitsBytes
  frame : before.Frame initial heap final
  cacheFresh : status = 0 → before.FreshNode cacheNode
  logitsFresh : status = 0 → before.FreshNode logitsNode
  separated : status = 0 → regionsDisjoint cacheNode.region logitsNode.region
  pages : final.mem.pages ≤ 65536
  capacity : final.memoryCap «module» 0 = initial.memoryCap «module» 0

theorem Completion.released {before heap : Heap} {initial store : Store Unit}
    {status : UInt64} {cache logits : FreeNode} {cacheBytes logitsBytes : ByteArray}
    (h : Completion before initial heap store status cache logits cacheBytes logitsBytes)
    (node : FreeNode) (bytes : ByteArray) (hNode : heap.OwnsPacked store node bytes)
    (hFresh : before.FreshNode node)
    (hCacheSep : status = 0 → regionsDisjoint cache.region node.region)
    (hLogitsSep : status = 0 → regionsDisjoint logits.region node.region)
    (hHeap : (heap.release node).At (heap.releaseStore store node)) :
    Completion before initial (heap.release node) (heap.releaseStore store node)
      status cache logits cacheBytes logitsBytes := by
  have hRoot := hNode.buffer.rootBound
  have hRoot32 : node.root.toNat ≤ 4294967296 := by
    have := hNode.buffer.addressBound
    omega
  exact ⟨hHeap, h.cache.released node hRoot hRoot32 hCacheSep,
    h.logits.released node hRoot hRoot32 hLogitsSep,
    h.frame.released node hRoot hRoot32 hFresh,
    h.cacheFresh, h.logitsFresh, h.separated,
    by simpa only [Heap.releaseStore, releasedStore_pages] using h.pages,
    by simpa only [Heap.releaseStore, releasedStore_memoryCap] using h.capacity⟩

theorem Completion.trans {before middle heap : Heap} {initial intermediate final : Store Unit}
    {status : UInt64} {cache logits : FreeNode} {cacheBytes logitsBytes : ByteArray}
    (h : Completion middle intermediate heap final status cache logits cacheBytes logitsBytes)
    (hFrame : before.Frame initial middle intermediate)
    (hCap : intermediate.memoryCap «module» 0 = initial.memoryCap «module» 0) :
    Completion before initial heap final status cache logits cacheBytes logitsBytes :=
  ⟨h.heapAt, h.cache, h.logits, hFrame.trans h.frame,
    fun hZero => hFrame.freshNode (h.cacheFresh hZero),
    fun hZero => hFrame.freshNode (h.logitsFresh hZero), h.separated, h.pages, h.capacity.trans hCap⟩

theorem Completion.failure (before heap : Heap) (initial final : Store Unit) (status : UInt64)
    (cache logits : FreeNode) (hStatus : status ≠ 0) (hHeap : heap.At final)
    (hFrame : before.Frame initial heap final) (hPages : final.mem.pages ≤ 65536)
    (hCapacity : final.memoryCap «module» 0 = initial.memoryCap «module» 0) :
    Completion before initial heap final status cache logits .empty .empty := by
  refine ⟨hHeap, ⟨?_, fun _ => rfl⟩, ⟨?_, fun _ => rfl⟩, hFrame, ?_, ?_, ?_, hPages, hCapacity⟩
  all_goals intro h; exact False.elim (hStatus h)

#print axioms Completion.released
#print axioms Completion.trans
#print axioms Completion.failure
end Project.Gpt2QuantizedCached.Entry
