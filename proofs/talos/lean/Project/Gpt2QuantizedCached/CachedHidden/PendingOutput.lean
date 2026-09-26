import Project.Gpt2QuantizedCached.CachedHidden.LayerPlan

namespace Project.Gpt2QuantizedCached.CachedHidden
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution

structure PendingOutput (before : Heap) (initial : Store Unit) (heap : Heap) (store : Store Unit)
    (status : UInt64) (hiddenNode updateNode : FreeNode) (hiddenBytes updateBytes : ByteArray) : Prop where
  heapAt : heap.At store
  hidden : heap.StatusPacked store status hiddenNode hiddenBytes
  updates : heap.OwnsPacked store updateNode updateBytes
  frame : before.Frame initial heap store
  hiddenFresh : status = 0 → before.FreshNode hiddenNode
  updatesFresh : before.FreshNode updateNode
  separated : status = 0 → regionsDisjoint hiddenNode.region updateNode.region
  pages : store.mem.pages ≤ 65536
  capacity : store.memoryCap «module» 0 = initial.memoryCap «module» 0

theorem PendingOutput.released {before heap : Heap} {initial store : Store Unit}
    {status : UInt64} {hidden updates : FreeNode} {hiddenBytes updateBytes : ByteArray}
    (h : PendingOutput before initial heap store status hidden updates hiddenBytes updateBytes)
    (node : FreeNode) (bytes : ByteArray) (hNode : heap.OwnsPacked store node bytes)
    (hFresh : before.FreshNode node)
    (hHiddenSep : status = 0 → regionsDisjoint hidden.region node.region)
    (hUpdatesSep : regionsDisjoint updates.region node.region)
    (hHeap : (heap.release node).At (heap.releaseStore store node)) :
    PendingOutput before initial (heap.release node) (heap.releaseStore store node)
      status hidden updates hiddenBytes updateBytes := by
  have hRoot := hNode.buffer.rootBound
  have hRoot32 : node.root.toNat ≤ 4294967296 := by
    have := hNode.buffer.addressBound
    omega
  exact ⟨hHeap, h.hidden.released node hRoot hRoot32 hHiddenSep,
    h.updates.released node hRoot hRoot32 hUpdatesSep,
    h.frame.released node hRoot hRoot32 hFresh,
    h.hiddenFresh, h.updatesFresh, h.separated,
    by simpa only [Heap.releaseStore, releasedStore_pages] using h.pages,
    by simpa only [Heap.releaseStore, releasedStore_memoryCap] using h.capacity⟩

theorem PendingOutput.trans {before middle after : Heap} {original initial final : Store Unit}
    {status : UInt64} {hidden updates : FreeNode} {hiddenBytes updateBytes : ByteArray}
    (h : PendingOutput middle initial after final status hidden updates hiddenBytes updateBytes)
    (hFrame : before.Frame original middle initial)
    (hCap : initial.memoryCap «module» 0 = original.memoryCap «module» 0) :
    PendingOutput before original after final status hidden updates hiddenBytes updateBytes :=
  ⟨h.heapAt, h.hidden, h.updates, hFrame.trans h.frame,
    fun hZero => hFrame.freshNode (h.hiddenFresh hZero), hFrame.freshNode h.updatesFresh,
    h.separated, h.pages, h.capacity.trans hCap⟩

#print axioms PendingOutput.released
#print axioms PendingOutput.trans
end Project.Gpt2QuantizedCached.CachedHidden
