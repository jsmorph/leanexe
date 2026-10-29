import Verified.TreeMatchBlocks
import Verified.TreeMatchMemory
import Verified.TreeMemory
import Verified.TreeHeapFields

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

def treeDetachStore (mode : Mode) (store : Store Unit) (p : UInt64) : Store Unit :=
  match mode with
  | .borrowed => store
  | .owned => TreeHeader.clearMask store p

theorem treeNode_detach {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (hAt : heap.At store)
    (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode) :
    let store' := treeDetachStore mode store p
    heap.At store' ∧ mode.header shape r heap store' p ∧
      Step heap store (fun b => mode = .owned → regionsDisjoint b (block store p))
        heap store' [] ∧
      (∀ i, mode.node heap store'
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))
        (children i).toNode) ∧
      (∀ i, mode.array heap store'
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i)))
        ((shape.arrayElem r i).words (arrays i))) ∧
      (∀ i, RecordBuffer heap store'
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapBufferSlot (shape.kinds r) i)))
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapBufferSlot (shape.kinds r) i + 1)))
        (buffers i)) ∧
      (mode = .owned → (block store' p :: ((List.ofFn fun i =>
        (children i).toNode.blocks store'
          (store.mem.read64 (slotAddress p
            (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))).flatten ++
        ((List.ofFn fun i => [block store'
          (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
            heapArraySlot (shape.kinds r) i)))]).flatten ++
        (List.ofFn fun i => Bytes.regions store'
          (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
            heapBufferSlot (shape.kinds r) i)))).flatten))).Pairwise regionsDisjoint) ∧
      (∀ i : Fin (shape.width r), store'.mem.read64 (slotAddress p i.val) =
        store.mem.read64 (slotAddress p i.val)) ∧
      (Ty.tree shape).regions mode store' [.i64 p] (.node r words arrays buffers children) =
        (Ty.tree shape).regions mode store [.i64 p] (.node r words arrays buffers children) := by
  have hBound (i : Fin (shape.children r)) :
      shape.fieldStart + (fieldPosition true (shape.fields r) i).val < shape.width r :=
    shape.fieldSlot_lt r true i
  cases mode
  · exact ⟨hAt, trivial, Step.refl hAt _, treeNode_child_rep hNode, treeNode_array_rep hNode,
      treeNode_recordBuffer hNode, nofun, fun _ => rfl, rfl⟩
  · obtain ⟨hOwned, hApart⟩ := hNode
    obtain ⟨hHead, hSlots⟩ := hOwned
    have hLength := shape.recordSlots_length r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)
    obtain ⟨hAt', hHeader, hSlots', hBlocks, hApart'⟩ :=
      TreeHeader.detach_spec hAt ⟨hHead, hSlots⟩ hLength hApart
    obtain ⟨hWrites, _, _, hCap⟩ := TreeHeader.clearMask_spec hAt hHead hLength
    have hBase := hHead.base
    have hAddress := hHead.address
    have hCapacity := hHead.capacity
    rw [hLength] at hCapacity
    have hReadNat (k : Nat) (hk : k < shape.width r) :
        (TreeHeader.clearMask store p).mem.read64 (slotAddress p k) =
          store.mem.read64 (slotAddress p k) := by
      apply hWrites.read64
      right
      rw [slotAddress_toNat (by omega)]
      omega
    have hAll : SlotsOwned heap (TreeHeader.clearMask store p) p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) := hSlots'
    have hFieldSlots : SlotsOwned heap (TreeHeader.clearMask store p) p shape.fieldStart
        (treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode)) := by
      have hPrefix := ((SlotsOwned.append_iff _ _ _).mp hAll).1
      have := ((SlotsOwned.append_iff _ _ _).mp hPrefix).2
      rwa [Nat.zero_add, ← shape.fieldStart_tagSlots r] at this
    have hRecordApart := (List.pairwise_cons.mp hApart').2
    change (slotsBlocks _ p 0 (shape.recordSlots r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode))).Pairwise
        regionsDisjoint at hRecordApart
    rw [recordSlots_blocks] at hRecordApart
    have hFieldApart := (List.pairwise_append.mp hRecordApart).1
    have hChildren : ∀ i, Mode.owned.node heap (TreeHeader.clearMask store p)
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))
        (children i).toNode := by
      intro i
      have h := treeSlots_child_owned hFieldSlots hFieldApart i
      rw [hReadNat _ (hBound i)] at h
      exact h
    have hArrays : ∀ i, Mode.owned.array heap (TreeHeader.clearMask store p)
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i)))
        ((shape.arrayElem r i).words (arrays i)) := by
      intro i
      have h := recordSlots_array_owned hSlots' i
      rw [hReadNat _ (shape.heapArraySlot_lt_width r i)] at h
      exact h
    have hBufferAt : ∀ i, RecordBuffer heap (TreeHeader.clearMask store p)
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapBufferSlot (shape.kinds r) i)))
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapBufferSlot (shape.kinds r) i + 1)))
        (buffers i) := by
      intro i
      have h := recordSlots_recordBuffer_owned hSlots' i
      have hLt := shape.heapBufferSlot_lt_width r i
      rw [hReadNat _ (by omega), hReadNat _ hLt] at h
      exact h
    have hFieldBlocks : (slotsBlocks (TreeHeader.clearMask store p) p 0
        (shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
          (fun i => (children i).toNode))).Perm
        ((List.ofFn fun i => (children i).toNode.blocks (TreeHeader.clearMask store p)
          (store.mem.read64 (slotAddress p
            (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))).flatten ++
        ((List.ofFn fun i => [block (TreeHeader.clearMask store p)
          (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
            heapArraySlot (shape.kinds r) i)))]).flatten ++
        (List.ofFn fun i => Bytes.regions (TreeHeader.clearMask store p)
          (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
            heapBufferSlot (shape.kinds r) i)))).flatten)) := by
      rw [recordSlots_blocks]
      erw [treeSlots_blocks_read]
      refine List.Perm.append (List.Perm.of_eq ?_)
        ((heapSlots_blocks_perm _ p (shape.kinds r) _ _ _).trans (List.Perm.of_eq ?_))
      · congr 2
        funext i
        rw [hReadNat _ (hBound i)]
      · congr 2
        · congr 1
          funext i
          rw [hReadNat _ (shape.heapArraySlot_lt_width r i)]
        · congr 1
          funext i
          have hLt := shape.heapBufferSlot_lt_width r i
          rw [hReadNat _ (by omega), (hBufferAt i).blocks]
    have hStep := Step.ofWritesRange (region := block store p) hAt' hWrites
      (by simp only [block]; omega) (by simp only [block]; omega)
    refine ⟨hAt', hHeader, hStep.mono (fun _ hr => hr rfl) nofun,
      hChildren, hArrays, hBufferAt, ?_, fun i => hReadNat i.val i.isLt, ?_⟩
    · intro _
      have hList := hApart'
      change (block _ p :: slotsBlocks _ p 0
        (shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
          (fun i => (children i).toNode))).Pairwise _ at hList
      exact hList.perm (hFieldBlocks.cons _) (fun h => regionsDisjoint_symm h)
    · change block (TreeHeader.clearMask store p) p ::
        slotsBlocks (TreeHeader.clearMask store p) p 0
          (shape.recordSlots r (shape.slotWords r words) (shape.arrayWords r arrays) buffers
            (fun i => (children i).toNode)) =
        block store p :: _
      rw [block_eq hCap, hBlocks]

end Verified
