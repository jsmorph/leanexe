import Verified.TreeMatchBlocks
import Verified.TreeMatchMemory
import Verified.TreeMemory

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

def treeDetachStore (mode : Mode) (store : Store Unit) (p : UInt64) : Store Unit :=
  match mode with
  | .borrowed => store
  | .owned => TreeHeader.clearMask store p

theorem treeNode_detach {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {children : Fin (shape.children r) → Tree shape}
    (hAt : heap.At store) (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode) :
    let store' := treeDetachStore mode store p
    heap.At store' ∧ mode.header shape r heap store' p ∧
      Step heap store (fun b => mode = .owned → regionsDisjoint b (block store p))
        heap store' [] ∧
      (∀ i, mode.node heap store'
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))
        (children i).toNode) ∧
      (mode = .owned → (block store' p :: (List.ofFn fun i =>
        (children i).toNode.blocks store'
          (store.mem.read64 (slotAddress p
            (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))).flatten).Pairwise
            regionsDisjoint) ∧
      (∀ i : Fin (shape.width r), store'.mem.read64 (slotAddress p i.val) =
        store.mem.read64 (slotAddress p i.val)) ∧
      (Ty.tree shape).regions mode store' [.i64 p] (.node r words arrays buffers children) =
        (Ty.tree shape).regions mode store [.i64 p] (.node r words arrays buffers children) := by
  have hBound (i : Fin (shape.children r)) :
      shape.fieldStart + (fieldPosition true (shape.fields r) i).val < shape.width r :=
    shape.fieldSlot_lt r true i
  cases mode
  · exact ⟨hAt, trivial, Step.refl hAt _, treeNode_child_rep hNode, nofun, fun _ => rfl, rfl⟩
  · obtain ⟨hOwned, hApart⟩ := hNode
    obtain ⟨hHead, hSlots⟩ := hOwned
    have hLength :=
      shape.recordSlots_length r (shape.slotWords r words) (fun i => (children i).toNode)
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
    have hFieldSlots : SlotsOwned heap (TreeHeader.clearMask store p) p shape.fieldStart
        (treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode)) := by
      have hAll : SlotsOwned heap (TreeHeader.clearMask store p) p 0 (shape.tagSlots r ++
          treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode)) :=
        hSlots'
      have := ((SlotsOwned.append_iff _ _ _).mp hAll).2
      rwa [Nat.zero_add, ← shape.fieldStart_tagSlots r] at this
    have hFieldApart : (slotsBlocks (TreeHeader.clearMask store p) p shape.fieldStart
        (treeSlots (shape.fields r) (shape.slotWords r words)
          (fun i => (children i).toNode))).Pairwise regionsDisjoint := by
      have := (List.pairwise_cons.mp hApart').2
      change (slotsBlocks _ p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) (shape.slotWords r words)
          (fun i => (children i).toNode))).Pairwise regionsDisjoint at this
      rwa [slotsBlocks_append, tagSlots_blocks, List.nil_append, Nat.zero_add,
        ← shape.fieldStart_tagSlots r] at this
    have hChildren : ∀ i, Mode.owned.node heap (TreeHeader.clearMask store p)
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))
        (children i).toNode := by
      intro i
      have h := treeSlots_child_owned hFieldSlots hFieldApart i
      rw [hReadNat _ (hBound i)] at h
      exact h
    have hFieldBlocks : slotsBlocks (TreeHeader.clearMask store p) p 0
        (shape.recordSlots r (shape.slotWords r words) (fun i => (children i).toNode)) =
        (List.ofFn fun i => (children i).toNode.blocks (TreeHeader.clearMask store p)
          (store.mem.read64 (slotAddress p
            (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))).flatten := by
      change slotsBlocks _ p 0 (shape.tagSlots r ++ _) = _
      rw [slotsBlocks_append, tagSlots_blocks, List.nil_append, Nat.zero_add,
        ← shape.fieldStart_tagSlots r]
      erw [treeSlots_blocks_read]
      congr 2
      funext i
      rw [hReadNat _ (hBound i)]
    have hStep := Step.ofWritesRange (region := block store p) hAt' hWrites
      (by simp only [block]; omega) (by simp only [block]; omega)
    refine ⟨hAt', hHeader, hStep.mono (fun _ hr => hr rfl) nofun,
      hChildren, ?_, fun i => hReadNat i.val i.isLt, ?_⟩
    · intro _
      have hAll := hApart'
      change (block _ p :: slotsBlocks _ p 0
        (shape.recordSlots r (shape.slotWords r words) (fun i => (children i).toNode))).Pairwise _
        at hAll
      rwa [hFieldBlocks] at hAll
    · change block (TreeHeader.clearMask store p) p ::
        slotsBlocks (TreeHeader.clearMask store p) p 0
          (shape.recordSlots r (shape.slotWords r words) (fun i => (children i).toNode)) =
        block store p :: _
      rw [block_eq hCap, hBlocks]

theorem wp_detachTree {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode} {p : UInt64}
    {ptr : Nat} {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {children : Fin (shape.children r) → Tree shape} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (hPtr : s.get ptr = some (.i64 p))
    (hNext : wp m rest Q (treeDetachStore mode store p) s host) :
    wp m ((if mode = .owned then headerStore ptr 8 [.constI64 0] else []) ++ rest)
      Q store s host := by
  cases mode
  · exact hNext
  · have hBase := hNode.1.1.base
    have hBelow := hNode.1.1.below
    have hAddress := hNode.1.1.address
    have hRoom : (p - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
      rw [headerAddress_toNat (by change 8 ≤ p.toNat; omega) (by omega)]
      change p.toNat - 8 + 8 ≤ store.mem.pages * 65536
      have := hAt.top
      omega
    exact wp_headerStoreWord hPtr hRoom hNext

end Verified
