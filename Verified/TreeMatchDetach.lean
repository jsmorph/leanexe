import Verified.TreeMatchBlocks
import Verified.TreeMatchMemory
import Verified.TreeMemory

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

def treeDetachStore (mode : Mode) (store : Store Unit) (p : UInt64) : Store Unit :=
  match mode with
  | .borrowed => store
  | .owned => TreeHeader.clearMask store p

theorem treeNode_detach {heap : Heap} {store : Store Unit} {shape : TreeShape} {mode : Mode}
    {p : UInt64} {words : Fin shape.words → UInt64} {children : Fin shape.children → Tree shape}
    (hAt : heap.At store) (hNode : mode.node heap store p (Tree.node words children).toNode) :
    let store' := treeDetachStore mode store p
    heap.At store' ∧ mode.header shape heap store' p ∧
      Step heap store (fun r => mode = .owned → regionsDisjoint r (block store p))
        heap store' [] ∧
      (∀ i, mode.node heap store'
        (store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val))
        (children i).toNode) ∧
      (mode = .owned → (block store' p :: (List.ofFn fun i =>
        (children i).toNode.blocks store'
          (store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val))).flatten).Pairwise
            regionsDisjoint) ∧
      (∀ i : Fin shape.fields.length, store'.mem.read64 (slotAddress p i.val) =
        store.mem.read64 (slotAddress p i.val)) ∧
      (Ty.tree shape).regions mode store' [.i64 p] (.node words children) =
        (Ty.tree shape).regions mode store [.i64 p] (.node words children) := by
  cases mode
  · exact ⟨hAt, trivial, Step.refl hAt _, treeNode_child_rep hNode, nofun, fun _ => rfl, rfl⟩
  · obtain ⟨hOwned, hApart⟩ := hNode
    obtain ⟨hHead, hSlots⟩ := hOwned
    have hLength := treeSlots_length shape.fields words (fun i => (children i).toNode)
    obtain ⟨hAt', hHeader, hSlots', hBlocks, hApart'⟩ :=
      TreeHeader.detach_spec hAt ⟨hHead, hSlots⟩ hLength hApart
    obtain ⟨hWrites, _, _, hCap⟩ := TreeHeader.clearMask_spec hAt hHead hLength
    have hBase := hHead.base
    have hAddress := hHead.address
    have hCapacity := hHead.capacity
    rw [hLength] at hCapacity
    have hRead (i : Fin shape.fields.length) :
        (TreeHeader.clearMask store p).mem.read64 (slotAddress p i.val) =
          store.mem.read64 (slotAddress p i.val) := by
      apply hWrites.read64
      right
      rw [slotAddress_toNat (by have := i.isLt; omega)]
      omega
    have hChildren : ∀ i, Mode.owned.node heap (TreeHeader.clearMask store p)
        (store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val))
        (children i).toNode := by
      intro i
      have h := treeSlots_child_owned hSlots' (List.pairwise_cons.mp hApart').2 i
      rw [hRead (fieldPosition true shape.fields i)] at h
      exact h
    have hStep := Step.ofWritesRange (region := block store p) hAt' hWrites
      (by simp only [block]; omega) (by simp only [block]; omega)
    refine ⟨hAt', hHeader, hStep.mono (fun _ hr => hr rfl) nofun,
      hChildren, ?_, hRead, ?_⟩
    · intro _
      erw [treeSlots_blocks_read] at hApart'
      simp only [Nat.zero_add] at hApart'
      convert hApart' using 1
      congr 1
      congr 1
      congr 1
      funext i
      rw [hRead (fieldPosition true shape.fields i)]
      rfl
    · change block (TreeHeader.clearMask store p) p ::
        slotsBlocks (TreeHeader.clearMask store p) p 0 (treeSlots shape.fields words
          (fun i => (children i).toNode)) = block store p :: _
      rw [block_eq hCap, hBlocks]

theorem wp_detachTree {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {shape : TreeShape} {mode : Mode} {p : UInt64} {ptr : Nat}
    {words : Fin shape.words → UInt64} {children : Fin shape.children → Tree shape}
    {rest : Program} {Q : Assertion Unit} (hAt : heap.At store)
    (hNode : mode.node heap store p (Tree.node words children).toNode)
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
