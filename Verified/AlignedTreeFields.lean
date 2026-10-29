import Verified.AlignedSpec
import Verified.TreeMatchMemory
import Verified.TreeMatchBlocks

/-!
The split of a tree's regions when code descends into a child.  A record's regions, its slots
when borrowed and its blocks when owned, are its own region followed by those of its children,
which `recordSlots_regions`, `recordSlots_blocks`, `treeSlots_regions_read`, and
`treeSlots_blocks_read` lay out, so every region of a child is a region of the record and the
invariant passes from the record to the child.  `Ty.AlignedVal.treeChild` is the counterpart of
`treeNode_child_rep`, which gives the child's representation, and `Ty.AlignedVal.treeRecord`
gives the alignment of the record's own pointer, at which the code loads the fields.
-/

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

section

variable {mode : Mode} {store : Store Unit} {shape : TreeShape} {r : Fin shape.records}
  {p : UInt64} {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
  {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
  {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
  {children : Fin (shape.children r) → Tree shape}

/-- Every region of child `i` of a record is a region of the record. -/
theorem treeChild_regions_mem (i : Fin (shape.children r)) {c : Nat × Nat}
    (hc : c ∈ Ty.regions mode store (.tree shape)
      [.i64 (store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))]
      (children i)) :
    c ∈ Ty.regions mode store (.tree shape) [.i64 p] (Tree.node r words arrays buffers children) := by
  cases mode
  · simp only [Ty.regions, Ty.reads] at hc ⊢
    show c ∈ Node.slotRegions store p (.record (shape.recordSlots r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)))
    have hRead := treeSlots_regions_read store p (shape.fields r) shape.fieldStart
      (shape.slotWords r words) (fun i => (children i).toNode)
    simp only [Node.slotRegions, recordSlots_regions]
    refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
    exact (congrArg (fun l => c ∈ l) hRead).mpr
      (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hc⟩)
  · simp only [Ty.regions, Ty.blocks] at hc ⊢
    show c ∈ Node.blocks store p (.record (shape.recordSlots r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)))
    have hRead := treeSlots_blocks_read store p (shape.fields r) shape.fieldStart
      (shape.slotWords r words) (fun i => (children i).toNode)
    simp only [Node.blocks, recordSlots_blocks]
    refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
    exact (congrArg (fun l => c ∈ l) hRead).mpr
      (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, hc⟩)

/-- The invariant of child `i` of a record, from the record's. -/
theorem Ty.AlignedVal.treeChild
    (h : Ty.AlignedVal mode store (.tree shape) [.i64 p] (Tree.node r words arrays buffers children))
    (i : Fin (shape.children r)) :
    Ty.AlignedVal mode store (.tree shape)
      [.i64 (store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))]
      (children i) :=
  fun c hc => h c (treeChild_regions_mem i hc)

/-- The record's pointer, at which the code loads its slots, is a multiple of 8. -/
theorem Ty.AlignedVal.treeRecord
    (h : Ty.AlignedVal mode store (.tree shape) [.i64 p] (Tree.node r words arrays buffers children))
    (hp : 48 ≤ p.toNat) : p.toNat % 8 = 0 := by
  cases mode
  · exact (h (p.toNat, 8 * (shape.recordSlots r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)).length)
      (by simp only [Ty.regions, Ty.reads]; exact List.mem_cons_self ..)).1
  · have := (h (block store p) (by simp only [Ty.regions, Ty.blocks]; exact List.mem_cons_self ..)).1
    simp only [block] at this
    omega

/-- A slot's address in a record whose pointer is a multiple of 8. -/
theorem slotAddress_mod8 {p : UInt64} (hp : p.toNat % 8 = 0) (i : Nat) :
    (slotAddress p i).toNat % 8 = 0 := by
  unfold slotAddress
  refine UInt64.toUInt32_mod8 (UInt64.add_mod8 hp ?_)
  rw [UInt64.toNat_ofNat']
  simp only [Nat.reducePow]
  omega

end

end Verified
