import Verified.Tree
import LeanExe.Pipeline.Records

namespace Verified

open Wasm LeanExe.Pipeline

def TreeHeader.Owned (shape : TreeShape) (r : Fin shape.records) (heap : Heap) (store : Store Unit)
    (p : UInt64) : Prop :=
  ∃ words : List UInt64, words.length = shape.width r ∧
    NodeOwned heap store p (.record (words.map Slot.word))

theorem wordSlots_mask (words : List UInt64) : maskOf (words.map Slot.word) = 0 := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    change 2 * maskOf (rest.map Slot.word) + 0 = 0
    rw [ih]
    rfl

theorem wordSlots_blocks (store : Store Unit) (p : UInt64) (words : List UInt64) :
    ∀ i, slotsBlocks store p i (words.map Slot.word) = [] := by
  induction words with
  | nil => intros; rfl
  | cons word rest ih => intro i; exact ih (i + 1)

theorem TreeHeader.Owned.region {shape : TreeShape} {r : Fin shape.records} {heap : Heap}
    {store : Store Unit} {p : UInt64} (h : Owned shape r heap store p) :
    heap.Region (block store p) := by
  obtain ⟨words, _, hHead, _⟩ := h
  exact hHead.region

theorem TreeHeader.Owned.mask {shape : TreeShape} {r : Fin shape.records} {heap : Heap}
    {store : Store Unit} {p : UInt64} (h : Owned shape r heap store p) :
    store.mem.read64 (p - 8).toUInt32 = 0 := by
  obtain ⟨words, _, hHead, _⟩ := h
  exact hHead.mask.trans (wordSlots_mask words)

theorem TreeHeader.Owned.capacity {shape : TreeShape} {r : Fin shape.records} {heap : Heap}
    {store : Store Unit} {p : UInt64} (h : Owned shape r heap store p) :
    8 * shape.width r ≤ capacityAt store p := by
  obtain ⟨words, hLength, hHead, _⟩ := h
  simpa only [List.length_map, hLength] using hHead.capacity

theorem TreeHeader.Owned.frame {shape : TreeShape} {r : Fin shape.records} {heap heap' : Heap}
    {store store' : Store Unit} {p : UInt64} (h : Owned shape r heap store p)
    (hBytes : ∀ a, p.toNat - 48 ≤ a → a < p.toNat + capacityAt store p →
      store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store p)) (hAt : heap'.At store') :
    Owned shape r heap' store' p ∧ capacityAt store' p = capacityAt store p := by
  obtain ⟨words, hLength, hHead, hSlots⟩ := h
  have hBlocks : Node.blocks store p (.record (words.map Slot.word)) = [block store p] := by
    simp only [Node.blocks, wordSlots_blocks]
  obtain ⟨hNode, _⟩ := NodeOwned.frame hAt p (.record (words.map Slot.word)) ⟨hHead, hSlots⟩
    (fun b hb => by
      rw [hBlocks, List.mem_singleton] at hb
      subst b
      refine ⟨fun a hLow hHigh => hBytes a hLow ?_, hRegion⟩
      have := hHead.base
      simp only [block] at hHigh
      omega)
  exact ⟨⟨words, hLength, hNode⟩,
    (hHead.frame hBytes hRegion).2⟩

instance {shape : TreeShape} {r : Fin shape.records} : Represent (TreeHeader shape r) where
  width _ := 1
  borrowed _ _ vs _ := ∃ p, vs = [.i64 p]
  owned heap store vs _ := ∃ p, vs = [.i64 p] ∧ TreeHeader.Owned shape r heap store p
  blocks store vs _ := match vs with
    | [.i64 p] => [block store p]
    | _ => []
  reads _ _ _ := []
  moves _ _ _ := []

instance {shape : TreeShape} {r : Fin shape.records} : Represent (Moved (TreeHeader shape r)) where
  width _ := 1
  borrowed heap store vs x := Represent.owned heap store vs x.val
  owned heap store vs x := Represent.owned heap store vs x.val
  blocks store vs x := Represent.blocks store vs x.val
  reads _ _ _ := []
  moves _ vs _ := match vs with
    | [.i64 p] => [p]
    | _ => []

#print axioms TreeHeader.Owned.frame

end Verified
