import Verified.TreeHeader

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def recordWords (store : Store Unit) (p : UInt64) : Nat → Nat → List UInt64
  | _, 0 => []
  | i, n + 1 => store.mem.read64 (slotAddress p i) :: recordWords store p (i + 1) n

theorem recordWords_length (store : Store Unit) (p : UInt64) (n : Nat) :
    ∀ i, (recordWords store p i n).length = n := by
  induction n with
  | zero => intros; rfl
  | succ n ih => intro i; simp only [recordWords, List.length_cons, ih]

theorem recordWords_owned (heap : Heap) (store : Store Unit) (p : UInt64) (n : Nat) :
    ∀ i, SlotsOwned heap store p i ((recordWords store p i n).map Slot.word) := by
  induction n with
  | zero => intros; trivial
  | succ n ih => intro i; exact ⟨rfl, ih (i + 1)⟩

def TreeHeader.clearMask (store : Store Unit) (p : UInt64) : Store Unit :=
  { store with mem := store.mem.write64 (p - 8).toUInt32 0 }

theorem TreeHeader.clearMask_spec {shape : TreeShape} {r : Fin shape.records} {heap : Heap}
    {store : Store Unit} {p : UInt64} {slots : List Slot}
    (hHeap : heap.At store) (h : RecordHeader heap store p slots)
    (hLength : slots.length = shape.width r) :
    Memory.WritesRange store (clearMask store p) (p.toNat - 8) p.toNat ∧
      heap.At (clearMask store p) ∧
      Owned shape r heap (clearMask store p) p ∧
      capacityAt (clearMask store p) p = capacityAt store p := by
  have hBase := h.base
  have hAddress := h.address
  have hAddr : (p - 8).toUInt32.toNat = p.toNat - 8 :=
    headerAddress_toNat (by change 8 ≤ p.toNat; omega) (by omega)
  have hWrites : Memory.WritesRange store (clearMask store p) (p.toNat - 8) p.toNat :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [hAddr]) (by rw [hAddr]; omega)
  have hRead (back : UInt64) (h16 : 16 ≤ back.toNat) (h48 : back.toNat ≤ 48) :
      (clearMask store p).mem.read64 (p - back).toUInt32 =
        store.mem.read64 (p - back).toUInt32 := by
    apply hWrites.read64
    left
    rw [headerAddress_toNat (by omega) (by omega)]
    omega
  have hCapacity : capacityAt (clearMask store p) p = capacityAt store p := by
    unfold capacityAt
    rw [hRead 32 (by decide) (by decide)]
  let words := recordWords (clearMask store p) p 0 slots.length
  have hWords : (words.map Slot.word).length = slots.length := by
    simp only [List.length_map, words, recordWords_length]
  have hHead : RecordHeader heap (clearMask store p) p (words.map Slot.word) := by
    refine ⟨hBase, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hRead 48 (by decide) (by decide)]; exact h.magic
    · rw [hRead 40 (by decide) (by decide)]; exact h.count
    · rw [hRead 24 (by decide) (by decide)]; exact h.kind
    · rw [hRead 16 (by decide) (by decide), hWords]; exact h.width
    · rw [wordSlots_mask]
      exact Memory.read64_write64 ..
    · rw [hWords]; exact h.short
    · rw [hWords, hCapacity]; exact h.capacity
    · rw [hCapacity]; exact h.address
    · rw [hCapacity]; exact h.below
    · rw [hCapacity]; exact h.separate
    · exact wordSlots_lengths _
  refine ⟨hWrites, hHeap.writesApart hWrites ?_, ⟨words, ?_, hHead, recordWords_owned ..⟩,
    hCapacity⟩
  · intro node hNode
    have hSep := h.separate node hNode
    simp only [regionsDisjoint] at hSep ⊢
    omega
  · exact (recordWords_length _ _ _ _).trans hLength

#print axioms TreeHeader.clearMask_spec

theorem TreeHeader.detach_spec {shape : TreeShape} {r : Fin shape.records} {heap : Heap}
    {store : Store Unit} {p : UInt64} {slots : List Slot}
    (hHeap : heap.At store) (hNode : NodeOwned heap store p (.record slots))
    (hLength : slots.length = shape.width r)
    (hApart : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint) :
    heap.At (clearMask store p) ∧ Owned shape r heap (clearMask store p) p ∧
      SlotsOwned heap (clearMask store p) p 0 slots ∧
      slotsBlocks (clearMask store p) p 0 slots = slotsBlocks store p 0 slots ∧
      (block (clearMask store p) p :: slotsBlocks (clearMask store p) p 0 slots).Pairwise
        regionsDisjoint := by
  obtain ⟨hHead, hSlots⟩ := hNode
  obtain ⟨hWrites, hHeap', hHeader, hCapacity⟩ := clearMask_spec hHeap hHead hLength
  have hAddress := hHead.address
  have hRoom := hHead.capacity
  have hBase := hHead.base
  have hSeparate := (List.pairwise_cons.mp hApart).1
  obtain ⟨hSlots', hBlocks⟩ := SlotsOwned.frame hHeap' p 0 slots hSlots (by omega)
    (fun a hLow _ => hWrites.2.2 a (.inr (by omega)))
    (fun b hb => ⟨fun a hLow hHigh => hWrites.2.2 a (by
      have := hSeparate b hb
      simp only [regionsDisjoint, block] at this
      omega), SlotsOwned.regions p 0 slots hSlots b hb⟩)
  refine ⟨hHeap', hHeader, hSlots', hBlocks, ?_⟩
  rw [block_eq hCapacity, hBlocks]
  exact hApart

#print axioms TreeHeader.detach_spec

end Verified
