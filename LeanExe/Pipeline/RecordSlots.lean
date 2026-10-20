import LeanExe.Pipeline.Records

namespace LeanExe.Pipeline

open Wasm

def Slot.ValueOwned (heap : Heap) (store : Store Unit) (word : UInt64) : Slot → Prop
  | .word value => word = value
  | .child value => NodeOwned heap store word value

def Slot.valueBlocks (store : Store Unit) (word : UInt64) : Slot → List (Nat × Nat)
  | .word _ => []
  | .child value => value.blocks store word

theorem Slot.ValueOwned.frame {heap heap' : Heap} {store store' : Store Unit}
    {word : UInt64} {slot : Slot} (h : slot.ValueOwned heap store word)
    (hRegions : ∀ b ∈ slot.valueBlocks store word,
      (∀ a, b.1 ≤ a → a < b.1 + b.2 → store'.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region b) :
    slot.ValueOwned heap' store' word ∧
      slot.valueBlocks store' word = slot.valueBlocks store word := by
  cases slot with
  | word value => exact ⟨h, rfl⟩
  | child value => exact NodeOwned.frame word value h hRegions

theorem Slot.ValueOwned.regions {heap : Heap} {store : Store Unit}
    {word : UInt64} {slot : Slot} (h : slot.ValueOwned heap store word) :
    ∀ b ∈ slot.valueBlocks store word, heap.Region b := by
  cases slot with
  | word value => exact nofun
  | child value => exact NodeOwned.regions word value h

theorem Slot.ValueOwned.singleton {heap : Heap} {store : Store Unit}
    {word p : UInt64} {slot : Slot} {i : Nat} (h : slot.ValueOwned heap store word)
    (hRead : store.mem.read64 (slotAddress p i) = word) :
    SlotsOwned heap store p i [slot] ∧
      slotsBlocks store p i [slot] = slot.valueBlocks store word := by
  cases slot <;> simp only [SlotsOwned, slotsBlocks, hRead, Node.blocks, List.append_nil]
  · exact ⟨⟨h, trivial⟩, rfl⟩
  · exact ⟨⟨h, trivial⟩, rfl⟩

theorem SlotsOwned.append_iff {heap : Heap} {store : Store Unit} {p : UInt64}
    (first : List Slot) : ∀ second i,
      SlotsOwned heap store p i (first ++ second) ↔
        SlotsOwned heap store p i first ∧ SlotsOwned heap store p (i + first.length) second := by
  induction first with
  | nil => intros; simp [SlotsOwned]
  | cons slot rest ih =>
    intro second i
    cases slot <;> simp [SlotsOwned, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, and_assoc]

theorem SlotsBorrowed.append_iff {heap : Heap} {store : Store Unit} {p : UInt64}
    (first : List Slot) : ∀ second i,
      SlotsBorrowed heap store p i (first ++ second) ↔
        SlotsBorrowed heap store p i first ∧
          SlotsBorrowed heap store p (i + first.length) second := by
  induction first with
  | nil => intros; simp [SlotsBorrowed]
  | cons slot rest ih =>
    intro second i
    cases slot <;>
      simp [SlotsBorrowed, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, and_assoc]

theorem slotsBlocks_append (store : Store Unit) (p : UInt64) (first : List Slot) :
    ∀ second i, slotsBlocks store p i (first ++ second) =
      slotsBlocks store p i first ++ slotsBlocks store p (i + first.length) second := by
  induction first with
  | nil => intros; simp [slotsBlocks]
  | cons slot rest ih =>
    intro second i
    cases slot <;>
      simp [slotsBlocks, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc]

theorem SlotsOwned.get {heap : Heap} {store : Store Unit} {p : UInt64} :
    ∀ (slots : List Slot) i, SlotsOwned heap store p i slots →
      ∀ j (h : j < slots.length), SlotsOwned heap store p (i + j) [slots[j]]
  | [], _, _, j, h => by simp at h
  | slot :: rest, i, h, 0, _ => by
    cases slot <;> exact ⟨h.1, trivial⟩
  | slot :: rest, i, h, j + 1, hj => by
    cases slot <;>
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SlotsOwned.get rest (i + 1) h.2 j (by simpa using hj)

theorem SlotsBorrowed.get {heap : Heap} {store : Store Unit} {p : UInt64} :
    ∀ (slots : List Slot) i, SlotsBorrowed heap store p i slots →
      ∀ j (h : j < slots.length), SlotsBorrowed heap store p (i + j) [slots[j]]
  | [], _, _, j, h => by simp at h
  | slot :: rest, i, h, 0, _ => by
    cases slot <;> exact ⟨h.1, trivial⟩
  | slot :: rest, i, h, j + 1, hj => by
    cases slot <;>
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SlotsBorrowed.get rest (i + 1) h.2 j (by simpa using hj)

#print axioms SlotsOwned.append_iff
#print axioms SlotsOwned.get
#print axioms SlotsBorrowed.get
#print axioms Slot.ValueOwned.frame
#print axioms Slot.ValueOwned.singleton

end LeanExe.Pipeline
