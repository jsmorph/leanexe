import LeanExe.Pipeline.Records

namespace LeanExe.Pipeline

open Wasm

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

end LeanExe.Pipeline
