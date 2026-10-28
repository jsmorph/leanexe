import LeanExe.Pipeline.Records

namespace LeanExe.Pipeline

open Wasm

def Slot.ValueOwned (heap : Heap) (store : Store Unit) (word : UInt64) : Slot → Prop
  | .word value => word = value
  | .child value => NodeOwned heap store word value
  | .array words => heap.Owned store word words
  | .bytes data =>
      (word = 0 ∧ data.data.size = 0) ∨ (data.data.size ≠ 0 ∧ heap.Buffer store word data)

def Slot.valueBlocks (store : Store Unit) (word : UInt64) : Slot → List (Nat × Nat)
  | .word _ => []
  | .child value => value.blocks store word
  | .array _ => [block store word]
  | .bytes data => (bufferRoots data word).map (block store)

theorem Slot.ValueOwned.frame {heap heap' : Heap} {store store' : Store Unit}
    {word : UInt64} {slot : Slot} (hAt : heap'.At store') (h : slot.ValueOwned heap store word)
    (hRegions : ∀ b ∈ slot.valueBlocks store word,
      (∀ a, b.1 ≤ a → a < b.1 + b.2 → store'.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region b) :
    slot.ValueOwned heap' store' word ∧
      slot.valueBlocks store' word = slot.valueBlocks store word := by
  cases slot with
  | word value => exact ⟨h, rfl⟩
  | child value => exact NodeOwned.frame hAt word value h hRegions
  | array words =>
    have hFirst := hRegions _ List.mem_cons_self
    obtain ⟨hArray, hCapacity⟩ :=
      Heap.Owned.keepIn (q := word) (ws := words) h hAt hFirst.1 hFirst.2
    exact ⟨hArray, by simp only [Slot.valueBlocks, block_eq hCapacity]⟩
  | bytes data =>
    rcases h with ⟨hZero, hEmpty⟩ | ⟨hNonempty, hBuffer⟩
    · exact ⟨.inl ⟨hZero, hEmpty⟩, by simp only [Slot.valueBlocks, bufferRoots, hEmpty,
        ↓reduceIte, List.map_nil]⟩
    · have hFirst := hRegions (block store word)
        (by simp [Slot.valueBlocks, bufferRoots, hNonempty])
      obtain ⟨hBuffer', hCapacity⟩ := hBuffer.frameIn
        (fun a hLow hHigh => hFirst.1 a (by simp only [block]; omega)
          (by have := hBuffer.object.base; simp only [block]; omega)) hFirst.2
      exact ⟨.inr ⟨hNonempty, hBuffer'⟩, by
        simp only [Slot.valueBlocks, bufferRoots, hNonempty, ↓reduceIte, List.map_cons,
          List.map_nil, block_eq hCapacity]⟩

theorem Slot.ValueOwned.regions {heap : Heap} {store : Store Unit}
    {word : UInt64} {slot : Slot} (h : slot.ValueOwned heap store word) :
    ∀ b ∈ slot.valueBlocks store word, heap.Region b := by
  cases slot with
  | word value => exact nofun
  | child value => exact NodeOwned.regions word value h
  | array words =>
    intro b hb
    rw [List.mem_singleton.mp hb]
    exact Heap.Owned.region h
  | bytes data =>
    intro b hb
    rcases h with ⟨-, hEmpty⟩ | ⟨-, hBuffer⟩
    · simp [Slot.valueBlocks, bufferRoots, hEmpty] at hb
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      have : q = word := by
        unfold bufferRoots at hq
        split at hq <;> simp_all
      subst this
      exact hBuffer.region

theorem Slot.ValueOwned.singleton {heap : Heap} {store : Store Unit}
    {word p : UInt64} {slot : Slot} {i : Nat} (h : slot.ValueOwned heap store word)
    (hRead : store.mem.read64 (slotAddress p i) = word) :
    SlotsOwned heap store p i [slot] ∧
      slotsBlocks store p i [slot] = slot.valueBlocks store word := by
  cases slot <;> simp only [SlotsOwned, slotsBlocks, hRead, Node.blocks, List.append_nil] <;>
    exact ⟨⟨h, trivial⟩, rfl⟩

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
