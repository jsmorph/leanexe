import Verified.TreeFieldsMemory

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit

def fieldBlocks (store : Store Unit) : List UInt64 → List LeanExe.Pipeline.Slot →
    List (Nat × Nat)
  | word :: words, slot :: slots => slot.valueBlocks store word ++ fieldBlocks store words slots
  | _, _ => []

theorem fieldValues_frame {heap heap' : Heap} {store store' : Store Unit}
    {words : List UInt64} {slots : List LeanExe.Pipeline.Slot}
    (hValues : List.Forall₂ (fun word slot => slot.ValueOwned heap store word) words slots)
    (hRegions : ∀ b ∈ fieldBlocks store words slots,
      (∀ a, b.1 ≤ a → a < b.1 + b.2 → store'.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region b) :
    List.Forall₂ (fun word slot => slot.ValueOwned heap' store' word) words slots ∧
      fieldBlocks store' words slots = fieldBlocks store words slots := by
  induction hValues with
  | nil => exact ⟨.nil, rfl⟩
  | cons hValue hValues ih =>
    simp only [fieldBlocks] at hRegions ⊢
    obtain ⟨hValue', hFirst⟩ := hValue.frame
      (fun b hb => hRegions b (List.mem_append_left _ hb))
    obtain ⟨hValues', hRest⟩ := ih (fun b hb => hRegions b (List.mem_append_right _ hb))
    exact ⟨.cons hValue' hValues', by rw [hFirst, hRest]⟩

theorem slotsBlocks_of_values {heap : Heap} {store : Store Unit} (ptr : UInt64) :
    ∀ (i : Nat) (words : List UInt64) (slots : List LeanExe.Pipeline.Slot),
      List.Forall₂ (fun word slot => slot.ValueOwned heap store word) words slots →
      (∀ k (hk : k < words.length), store.mem.read64 (slotAddress ptr (i + k)) = words[k]) →
      slotsBlocks store ptr i slots = fieldBlocks store words slots
  | _, [], [], _, _ => rfl
  | i, word :: words, slot :: slots, hValues, hReads => by
    obtain ⟨hValue, hRest⟩ := List.forall₂_cons.mp hValues
    have hRead0 := hReads 0 (by simp)
    rw [Nat.add_zero, List.getElem_cons_zero] at hRead0
    have hFirst := hValue.singleton (p := ptr) (i := i) hRead0
    have hTail := slotsBlocks_of_values ptr (i + 1) words slots hRest fun k hk => by
      have hRead := hReads (k + 1) (by simpa using hk)
      rw [List.getElem_cons_succ] at hRead
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hRead
    change slotsBlocks store ptr i ([slot] ++ slots) = _
    rw [slotsBlocks_append, hFirst.2]
    simpa only [List.length_singleton, fieldBlocks] using congrArg
      (fun tail => slot.valueBlocks store word ++ tail) hTail

theorem fieldValues_regions {heap : Heap} {store : Store Unit}
    {words : List UInt64} {slots : List LeanExe.Pipeline.Slot}
    (hValues : List.Forall₂ (fun word slot => slot.ValueOwned heap store word) words slots) :
    ∀ b ∈ fieldBlocks store words slots, heap.Region b := by
  induction hValues with
  | nil => exact nofun
  | cons hValue hValues ih =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hValue.regions b hb
    · exact ih b hb

end Verified
