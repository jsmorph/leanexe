import Verified.TreeStorage
import LeanExe.Pipeline.RecordSlots

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit

def recordWriteValues (ptr : UInt64) : Nat → List UInt64 → Store Unit → Store Unit
  | _, [], store => store
  | i, word :: rest, store =>
    recordWriteValues ptr (i + 1) rest
      { store with mem := store.mem.write64 (slotAddress ptr i) word }

theorem recordWriteValues_range (ptr : UInt64) :
    ∀ (i : Nat) (words : List UInt64) (store : Store Unit),
      ptr.toNat + 8 * (i + words.length) < 4294967296 →
      Memory.WritesRange store (recordWriteValues ptr i words store)
        (ptr.toNat + 8 * i) (ptr.toNat + 8 * (i + words.length))
  | i, [], store, _ => Memory.WritesRange.refl store _ _
  | i, word :: rest, store, hAddress => by
    have hSlot : (slotAddress ptr i).toNat = ptr.toNat + 8 * i :=
      slotAddress_toNat (by simp only [List.length_cons] at hAddress; omega)
    have hWrite := Memory.WritesRange.write64 store (slotAddress ptr i) word
      (ptr.toNat + 8 * i) (ptr.toNat + 8 * (i + (word :: rest).length))
      (by rw [hSlot]) (by rw [hSlot]; simp only [List.length_cons]; omega)
    exact hWrite.trans ((recordWriteValues_range ptr (i + 1) rest _ (by
      simp only [List.length_cons] at hAddress; omega)).mono (by omega) (by
        simp only [List.length_cons]; omega))

theorem recordWriteValues_read (ptr : UInt64) :
    ∀ (i : Nat) (words : List UInt64) (store : Store Unit),
      ptr.toNat + 8 * (i + words.length) < 4294967296 →
      ∀ k (hk : k < words.length),
        (recordWriteValues ptr i words store).mem.read64 (slotAddress ptr (i + k)) = words[k]
  | _, [], _, _, k, hk => by simp at hk
  | i, word :: rest, store, hAddress, 0, _ => by
    have hRest := recordWriteValues_range ptr (i + 1) rest
      { store with mem := store.mem.write64 (slotAddress ptr i) word } (by
        simp only [List.length_cons] at hAddress; omega)
    change (recordWriteValues ptr (i + 1) rest _).mem.read64 (slotAddress ptr i) = word
    rw [hRest.read64 _ (Or.inl (by
      rw [slotAddress_toNat (by simp only [List.length_cons] at hAddress; omega)]
      omega))]
    exact Memory.read64_write64 ..
  | i, word :: rest, store, hAddress, k + 1, hk => by
    have h := recordWriteValues_read ptr (i + 1) rest
      { store with mem := store.mem.write64 (slotAddress ptr i) word }
      (by simp only [List.length_cons] at hAddress; omega) k
      (by simp only [List.length_cons] at hk; omega)
    simpa only [recordWriteValues, List.getElem_cons_succ, Nat.add_assoc,
      Nat.add_comm 1 k] using h

theorem slotsOwned_of_values {heap : Heap} {store : Store Unit} (ptr : UInt64) :
    ∀ (i : Nat) (words : List UInt64) (slots : List LeanExe.Pipeline.Slot),
      List.Forall₂ (fun word slot => slot.ValueOwned heap store word) words slots →
      (∀ k (hk : k < words.length), store.mem.read64 (slotAddress ptr (i + k)) = words[k]) →
      SlotsOwned heap store ptr i slots
  | _, [], [], _, _ => trivial
  | i, word :: words, slot :: slots, hValues, hReads => by
    obtain ⟨hValue, hRest⟩ := List.forall₂_cons.mp hValues
    have hRead0 := hReads 0 (by simp)
    rw [Nat.add_zero, List.getElem_cons_zero] at hRead0
    have hFirst := hValue.singleton (p := ptr) (i := i) hRead0
    have hTail := slotsOwned_of_values ptr (i + 1) words slots hRest fun k hk => by
      have hRead := hReads (k + 1) (by simpa using hk)
      rw [List.getElem_cons_succ] at hRead
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hRead
    exact (SlotsOwned.append_iff [slot] slots i).mpr ⟨hFirst.1, hTail⟩

end Verified
