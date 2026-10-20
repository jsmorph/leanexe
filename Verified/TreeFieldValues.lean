import Verified.TreeLayout
import Verified.TreeFieldsCode
import LeanExe.Pipeline.RecordSlots

namespace Verified

open Wasm LeanExe.Pipeline

def treeFieldValues : (fields : List Bool) →
    (Fin (fields.count false) → UInt64) → (Fin (fields.count true) → UInt64) → List UInt64
  | [], _, _ => []
  | false :: rest, words, children =>
    words ⟨0, by simp⟩ :: treeFieldValues rest
      (fun i => words ⟨i.val + 1, by simp⟩) (fun i => children ⟨i.val, by simp⟩)
  | true :: rest, words, children =>
    children ⟨0, by simp⟩ :: treeFieldValues rest
      (fun i => words ⟨i.val, by simp⟩) (fun i => children ⟨i.val + 1, by simp⟩)

theorem treeFieldValues_length (fields : List Bool) :
    ∀ words children, (treeFieldValues fields words children).length = fields.length := by
  induction fields with
  | nil => intros; rfl
  | cons bit rest ih => cases bit <;> intros <;> simp only [treeFieldValues, List.length_cons, ih]

theorem treeFieldValues_owned {heap : Heap} {store : Store Unit} (fields : List Bool) :
    ∀ words pointers children,
      (∀ i, NodeOwned heap store (pointers i) (children i)) →
      List.Forall₂ (fun word slot => slot.ValueOwned heap store word)
        (treeFieldValues fields words pointers) (treeSlots fields words children) := by
  induction fields with
  | nil => intros; exact .nil
  | cons bit rest ih =>
    intro words pointers children hChildren
    cases bit <;> simp only [treeFieldValues, treeSlots]
    · exact .cons rfl (ih _ _ _ fun i => hChildren ⟨i.val, by simp⟩)
    · exact .cons (hChildren ⟨0, by simp⟩) (ih _ _ _ fun i => hChildren ⟨i.val + 1, by simp⟩)

theorem treeFieldLocs_values {s : Locals} (fields : List Bool) :
    ∀ wordBase childBase words pointers,
      (∀ i, s.get (wordBase + i.val) = some (.i64 (words i))) →
      (∀ i, s.get (childBase + i.val) = some (.i64 (pointers i))) →
      List.Forall₂ (fun src word => s.get src = some (.i64 word))
        (treeFieldLocs fields wordBase childBase) (treeFieldValues fields words pointers) := by
  induction fields with
  | nil => intros; exact .nil
  | cons bit rest ih =>
    intro wordBase childBase words pointers hWords hPointers
    cases bit <;> simp only [treeFieldLocs, treeFieldValues]
    · exact .cons (by simpa using hWords ⟨0, by simp⟩)
        (ih _ _ _ _ (fun i => by
          simpa only [Nat.add_assoc, Nat.add_comm 1 i.val] using hWords ⟨i.val + 1, by simp⟩)
          (fun i => hPointers ⟨i.val, by simp⟩))
    · exact .cons (by simpa using hPointers ⟨0, by simp⟩)
        (ih _ _ _ _ (fun i => hWords ⟨i.val, by simp⟩) (fun i => by
          simpa only [Nat.add_assoc, Nat.add_comm 1 i.val] using hPointers ⟨i.val + 1, by simp⟩))

end Verified
