import Verified.TreeLayout
import Verified.TreeFieldsCode
import Verified.TreeFieldsStore
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

/-- The words at positions from `wordBase` on, of the types `tys`, and the pointers at the
positions from `childBase` on are the sources of a record's slots in the order of `fields`. -/
theorem treeFieldLocs_values {s : Locals} {h : Nat} (fields : List Bool) :
    ∀ (tys : List ValueType) wordBase childBase words pointers,
      (∀ i, s.get (slotIndex h (wordBase + i.val) (tys.getD i.val .i64)) =
          some (typedValue (tys.getD i.val .i64) (words i)) ∧
        Value.word (typedValue (tys.getD i.val .i64) (words i)) = words i) →
      (∀ i, s.get (childBase + i.val) = some (.i64 (pointers i))) →
      SourcesHold s h (treeFieldLocs fields wordBase childBase) (treeFieldTypes fields tys)
        (treeFieldValues fields words pointers) := by
  induction fields with
  | nil => intros; trivial
  | cons bit rest ih =>
    intro tys wordBase childBase words pointers hWords hPointers
    cases bit <;> simp only [treeFieldLocs, treeFieldValues, treeFieldTypes, SourcesHold]
    · have h0 := hWords ⟨0, by simp⟩
      have hHead : tys.getD 0 .i64 = tys.headD .i64 := by cases tys <;> rfl
      simp only [Nat.add_zero, hHead] at h0
      exact ⟨h0.1, h0.2, ih _ _ _ _ _ (fun i => by
          have hi := hWords ⟨i.val + 1, by simp⟩
          have hTail : tys.getD (i.val + 1) .i64 = tys.tail.getD i.val .i64 := by
            cases tys <;> simp
          simpa only [Nat.add_assoc, Nat.add_comm 1 i.val, hTail] using hi)
          (fun i => hPointers ⟨i.val, by simp⟩)⟩
    · exact ⟨by simpa [slotIndex, typedValue] using hPointers ⟨0, by simp⟩, rfl,
        ih _ _ _ _ _ (fun i => hWords ⟨i.val, by simp⟩) (fun i => by
          simpa only [Nat.add_assoc, Nat.add_comm 1 i.val] using hPointers ⟨i.val + 1, by simp⟩)⟩

end Verified
