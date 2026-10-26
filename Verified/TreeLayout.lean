import Verified.Tree

namespace Verified

theorem bool_counts (fields : List Bool) : fields.count false + fields.count true = fields.length := by
  induction fields with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp_all <;> omega

theorem TreeShape.words_children (shape : TreeShape) (r : Fin shape.records) :
    shape.words r + shape.children r = (shape.fields r).length := bool_counts (shape.fields r)

def fieldPosition (bit : Bool) : (fields : List Bool) → Fin (fields.count bit) → Fin fields.length
  | [], i => Fin.elim0 i
  | head :: rest, i =>
    if h : head = bit then
      if hz : i.val = 0 then ⟨0, by simp⟩
      else
        (fieldPosition bit rest ⟨i.val - 1, by
          have := i.isLt
          simp only [List.count_cons, h, beq_self_eq_true, ite_true] at this
          omega⟩).succ
    else
      (fieldPosition bit rest ⟨i.val, by simpa [h] using i.isLt⟩).succ

theorem fieldPosition_get (bit : Bool) : ∀ (fields : List Bool) (i : Fin (fields.count bit)),
    fields[(fieldPosition bit fields i).val] = bit
  | [], i => Fin.elim0 i
  | head :: rest, i => by
    by_cases h : head = bit
    · by_cases hz : i.val = 0
      · simp [fieldPosition, h, hz]
      · simp only [fieldPosition, dite_eq_left h, dite_eq_right hz, Fin.val_succ,
          List.getElem_cons_succ]
        exact fieldPosition_get bit rest _
    · simp only [fieldPosition, dite_eq_right h, Fin.val_succ, List.getElem_cons_succ]
      exact fieldPosition_get bit rest _

#print axioms TreeShape.words_children
#print axioms fieldPosition_get

theorem treeSlots_word_get (fields : List Bool) :
    ∀ words children (i : Fin (fields.count false)),
      (treeSlots fields words children)[(fieldPosition false fields i).val]'(by
        rw [treeSlots_length]; exact (fieldPosition false fields i).isLt) =
        LeanExe.Pipeline.Slot.word (words i) := by
  induction fields with
  | nil => intro words children i; exact Fin.elim0 i
  | cons bit rest ih =>
    intro words children i
    cases bit
    · by_cases hz : i.val = 0
      · have hi : i = ⟨0, by simp⟩ := Fin.ext hz
        subst i
        simp [treeSlots, fieldPosition]
      · rw [fieldPosition, dite_eq_left rfl, dite_eq_right hz]
        simp only [Fin.val_succ, treeSlots, List.getElem_cons_succ]
        rw [ih]
        congr 1
        apply congrArg words
        apply Fin.ext
        simp only
        omega
    · simp only [fieldPosition, dite_eq_right (by decide : true ≠ false), Fin.val_succ,
        treeSlots, List.getElem_cons_succ]
      exact ih _ _ _

theorem treeSlots_child_get (fields : List Bool) :
    ∀ words children (i : Fin (fields.count true)),
      (treeSlots fields words children)[(fieldPosition true fields i).val]'(by
        rw [treeSlots_length]; exact (fieldPosition true fields i).isLt) =
        LeanExe.Pipeline.Slot.child (children i) := by
  induction fields with
  | nil => intro words children i; exact Fin.elim0 i
  | cons bit rest ih =>
    intro words children i
    cases bit
    · simp only [fieldPosition, dite_eq_right (by decide : false ≠ true), Fin.val_succ,
        treeSlots, List.getElem_cons_succ]
      exact ih _ _ _
    · by_cases hz : i.val = 0
      · have hi : i = ⟨0, by simp⟩ := Fin.ext hz
        subst i
        simp [treeSlots, fieldPosition]
      · rw [fieldPosition, dite_eq_left rfl, dite_eq_right hz]
        simp only [Fin.val_succ, treeSlots, List.getElem_cons_succ]
        rw [ih]
        congr 1
        apply congrArg children
        apply Fin.ext
        simp only
        omega

#print axioms treeSlots_word_get
#print axioms treeSlots_child_get

end Verified
