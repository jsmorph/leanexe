import Project.LocalRegion.Pull
import Project.LocalRegion.Decidable
import Mathlib.Tactic.SplitIfs

namespace Project.ClobLimit.MatchLocals
open Project.LocalRegion

def Domain (i : Nat) : Prop := i = 0 ∨ 9 ≤ i ∧ i < 95

instance : DecidablePred Domain := fun i =>
  inferInstanceAs (Decidable (i = 0 ∨ 9 ≤ i ∧ i < 95))

def rename (i : Nat) : Nat :=
  if i = 0 then 0
  else if i < 21 then i - 8
  else if i = 21 then 14
  else if i = 22 then 16
  else if i = 23 then 17
  else if i = 73 then 13
  else if i = 75 then 15
  else i - 6

def mapping : SlotMap rename Domain where
  sourceLayout := ⟨9, 86⟩
  targetLayout := ⟨11, 78⟩
  sourceBound := by
    intro i hi
    change i < 95
    simp only [Domain] at hi
    omega
  targetBound := by
    intro i hi
    change rename i < 89
    simp only [Domain] at hi
    simp only [rename]
    split_ifs <;> omega
  injective := by
    intro i j hi hj hEq
    simp only [Domain] at hi hj
    simp only [rename] at hEq
    split_ifs at hEq <;> omega

#print axioms mapping

theorem get (h : mapping.Related source target) (i : Nat) (hi : Domain i)
    (hGet : source.get i = some value) : target.get (rename i) = some value :=
  (h.2.2.2 i hi).symm.trans hGet

end Project.ClobLimit.MatchLocals
