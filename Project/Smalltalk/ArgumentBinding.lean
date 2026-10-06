import Project.Smalltalk.ArgumentLinks
import Project.Smalltalk.Construction

namespace Project.Smalltalk.ArgumentBinding
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes

def slotValue (s : Array UInt64) (args arity receiver index : UInt64) : UInt64 :=
  if index == 0 then receiver
  else if index < arity then field s (walk s args (arity - 1 - index)) 2 else 1

theorem selected_eq (s : Array UInt64) (args arity receiver index : UInt64) :
    (if index == 0 then receiver else if index < arity then
      field s (walk s args (if index < arity then arity - 1 - index else 0)) 2 else 1) =
      slotValue s args arity receiver index := by
  unfold slotValue
  split
  · rfl
  · split
    · rfl
    · rfl

theorem argument_depth {arity nargs index : UInt64}
    (arityCount : arity.toNat = nargs.toNat + 1) (positive : 0 < index.toNat)
    (argument : index.toNat < arity.toNat) : (arity - 1 - index).toNat ≤ nargs.toNat := by
  have one : (1 : UInt64) ≤ arity := UInt64.le_iff_toNat_le.mpr (by change 1 ≤ arity.toNat; omega)
  have first : (arity - 1).toNat = arity.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ one]; rfl
  have second : index ≤ arity - 1 := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [first]; omega
  rw [UInt64.toNat_sub_of_le _ _ second, first]
  omega

theorem slotValue_valid_send {s : Array UInt64} {cap : Nat} {args arity nargs receiver : UInt64}
    (valid : Graph.Valid s cap) (typed : PointerTypes.Valid s cap)
    (arguments : Matches s cap 7 args) (bounded : nargs.toNat < cap)
    (accepted : kind s (walk s args nargs) = 7) (arityCount : arity.toNat = nargs.toNat + 1)
    (receiverValue : HeapWrite.Value s cap receiver) (index : UInt64) :
    HeapWrite.Value s cap (slotValue s args arity receiver index) := by
  unfold slotValue
  by_cases zero : index = 0
  · simp only [zero, BEq.rfl, ite_true]; exact receiverValue
  · simp only [show (index == 0) = false from beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false]
    by_cases argument : index < arity
    · simp only [argument, ite_true]
      have positive : 0 < index.toNat := by
        have nonzero : index.toNat ≠ 0 := by intro eq; exact zero (UInt64.toNat_inj.mp eq)
        omega
      exact (ArgumentLinks.send_argument valid typed arguments bounded accepted
        (argument_depth arityCount positive (UInt64.lt_iff_toNat_lt.mp argument))).2.2
    · simp only [argument, ite_false]
      exact Or.inr (valid.2.1 1 ⟨by decide, by simp⟩)

theorem slotValue_valid_entry {s : Array UInt64} {cap : Nat} {args receiver : UInt64}
    (valid : Graph.Valid s cap) (receiverValue : HeapWrite.Value s cap receiver) (index : UInt64) :
    HeapWrite.Value s cap (slotValue s args 1 receiver index) := by
  unfold slotValue
  by_cases zero : index = 0
  · simp only [zero, BEq.rfl, ite_true]; exact receiverValue
  · have outside : ¬ index < (1 : UInt64) := by
      intro smaller
      have bound := UInt64.lt_iff_toNat_lt.mp smaller
      have eq : index.toNat = (0 : UInt64).toNat := by change index.toNat = 0; change index.toNat < 1 at bound; omega
      exact zero (UInt64.toNat_inj.mp eq)
    simp only [show (index == 0) = false from beq_eq_false_iff_ne.mpr zero,
      Bool.false_eq_true, ite_false, outside]
    exact Or.inr (valid.2.1 1 ⟨by decide, by simp⟩)

theorem bindOne_eq_prepend (s : Array UInt64) (args arity locals receiver i : UInt64) :
    bindOne s args arity locals receiver i =
      Construction.prepend s (slotValue s args arity receiver (arity + locals - 1 - i)) :=
  congrArg (Construction.prepend s) (selected_eq s args arity receiver (arity + locals - 1 - i))

theorem bindOne_effect {s : Array UInt64} {cap : Nat} {args arity locals receiver i : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (tail : Matches s cap 7 (read s 19))
    (selected : HeapWrite.Value s cap (slotValue s args arity receiver (arity + locals - 1 - i)))
    (enough : (1 : UInt64) ≤ read s 9) :
    Construction.Effect s (bindOne s args arity locals receiver i) cap
      (slotValue s args arity receiver (arity + locals - 1 - i)) := by
  rw [bindOne_eq_prepend]
  exact Construction.prepend_effect valid typed tail selected enough

end Project.Smalltalk.ArgumentBinding
