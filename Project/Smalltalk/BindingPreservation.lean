import Project.Smalltalk.ArgumentBinding

namespace Project.Smalltalk.BindingPreservation
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.Traversal
open Project.Smalltalk.ArgumentBinding

def Preserved (s t : Array UInt64) (cap : Nat) : Prop :=
  ∀ h, Handle cap h → field s h 0 ≠ 0 → ∀ k : UInt64, k.toNat < 8 → field t h k = field s h k

theorem value_transfer {s t : Array UInt64} {cap : Nat} {value : UInt64}
    (same : Preserved s t cap) (original : HeapWrite.Value s cap value) : HeapWrite.Value t cap value := by
  rcases original with zero | cell
  · exact Or.inl zero
  · exact Or.inr ⟨cell.1, by rw [same value cell.1 cell.2 0 (by decide)]; exact cell.2⟩

theorem matches_transfer {s t : Array UInt64} {cap : Nat} {tag value : UInt64}
    (same : Preserved s t cap) (nonzero : tag ≠ 0) (original : Matches s cap tag value) :
    Matches t cap tag value := by
  rcases original with zero | cell
  · exact Or.inl zero
  · exact Or.inr ⟨cell.1, by rw [same value cell.1 (by rw [cell.2]; exact nonzero) 0 (by decide)]; exact cell.2⟩

theorem follow_transfer {s t : Array UInt64} {cap : Nat} {head : UInt64}
    (originalShape : Shape s cap) (finalShape : Shape t cap) (typed : PointerTypes.Valid s cap)
    (same : Preserved s t cap) (arguments : Matches s cap 7 head) (n : Nat) :
    follow t 7 3 n head = follow s 7 3 n head := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [follow, ih]
    have matching := ArgumentLinks.follow_typed originalShape typed arguments n
    rcases matching with zero | cell
    · rw [zero]; simp [hop, kind]
    · have tag : kind s (follow s 7 3 n head) = 7 := (kind_eq_field originalShape cell.1).trans cell.2
      have tagAfter : kind t (follow s 7 3 n head) = 7 := by
        rw [kind_eq_field finalShape cell.1, same _ cell.1 (by rw [cell.2]; decide) 0 (by decide), cell.2]
      simp only [hop, tag, tagAfter, ite_true]
      exact same _ cell.1 (by rw [cell.2]; decide) 3 (by decide)

theorem walk_transfer {s t : Array UInt64} {cap : Nat} {args : UInt64}
    (originalShape : Shape s cap) (finalShape : Shape t cap) (typed : PointerTypes.Valid s cap)
    (same : Preserved s t cap) (arguments : Matches s cap 7 args) (count : UInt64) :
    walk t args count = walk s args count := by
  have capacity : read t 14 = read s 14 := UInt64.toNat_inj.mp (finalShape.2.2.2.trans originalShape.2.2.2.symm)
  rw [walk_eq_follow, walk_eq_follow, capacity]
  exact follow_transfer originalShape finalShape typed same arguments _

structure Inputs (s : Array UInt64) (cap : Nat) (args arity receiver : UInt64) : Prop where
  argsTyped : Matches s cap 7 args
  receiver : HeapWrite.Value s cap receiver
  arguments : ∀ depth : UInt64, depth.toNat + 1 < arity.toNat →
    Handle cap (walk s args depth) ∧ field s (walk s args depth) 0 = 7

theorem send_inputs {s : Array UInt64} {cap : Nat} {args arity nargs receiver : UInt64}
    (valid : Graph.Valid s cap) (typed : PointerTypes.Valid s cap)
    (arguments : Matches s cap 7 args) (bounded : nargs.toNat < cap)
    (accepted : kind s (walk s args nargs) = 7) (arityCount : arity.toNat = nargs.toNat + 1)
    (receiverValue : HeapWrite.Value s cap receiver) : Inputs s cap args arity receiver := by
  refine ⟨arguments, receiverValue, ?_⟩
  intro depth within
  have argument := ArgumentLinks.send_argument valid typed arguments bounded accepted (show depth.toNat ≤ nargs.toNat by omega)
  exact ⟨argument.1, argument.2.1⟩

theorem entry_inputs {s : Array UInt64} {cap : Nat} {receiver : UInt64}
    (receiverValue : HeapWrite.Value s cap receiver) : Inputs s cap 0 1 receiver := by
  refine ⟨Or.inl rfl, receiverValue, ?_⟩
  intro depth within
  change depth.toNat + 1 < 1 at within
  omega

theorem depth_lt {arity index : UInt64} (positive : 0 < index.toNat)
    (argument : index.toNat < arity.toNat) : (arity - 1 - index).toNat + 1 < arity.toNat := by
  have one : (1 : UInt64) ≤ arity := UInt64.le_iff_toNat_le.mpr (by change 1 ≤ arity.toNat; omega)
  have first : (arity - 1).toNat = arity.toNat - 1 := by rw [UInt64.toNat_sub_of_le _ _ one]; rfl
  have second : index ≤ arity - 1 := by apply UInt64.le_iff_toNat_le.mpr; rw [first]; omega
  rw [UInt64.toNat_sub_of_le _ _ second, first]
  omega

theorem selected_argument {s : Array UInt64} {cap : Nat} {args arity receiver index : UInt64}
    (inputs : Inputs s cap args arity receiver) (nonzero : index ≠ 0) (argument : index < arity) :
    Handle cap (walk s args (arity - 1 - index)) ∧ field s (walk s args (arity - 1 - index)) 0 = 7 := by
  have positive : 0 < index.toNat := by
    have nz : index.toNat ≠ 0 := by intro eq; exact nonzero (UInt64.toNat_inj.mp eq)
    omega
  exact inputs.arguments _ (depth_lt positive (UInt64.lt_iff_toNat_lt.mp argument))

theorem slotValue_valid {s : Array UInt64} {cap : Nat} {args arity receiver : UInt64}
    (valid : Graph.Valid s cap) (inputs : Inputs s cap args arity receiver) (index : UInt64) :
    HeapWrite.Value s cap (slotValue s args arity receiver index) := by
  unfold slotValue
  by_cases zero : index = 0
  · simp only [zero, BEq.rfl, ite_true]; exact inputs.receiver
  · simp only [show (index == 0) = false from beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false]
    by_cases argument : index < arity
    · simp only [argument, ite_true]
      have cell := selected_argument inputs zero argument
      exact Reachability.pointer_value valid cell.1 (by rw [cell.2]; decide) (by decide) (by simp [PointerField, cell.2])
    · simp only [argument, ite_false]
      exact Or.inr (valid.2.1 1 ⟨by decide, by simp⟩)

theorem slotValue_transfer {s t : Array UInt64} {cap : Nat} {args arity receiver : UInt64}
    (originalShape : Shape s cap) (finalShape : Shape t cap) (typed : PointerTypes.Valid s cap)
    (same : Preserved s t cap) (inputs : Inputs s cap args arity receiver) (index : UInt64) :
    slotValue t args arity receiver index = slotValue s args arity receiver index := by
  unfold slotValue
  by_cases zero : index = 0
  · simp only [zero, BEq.rfl, ite_true]
  · simp only [show (index == 0) = false from beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false]
    by_cases argument : index < arity
    · simp only [argument, ite_true]
      rw [walk_transfer originalShape finalShape typed same inputs.argsTyped]
      have cell := selected_argument inputs zero argument
      exact same _ cell.1 (by rw [cell.2]; decide) 2 (by decide)
    · simp only [argument, ite_false]

end Project.Smalltalk.BindingPreservation
