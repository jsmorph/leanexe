import Project.Smalltalk.AdvanceTypes
import Project.Smalltalk.ArgumentTransfer

namespace Project.Smalltalk.CallInputs
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.Reachability

theorem current_handle {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (current : kind s (read s 2) = 5) : Handle cap (read s 2) := kind_handle valid.1 (by decide) current

theorem current_tag {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (current : kind s (read s 2) = 5) : field s (read s 2) 0 = 5 :=
  (kind_eq_field valid.1 (current_handle valid current)).symm.trans current

theorem args_typed {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (typed : PointerTypes.Valid s cap) (current : kind s (read s 2) = 5) :
    Matches s cap 7 (field s (read s 2) 7) := by
  have tag := current_tag valid current
  exact typed _ (current_handle valid current) (by rw [tag]; decide) 7 (by decide) 7 (by simp [Required, tag])

theorem args_live {s : Array UInt64} (current : kind s (read s 2) = 5) :
    Live s (field s (read s 2) 7) := by
  have reached := live_reached (root_live s 2 (Or.inl rfl)) (by decide) current
  apply pointer_live reached (show (7 : UInt64).toNat < 8 by decide)
  -- A reached activation's kind equals its tag at every valid handle.
  unfold kind at current
  split at current
  · contradiction
  · rw [current]; simp [PointerField]

theorem walk_typed {s : Array UInt64} {cap : Nat} {args : UInt64}
    (shape : Shape s cap) (typed : PointerTypes.Valid s cap) (head : Matches s cap 7 args) (count : UInt64) :
    Matches s cap 7 (walk s args count) := by
  rw [Traversal.walk_eq_follow]
  exact ArgumentLinks.follow_typed shape typed head _

theorem advance_payload {s : Array UInt64} {cap : Nat} {rest : UInt64}
    (valid : Graph.Valid s cap) (current : kind s (read s 2) = 5) :
    ArgumentTransfer.Payload s (advance s rest) := by
  intro h reached tag k bound _
  have handle := (reachable_allocated valid reached).1
  have different : h ≠ read s 2 := by
    intro same
    rw [same, current_tag valid current] at tag
    contradiction
  rw [Frame.advance_field valid.1 (current_handle valid current) handle bound]
  simp only [different, false_and, ite_false]

theorem advance_inputs {s : Array UInt64} {cap : Nat} {arity receiver rest : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (current : kind s (read s 2) = 5)
    (inputs : BindingPreservation.Inputs s cap (field s (read s 2) 7) arity receiver) :
    BindingPreservation.Inputs (advance s rest) cap (field s (read s 2) 7) arity receiver :=
  ArgumentTransfer.inputs_transfer valid.1 typed (Frame.advance_shape valid.1.1 (current_handle valid.1 current) rest)
    (args_live current) inputs (advance_payload valid.1 current)
    (AdvanceTypes.advance_value valid.1.1 (current_handle valid.1 current) inputs.receiver)

end Project.Smalltalk.CallInputs
