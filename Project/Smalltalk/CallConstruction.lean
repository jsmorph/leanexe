import Project.Smalltalk.CallInputs
import Project.Smalltalk.ActivationConstruction

namespace Project.Smalltalk.CallConstruction
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.PointerTypes Project.Smalltalk.CallInputs

theorem sendMethodReady_eq (p s : Array UInt64) (method arity receiver lex : UInt64) :
    sendMethodReady p s method arity receiver lex =
      enterReady p (advance s (walk s (field s (read s 2) 7) arity)) method
        (field s (read s 2) 7) receiver (read s 2) lex := rfl

structure Effect (p s t : Array UInt64) (cap : Nat) (method arity receiver lex : UInt64) : Prop where
  entry : ActivationConstruction.Effect p (advance s (walk s (field s (read s 2) 7) arity)) t cap
    method (field s (read s 2) 7) receiver (read s 2) lex
  callerPC : field t (read s 2) 3 = field s (read s 2) 3 + 1
  callerStack : field t (read s 2) 7 = walk s (field s (read s 2) 7) arity
  phase : read t 0 = read s 0

theorem sendMethodReady_effect {p s : Array UInt64} {cap : Nat} {method arity receiver lex : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (current : kind s (read s 2) = 5)
    (inputs : BindingPreservation.Inputs s cap (field s (read s 2) 7) (methodAt p method 2) receiver)
    (lexType : Matches s cap 5 lex)
    (budget : (methodAt p method 2).toNat + (methodAt p method 3).toNat + 1 ≤ (read s 9).toNat) :
    Effect p s (sendMethodReady p s method arity receiver lex) cap method arity receiver lex := by
  let rest := walk s (field s (read s 2) 7) arity
  let t := advance s rest
  have handle := current_handle valid.1 current
  have tag := current_tag valid.1 current
  have restType : Matches s cap 7 rest := walk_typed valid.1.1 typed (args_typed valid.1 typed current) arity
  have updated : Heap.Valid t cap := FrameHeap.advance_valid valid handle tag (matches_value restType (by decide))
  have updatedTyped : PointerTypes.Valid t cap := AdvanceTypes.advance_typed valid.1.1 typed handle tag restType
  have caller : Matches t cap 5 (read s 2) := AdvanceTypes.advance_matches valid.1.1 handle (Or.inr ⟨handle, tag⟩)
  have lexAfter : Matches t cap 5 lex := AdvanceTypes.advance_matches valid.1.1 handle lexType
  have selected : BindingPreservation.Inputs t cap (field s (read s 2) 7) (methodAt p method 2) receiver :=
    advance_inputs valid typed current inputs
  have room : (methodAt p method 2).toNat + (methodAt p method 3).toNat + 1 ≤ (read t 9).toNat := by
    rw [Frame.advance_register valid.1.1 handle (show (9 : UInt64).toNat < 24 by decide)]
    exact budget
  have built : ActivationConstruction.Effect p t (enterReady p t method (field s (read s 2) 7) receiver (read s 2) lex)
      cap method (field s (read s 2) 7) receiver (read s 2) lex :=
    ActivationConstruction.enterReady_effect updated updatedTyped selected caller lexAfter room
  rw [sendMethodReady_eq]
  refine ⟨built, ?_, ?_, ?_⟩
  · have allocated : field t (read s 2) 0 ≠ 0 := by
      rw [AdvanceTypes.advance_tag valid.1.1 handle handle, tag]; decide
    rw [built.previous _ handle allocated 3 (by decide), Frame.advance_field valid.1.1 handle handle (show (3 : UInt64).toNat < 8 by decide)]
    simp
  · have allocated : field t (read s 2) 0 ≠ 0 := by
      rw [AdvanceTypes.advance_tag valid.1.1 handle handle, tag]; decide
    rw [built.previous _ handle allocated 7 (by decide), Frame.advance_field valid.1.1 handle handle (show (7 : UInt64).toNat < 8 by decide)]
    simp [rest]
  · exact (built.registers 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      (Frame.advance_register valid.1.1 handle (show (0 : UInt64).toNat < 24 by decide) rest)

end Project.Smalltalk.CallConstruction
