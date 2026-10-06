import Project.Smalltalk.CallConstruction
import Project.Smalltalk.CallBudget
import Project.Smalltalk.CallReservation

namespace Project.Smalltalk.CallHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.Reachability

theorem callMethod_eq (p s : Array UInt64) (method arity receiver lex : UInt64) :
    callMethod p s method arity receiver lex =
      if read (reserve s (CallBudget.need p method)) 0 == 4 then reserve s (CallBudget.need p method)
      else sendMethodReady p (reserve s (CallBudget.need p method)) method arity receiver lex := rfl

theorem callMethod_correct {p s : Array UInt64} {cap : Nat} {method arity receiver lex : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4)
    (current : kind s (read s 2) = 5) (bounds : ProgramBounds.Method p method)
    (inputs : BindingPreservation.Inputs s cap (field s (read s 2) 7) (methodAt p method 2) receiver)
    (receiverLive : Live s receiver) (lexLive : Live s lex) (lexType : Matches s cap 5 lex) :
    Heap.Valid (callMethod p s method arity receiver lex) cap ∧
      PointerTypes.Valid (callMethod p s method arity receiver lex) cap ∧
      ((read (callMethod p s method arity receiver lex) 0 = 4 ∧
          read (callMethod p s method arity receiver lex) 15 = 9) ∨
        (read (callMethod p s method arity receiver lex) 0 = read s 0 ∧
          CallConstruction.Effect p (reserve s (CallBudget.need p method))
            (callMethod p s method arity receiver lex) cap method arity receiver lex)) := by
  let need := CallBudget.need p method
  have reserved := Reservation.reserve_correct valid phase need
  have reservedTyped := TypedCollection.reserve_typed valid typed phase need
  rw [callMethod_eq]
  by_cases error : read (reserve s (CallBudget.need p method)) 0 = 4
  · simp only [error, BEq.rfl, ite_true]
    exact ⟨reserved.1, reservedTyped, Or.inl ⟨True.intro, PushReservation.reserve_reason valid phase need error⟩⟩
  · simp only [show (read (reserve s (CallBudget.need p method)) 0 == 4) = false from beq_eq_false_iff_ne.mpr error,
      Bool.false_eq_true, ite_false]
    have afterCurrent := (PushReservation.reserve_current valid phase current need).2
    have afterInputs := CallReservation.reserve_inputs valid typed phase current inputs receiverLive need
    have afterLex := ReturnHeap.reserve_matches valid phase lexLive lexType need
    have room := UInt64.le_iff_toNat_le.mp (PushReservation.reserve_room valid phase need error)
    rw [CallBudget.need_toNat bounds] at room
    have called := CallConstruction.sendMethodReady_effect reserved.1 reservedTyped afterCurrent afterInputs afterLex room
      (arity := arity)
    have samePhase : read (reserve s need) 0 = read s 0 := by
      rcases reserved.2.2.2 with ready | failed
      · exact ready.1
      · exact False.elim (error failed.1)
    exact ⟨called.entry.heap, called.entry.typed, Or.inr ⟨called.phase.trans samePhase, called⟩⟩

end Project.Smalltalk.CallHeap
