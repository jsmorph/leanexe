import Project.Smalltalk.ReturnCallerHeap
import Project.Smalltalk.UnwindHeap
import Project.Smalltalk.TypedCollection
import Project.Smalltalk.PushReservation
import Project.Smalltalk.ReturnDispatch

namespace Project.Smalltalk.ReturnHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.Reachability
open Project.Smalltalk.StackPush Project.Smalltalk.PushReservation Project.Smalltalk.Reservation

theorem reserve_matches {s : Array UInt64} {cap : Nat} {tag value : UInt64}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4) (live : Live s value)
    (matching : Matches s cap tag value) (need : UInt64) : Matches (reserve s need) cap tag value := by
  rcases matching with zero | cell
  · exact Or.inl zero
  · have nonzero : value ≠ 0 := by
      intro zero
      have lower := cell.1.1
      rw [zero] at lower
      contradiction
    have reached : Reachable s value := live.resolve_left nonzero
    exact Or.inr ⟨cell.1, ((reserve_correct valid phase need).2.1 value reached 0 (by decide) (by decide)).trans cell.2⟩

theorem returnReady_valid {s : Array UInt64} {cap : Nat} {stop caller value : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (currentCell : Matches s cap 5 (read s 2)) (callerCell : Matches s cap 5 caller)
    (valueValid : HeapWrite.Value s cap value) (enough : caller ≠ 0 → (1 : UInt64) ≤ read s 9) :
    Heap.Valid (returnReady s stop caller value) cap ∧ PointerTypes.Valid (returnReady s stop caller value) cap := by
  have holds := UnwindHeap.unwind_preserves valid typed currentCell callerCell valueValid stop (read s 14)
  apply ReturnCallerHeap.returnCaller_valid holds.heap holds.typed holds.caller holds.value
  intro nonzero
  rw [holds.registers 9 (by decide)]
  exact enough nonzero

theorem returnReserved_valid {s : Array UInt64} {cap : Nat} {stop caller value : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4)
    (activation : kind s (read s 2) = 5) (callerCell : Matches s cap 5 caller)
    (callerLive : Live s caller) (valueLive : Live s value) :
    Heap.Valid (returnReserved s stop caller value) cap ∧ PointerTypes.Valid (returnReserved s stop caller value) cap := by
  let need : UInt64 := ReturnDispatch.cells caller
  have facts := reserve_correct valid phase need
  have postTyped := TypedCollection.reserve_typed valid typed phase need
  have current := reserve_current valid phase activation need
  have cell := current_facts facts.1.1 current.2
  have callerPost := reserve_matches valid phase callerLive callerCell need
  have valuePost := live_value facts.1.1 (reserve_live valid phase valueLive need)
  rw [ReturnDispatch.returnReserved_eq]
  change Heap.Valid (if read (reserve s need) 0 == 4 then reserve s need else
    returnReady (reserve s need) stop caller value) cap ∧
    PointerTypes.Valid (if read (reserve s need) 0 == 4 then reserve s need else
      returnReady (reserve s need) stop caller value) cap
  by_cases error : read (reserve s need) 0 = 4
  · simp only [error, BEq.rfl, ite_true]
    exact ⟨facts.1, postTyped⟩
  · simp only [show (read (reserve s need) 0 == 4) = false from beq_eq_false_iff_ne.mpr error,
      Bool.false_eq_true, ite_false]
    apply returnReady_valid facts.1 postTyped (Or.inr ⟨cell.1, cell.2.1⟩) callerPost valuePost
    intro nonzero
    have needOne : need = 1 := by
      simp only [need, ReturnDispatch.cells, show (caller == 0) = false from beq_eq_false_iff_ne.mpr nonzero,
        Bool.false_eq_true, ite_false]
    rw [← needOne]
    exact reserve_room valid phase need error

end Project.Smalltalk.ReturnHeap
