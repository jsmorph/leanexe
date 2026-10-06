import Project.Smalltalk.CallInputs
import Project.Smalltalk.ReturnHeap

namespace Project.Smalltalk.CallReservation
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.Reachability

theorem reserve_args {s : Array UInt64} {cap : Nat}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4) (current : kind s (read s 2) = 5) (need : UInt64) :
    field (reserve s need) (read (reserve s need) 2) 7 = field s (read s 2) 7 := by
  have after := PushReservation.reserve_current valid phase current need
  have reached := live_reached (root_live s 2 (Or.inl rfl)) (by decide) current
  rw [after.1]
  exact (Reservation.reserve_correct valid phase need).2.1 _ reached 7 (by decide) (by decide)

theorem reserve_inputs {s : Array UInt64} {cap : Nat} {arity receiver : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4)
    (current : kind s (read s 2) = 5)
    (inputs : BindingPreservation.Inputs s cap (field s (read s 2) 7) arity receiver)
    (receiverLive : Live s receiver) (need : UInt64) :
    BindingPreservation.Inputs (reserve s need) cap (field (reserve s need) (read (reserve s need) 2) 7) arity receiver := by
  have reserved := Reservation.reserve_correct valid phase need
  have afterInputs := ArgumentTransfer.inputs_transfer valid.1 typed reserved.1.1.1 (CallInputs.args_live current) inputs
    (fun h reached _ k bound nonmark => reserved.2.1 h reached k bound nonmark)
    (live_value reserved.1.1 (PushReservation.reserve_live valid phase receiverLive need))
  rw [reserve_args valid phase current need]
  exact afterInputs

end Project.Smalltalk.CallReservation
