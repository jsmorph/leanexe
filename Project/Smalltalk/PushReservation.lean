import Project.Smalltalk.StackPush
import Project.Smalltalk.PushDispatch

namespace Project.Smalltalk.PushReservation
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.HeapWrite Project.Smalltalk.Reachability
open Project.Smalltalk.StackPush Project.Smalltalk.Reservation

theorem reserve_live {s : Array UInt64} {cap : Nat} {value : UInt64}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4) (live : Live s value) (need : UInt64) :
    Live (reserve s need) value := by
  rcases live with zero | reached
  · exact Or.inl zero
  · exact Or.inr (((reserve_correct valid phase need).2.2.1 value).mpr reached)

theorem reserve_current {s : Array UInt64} {cap : Nat}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4)
    (activation : kind s (read s 2) = 5) (need : UInt64) :
    read (reserve s need) 2 = read s 2 ∧ kind (reserve s need) (read (reserve s need) 2) = 5 := by
  have current := current_facts valid.1 activation
  have reached := live_reached (root_live s 2 (Or.inl rfl)) (by decide) activation
  have facts := reserve_correct valid phase need
  have register := reserve_register valid phase need (show (2 : UInt64).toNat < 24 by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨register, ?_⟩
  rw [register, kind_eq_field facts.1.1.1 current.1,
    facts.2.1 _ reached 0 (by decide) (by decide)]
  exact current.2.1

theorem reserve_room {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (need : UInt64) (success : read (reserve s need) 0 ≠ 4) :
    need ≤ read (reserve s need) 9 := by
  rcases (reserve_correct valid phase need).2.2.2 with ready | failed
  · exact ready.2
  · exact False.elim (success failed.1)

theorem reserve_reason {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (phase : read s 0 ≠ 4) (need : UInt64) (error : read (reserve s need) 0 = 4) :
    read (reserve s need) 15 = 9 := by
  rcases (reserve_correct valid phase need).2.2.2 with ready | failed
  · exact False.elim (phase (ready.1.symm.trans error))
  · exact failed.2

theorem push_correct {s : Array UInt64} {cap : Nat} {value : UInt64}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4)
    (activation : kind s (read s 2) = 5) (live : Live s value) :
    Heap.Valid (push s value) cap ∧
    ((read (push s value) 0 = 4 ∧ read (push s value) 15 = 9) ∨
      ∃ h, Handle cap h ∧ read (push s value) 2 = read s 2 ∧
        field (push s value) (read s 2) 3 = field s (read s 2) 3 + 1 ∧
        field (push s value) (read s 2) 7 = h ∧
        field (push s value) h 0 = 7 ∧ field (push s value) h 2 = value ∧
        field (push s value) h 3 = field s (read s 2) 7) := by
  have facts := reserve_correct valid phase 1
  have current := reserve_current valid phase activation 1
  have reached := live_reached (root_live s 2 (Or.inl rfl)) (by decide) activation
  by_cases error : read (reserve s 1) 0 = 4
  · rw [PushDispatch.push_error s value error]
    exact ⟨facts.1, Or.inl ⟨error, reserve_reason valid phase 1 error⟩⟩
  · have room := reserve_room valid phase 1 error
    have valueValid := live_value facts.1.1 (reserve_live valid phase live 1)
    have delivered := pushReady_delivers facts.1 current.2 valueValid room
    rw [current.1, facts.2.1 _ reached 3 (by decide) (by decide),
      facts.2.1 _ reached 7 (by decide) (by decide)] at delivered
    rw [PushDispatch.push_success s value error]
    exact ⟨pushReady_valid facts.1 current.2 valueValid room, Or.inr delivered⟩

theorem loadSlot_valid {s : Array UInt64} {cap : Nat} {slot : UInt64}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4)
    (activation : kind s (read s 2) = 5) (live : Live s slot)
    (cell : slot = 0 ∨ kind s slot = 7) : Heap.Valid (loadSlot s slot) cap := by
  by_cases zero : slot = 0
  · simp only [loadSlot, zero, BEq.rfl, ite_true]
    exact Heap.fail_valid valid 2
  · have tag := cell.resolve_left zero
    have reached := live_reached live (by decide) tag
    have valueLive := pointer_live reached (show (2 : UInt64).toNat < 8 by decide) (by
      rw [← kind_eq_field valid.1.1 (reachable_allocated valid.1 reached).1, tag]
      simp [PointerField])
    simp only [loadSlot, show (slot == 0) = false from beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false]
    exact (push_correct valid phase activation valueLive).1

end Project.Smalltalk.PushReservation
