import Project.Smalltalk.PointerTypes
import Project.Smalltalk.InitializationFree
import Project.Smalltalk.Reservation

namespace Project.Smalltalk.TypedCollection
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.PointerTypes Project.Smalltalk.Collector Project.Smalltalk.CollectorPreservation

theorem collect_typed {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4) : PointerTypes.Valid (collect s) cap := by
  intro parent handle allocated k bound tag required
  have reached := (collect_allocated valid phase handle).mp allocated
  have payload := (collect_correct valid phase).2.1
  have sameTag := payload parent reached 0 (by decide) (by decide)
  rw [sameTag] at required
  have notMark := pointerField_not_mark (required_pointer required)
  rw [payload parent reached k bound notMark]
  rcases typed parent handle (reachable_allocated valid reached).2 k bound tag required with zero | child
  · exact Or.inl zero
  · have nonzero : field s parent k ≠ 0 := by
      intro zero
      have lower := child.1.1
      rw [zero] at lower
      contradiction
    have childReach := Reachable.next reached ⟨nonzero, k, bound, required_pointer required, rfl⟩
    exact Or.inr ⟨child.1, (payload _ childReach 0 (by decide) (by decide)).trans child.2⟩

theorem fail_typed {s : Array UInt64} {cap : Nat} (shape : Shape s cap)
    (typed : PointerTypes.Valid s cap) (reason : UInt64) : PointerTypes.Valid (fail s reason) cap :=
  write_register_valid (write_shape shape (show (0 : UInt64) ≠ 14 by decide))
    (write_register_valid shape typed (show (0 : UInt64).toNat < 24 by decide))
    (show (15 : UInt64).toNat < 24 by decide)

theorem init_typed (requested stress : UInt64) :
    PointerTypes.Valid (init requested stress) (InitializationBase.capacity requested).toNat := by
  intro parent handle allocated k _ tag required
  have tagTwo : field (init requested stress) parent 0 = 2 := by
    rw [InitializationGraph.init_tag requested stress handle]
    by_cases canonical : parent ≤ 3
    · simp only [canonical, ite_true]
    · have zero : field (init requested stress) parent 0 = 0 := by
        rw [InitializationGraph.init_tag requested stress handle]; simp only [canonical, ite_false]
      exact False.elim (allocated zero)
  rw [tagTwo] at required
  simp [Required] at required

theorem stress_typed {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4) (need : UInt64) :
    PointerTypes.Valid (stressCollection s need) cap := by
  unfold stressCollection
  split
  · exact collect_typed valid typed phase
  · exact typed

theorem space_typed {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4) (need : UInt64) :
    PointerTypes.Valid (spaceCollection s need) cap := by
  unfold spaceCollection
  split
  · exact collect_typed valid typed phase
  · exact typed

theorem reserve_typed {s : Array UInt64} {cap : Nat} (valid : Heap.Valid s cap)
    (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4) (need : UInt64) :
    PointerTypes.Valid (reserve s need) cap := by
  have first := Reservation.stress_effect valid phase need
  have firstTyped := stress_typed valid.1 typed phase need
  have firstPhase : read (stressCollection s need) 0 ≠ 4 := by
    rw [Reservation.effect_phase first]; exact phase
  have prepared := Reservation.prepared_effect valid phase need
  have preparedTyped := space_typed first.heap.1 firstTyped firstPhase need
  rw [Reservation.reserve_eq valid phase need]
  split
  · exact fail_typed prepared.heap.1.1 preparedTyped 9
  · exact preparedTyped

end Project.Smalltalk.TypedCollection
