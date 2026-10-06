import Project.Smalltalk.TypedAllocation
import Project.Smalltalk.StackPush

namespace Project.Smalltalk.ReturnCallerHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.AllocationEffect

theorem returnCallerReady_valid {s : Array UInt64} {cap : Nat} {caller value : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap)
    (callerCell : Matches s cap 5 caller) (nonzero : caller ≠ 0)
    (valueValid : HeapWrite.Value s cap value) (enough : (1 : UInt64) ≤ read s 9) :
    Heap.Valid (returnCallerReady s caller value) cap ∧ PointerTypes.Valid (returnCallerReady s caller value) cap := by
  have callerFacts : Handle cap caller ∧ field s caller 0 = 5 := callerCell.resolve_left nonzero
  have callerAllocated : field s caller 0 ≠ 0 := by rw [callerFacts.2]; decide
  have restValue := Reachability.pointer_value valid.1 callerFacts.1 callerAllocated
    (show (7 : UInt64).toNat < 8 by decide) (by rw [callerFacts.2]; simp [PointerField])
  have restType := typed caller callerFacts.1 callerAllocated 7 (by decide) 7 (by
    rw [callerFacts.2]; simp [Required])
  rcases valid.2 with ⟨nodes, free⟩
  rcases free_nonempty free enough with ⟨head, rest, eq⟩
  subst nodes
  let t := allocate s 7 value (field s caller 7) 0 0 0 0
  have refs := StackPush.link_references valueValid restValue
  have effect : Effect s t cap 7 value (field s caller 7) 0 0 0 0 :=
    allocate_effect valid.1 free 7 value (field s caller 7) 0 0 0 0 (by simp [ValidTag]) refs
  have newTyped : PointerTypes.Valid t cap := TypedAllocation.allocate_typed valid.1 typed free
    7 value (field s caller 7) 0 0 0 0 (by simp [ValidTag]) refs (TypedAllocation.link_references restType)
  have callerValue := previous_value effect (matches_value callerCell (by decide))
  have rootHeap := HeapWrite.write_register_valid effect.heap (show (2 : UInt64).toNat < 24 by decide)
    (show (2 : UInt64) ≠ 14 by decide) (by decide) (by decide) (fun _ => callerValue) (v := caller)
  have rootTyped := PointerTypes.write_register_valid effect.heap.1.1 newTyped
    (show (2 : UInt64).toNat < 24 by decide) (v := caller)
  have callerTag : field (write t 2 caller) caller 0 = 5 := by
    rw [field_write_register effect.heap.1.1 callerFacts.1 (show (0 : UInt64).toNat < 8 by decide)
      (show (2 : UInt64).toNat < 24 by decide), effect.previous caller callerFacts.1 callerAllocated 0 (by decide)]
    exact callerFacts.2
  have headValue := HeapWrite.value_after_register effect.heap.1.1 (show (2 : UInt64).toNat < 24 by decide)
    (last_value effect (by decide)) (v := caller)
  have headType : Matches t cap 7 (read t 10) := by
    rw [effect.last]
    exact Or.inr ⟨effect.handle, by rw [effect.words 0 (by decide)]; rfl⟩
  change Heap.Valid (write (write t 2 caller) (address caller + 7) (read t 10)) cap ∧
    PointerTypes.Valid (write (write t 2 caller) (address caller + 7) (read t 10)) cap
  constructor
  · exact HeapWrite.write_cell_valid rootHeap callerFacts.1 (by rw [callerTag]; decide)
      (show (7 : UInt64).toNat < 8 by decide) (by decide) (fun _ => headValue)
  · apply PointerTypes.write_cell_valid rootHeap.1.1 rootTyped callerFacts.1
      (show (7 : UInt64).toNat < 8 by decide) (show (7 : UInt64) ≠ 0 by decide)
    intro expected required
    rw [callerTag] at required
    have expectedTag : expected = 7 := by simpa [Required] using required
    subst expected
    exact matches_after_register effect.heap.1.1 (show (2 : UInt64).toNat < 24 by decide) headType

theorem return_final_valid {s : Array UInt64} {cap : Nat} {value : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (valueValid : HeapWrite.Value s cap value) :
    Heap.Valid (write (write (write s 0 3) 2 0) 7 value) cap ∧
    PointerTypes.Valid (write (write (write s 0 3) 2 0) 7 value) cap := by
  have phase := HeapWrite.write_register_valid valid (show (0 : UInt64).toNat < 24 by decide)
    (show (0 : UInt64) ≠ 14 by decide) (by decide) (by decide) (by intro root; simp at root) (v := 3)
  have phaseTyped := PointerTypes.write_register_valid valid.1.1 typed
    (show (0 : UInt64).toNat < 24 by decide) (v := 3)
  have current := HeapWrite.write_register_valid phase (show (2 : UInt64).toNat < 24 by decide)
    (show (2 : UInt64) ≠ 14 by decide) (by decide) (by decide) (fun _ => Or.inl rfl) (v := 0)
  have currentTyped := PointerTypes.write_register_valid phase.1.1 phaseTyped
    (show (2 : UInt64).toNat < 24 by decide) (v := 0)
  have preserved := HeapWrite.value_after_register phase.1.1 (show (2 : UInt64).toNat < 24 by decide)
    (HeapWrite.value_after_register valid.1.1 (show (0 : UInt64).toNat < 24 by decide) valueValid (v := 3)) (v := 0)
  exact ⟨HeapWrite.write_register_valid current (show (7 : UInt64).toNat < 24 by decide)
      (by decide) (by decide) (by decide) (fun _ => preserved),
    PointerTypes.write_register_valid current.1.1 currentTyped (show (7 : UInt64).toNat < 24 by decide)⟩

theorem returnCaller_valid {s : Array UInt64} {cap : Nat} {caller value : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (callerCell : Matches s cap 5 caller)
    (valueValid : HeapWrite.Value s cap value) (enough : caller ≠ 0 → (1 : UInt64) ≤ read s 9) :
    Heap.Valid (returnCaller s caller value) cap ∧ PointerTypes.Valid (returnCaller s caller value) cap := by
  by_cases zero : caller = 0
  · simp only [returnCaller, zero, BEq.rfl, ite_true]
    exact return_final_valid valid typed valueValid
  · simp only [returnCaller, show (caller == 0) = false from beq_eq_false_iff_ne.mpr zero,
      Bool.false_eq_true, ite_false]
    exact returnCallerReady_valid valid typed callerCell zero valueValid (enough zero)

end Project.Smalltalk.ReturnCallerHeap
