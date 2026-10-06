import Project.Smalltalk.AllocationEffect
import Project.Smalltalk.Reachability
import Project.Smalltalk.FrameHeap
import Project.Smalltalk.Reservation

namespace Project.Smalltalk.StackPush
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.HeapWrite Project.Smalltalk.Reachability
open Project.Smalltalk.HeapAllocation Project.Smalltalk.AllocationEffect
open Project.Smalltalk.Allocation Project.Smalltalk.FreeList

theorem value_nonzero {s : Array UInt64} {cap : Nat} {value : UInt64}
    (valid : Value s cap value) (nonzero : value ≠ 0) : Handle cap value ∧ field s value 0 ≠ 0 := by
  rcases valid with zero | allocated
  · exact False.elim (nonzero zero)
  · exact allocated

theorem link_references {s : Array UInt64} {cap : Nat} {value rest : UInt64}
    (valueValid : Value s cap value) (restValid : Value s cap rest) : References s cap 7 value rest 0 0 0 0 := by
  intro k _ pointer nonzero
  have cases : k = 2 ∨ k = 3 := by simpa [PointerField] using pointer
  rcases cases with rfl | rfl
  · simp only [allocatedWord] at nonzero ⊢
    exact value_nonzero valueValid nonzero
  · simp only [allocatedWord] at nonzero ⊢
    exact value_nonzero restValid nonzero

theorem current_facts {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (activation : kind s (read s 2) = 5) :
    Handle cap (read s 2) ∧ field s (read s 2) 0 = 5 ∧ Value s cap (field s (read s 2) 7) := by
  have handle := kind_handle valid.1 (by decide) activation
  have tag : field s (read s 2) 0 = 5 := (kind_eq_field valid.1 handle).symm.trans activation
  exact ⟨handle, tag, pointer_value valid handle (by rw [tag]; decide)
    (show (7 : UInt64).toNat < 8 by decide) (by rw [tag]; simp [PointerField])⟩

theorem pushReady_valid {s : Array UInt64} {cap : Nat} {value : UInt64}
    (valid : Heap.Valid s cap) (activation : kind s (read s 2) = 5)
    (valueValid : Value s cap value) (enough : (1 : UInt64) ≤ read s 9) : Heap.Valid (pushReady s value) cap := by
  have act := current_facts valid.1 activation
  rcases valid.2 with ⟨nodes, free⟩
  rcases free_nonempty free enough with ⟨h, rest, eq⟩
  subst nodes
  have effect := allocate_effect valid.1 free 7 value (field s (read s 2) 7) 0 0 0 0
    (by simp [ValidTag]) (link_references valueValid act.2.2)
  have current := effect.registers 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have originalAllocated : field s (read s 2) 0 ≠ 0 := by rw [act.2.1]; decide
  change Heap.Valid (advance (allocate s 7 value (field s (read s 2) 7) 0 0 0 0)
    (read (allocate s 7 value (field s (read s 2) 7) 0 0 0 0) 10)) cap
  apply FrameHeap.advance_valid effect.heap
  · rw [current]; exact act.1
  · rw [current, effect.previous _ act.1 originalAllocated 0 (by decide)]; exact act.2.1
  · exact last_value effect (by decide)

theorem pushReady_delivers {s : Array UInt64} {cap : Nat} {value : UInt64}
    (valid : Heap.Valid s cap) (activation : kind s (read s 2) = 5)
    (valueValid : Value s cap value) (enough : (1 : UInt64) ≤ read s 9) :
    ∃ h, Handle cap h ∧ read (pushReady s value) 2 = read s 2 ∧
      field (pushReady s value) (read s 2) 3 = field s (read s 2) 3 + 1 ∧
      field (pushReady s value) (read s 2) 7 = h ∧
      field (pushReady s value) h 0 = 7 ∧ field (pushReady s value) h 2 = value ∧
      field (pushReady s value) h 3 = field s (read s 2) 7 := by
  have act := current_facts valid.1 activation
  have allocated : field s (read s 2) 0 ≠ 0 := by rw [act.2.1]; decide
  rcases valid.2 with ⟨nodes, free⟩
  rcases free_nonempty free enough with ⟨h, rest, eq⟩
  subst nodes
  let t := allocate s 7 value (field s (read s 2) 7) 0 0 0 0
  have effect : Effect s t cap 7 value (field s (read s 2) 7) 0 0 0 0 :=
    allocate_effect valid.1 free 7 value (field s (read s 2) 7) 0 0 0 0
      (by simp [ValidTag]) (link_references valueValid act.2.2)
  have current := effect.registers 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have handle : Handle cap (read t 2) := by rw [current]; exact act.1
  have different : read s 8 ≠ read t 2 := by rw [current]; exact Ne.symm (allocated_not_head free allocated)
  change ∃ h, Handle cap h ∧ read (advance t (read t 10)) 2 = read s 2 ∧
    field (advance t (read t 10)) (read s 2) 3 = field s (read s 2) 3 + 1 ∧
    field (advance t (read t 10)) (read s 2) 7 = h ∧
    field (advance t (read t 10)) h 0 = 7 ∧ field (advance t (read t 10)) h 2 = value ∧
    field (advance t (read t 10)) h 3 = field s (read s 2) 7
  refine ⟨read s 8, effect.handle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Frame.advance_register effect.heap.1.1 handle (show (2 : UInt64).toNat < 24 by decide), current]
  · rw [Frame.advance_field effect.heap.1.1 handle act.1 (show (3 : UInt64).toNat < 8 by decide), current]
    simp [effect.previous _ act.1 allocated 3 (by decide)]
  · rw [Frame.advance_field effect.heap.1.1 handle act.1 (show (7 : UInt64).toNat < 8 by decide), current]
    simp [effect.last]
  · rw [Frame.advance_field effect.heap.1.1 handle effect.handle (show (0 : UInt64).toNat < 8 by decide)]
    simp [different, effect.words 0 (by decide), allocatedWord]
  · rw [Frame.advance_field effect.heap.1.1 handle effect.handle (show (2 : UInt64).toNat < 8 by decide)]
    simp [different, effect.words 2 (by decide), allocatedWord]
  · rw [Frame.advance_field effect.heap.1.1 handle effect.handle (show (3 : UInt64).toNat < 8 by decide)]
    simp [different, effect.words 3 (by decide), allocatedWord]

end Project.Smalltalk.StackPush
