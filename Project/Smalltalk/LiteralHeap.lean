import Project.Smalltalk.PushReservation

namespace Project.Smalltalk.LiteralHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.HeapWrite Project.Smalltalk.Reachability
open Project.Smalltalk.HeapAllocation Project.Smalltalk.AllocationEffect
open Project.Smalltalk.StackPush Project.Smalltalk.PushReservation Project.Smalltalk.Reservation

theorem remaining_cell {s t : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (original : FreeList.Valid s cap (h :: rest)) (remaining : FreeList.Valid t cap rest)
    (enough : (2 : UInt64) ≤ read s 9) : (1 : UInt64) ≤ read t 9 := by
  have before := original.2.1
  have after := remaining.2.1
  have needed := UInt64.le_iff_toNat_le.mp enough
  change 2 ≤ (read s 9).toNat at needed
  simp only [List.length_cons] at before
  apply UInt64.le_iff_toNat_le.mpr
  change 1 ≤ (read t 9).toNat
  omega

theorem literalReady_valid {s : Array UInt64} {cap : Nat} {tag a b : UInt64}
    (valid : Heap.Valid s cap) (activation : kind s (read s 2) = 5)
    (supported : ValidTag tag) (refs : References s cap tag a b 0 0 0 0)
    (enough : (2 : UInt64) ≤ read s 9) : Heap.Valid (literalReady s tag a b) cap := by
  have current := current_facts valid.1 activation
  have nonzero := validTag_nonzero supported
  have one : (1 : UInt64) ≤ read s 9 := by
    apply UInt64.le_iff_toNat_le.mpr
    have needed := UInt64.le_iff_toNat_le.mp enough
    change 2 ≤ (read s 9).toNat at needed
    change 1 ≤ (read s 9).toNat
    omega
  rcases valid.2 with ⟨nodes, free⟩
  rcases free_nonempty free one with ⟨h, rest, eq⟩
  subst nodes
  have effect := allocate_effect valid.1 free tag a b 0 0 0 0 supported refs
  have tail := (FreeList.allocate_valid valid.1.1 free tag a b 0 0 0 0 nonzero).2
  have act := effect.registers 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have postTag : kind (allocate s tag a b 0 0 0 0) (read (allocate s tag a b 0 0 0 0) 2) = 5 := by
    rw [act, kind_eq_field effect.heap.1.1 current.1,
      effect.previous _ current.1 (by rw [current.2.1]; decide) 0 (by decide)]
    exact current.2.1
  exact pushReady_valid effect.heap postTag (last_value effect nonzero) (remaining_cell free tail enough)

theorem scalar_references (s : Array UInt64) (cap : Nat) (tag a b : UInt64)
    (scalar : tag = 1 ∨ tag = 8) : References s cap tag a b 0 0 0 0 := by
  intro k _ pointer _
  rcases scalar with rfl | rfl <;> simp [PointerField] at pointer

theorem block_references {s : Array UInt64} {cap : Nat} {method capture : UInt64}
    (value : Value s cap capture) : References s cap 6 method capture 0 0 0 0 := by
  intro k _ pointer nonzero
  have offset : k = 3 := by simpa [PointerField] using pointer
  subst k
  simp only [Allocation.allocatedWord] at nonzero ⊢
  exact value_nonzero value nonzero

theorem literal_scalar_valid {s : Array UInt64} {cap : Nat} {tag a b : UInt64}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4)
    (activation : kind s (read s 2) = 5) (scalar : tag = 1 ∨ tag = 8) :
    Heap.Valid (literal s tag a b) cap := by
  have facts := reserve_correct valid phase 2
  have current := reserve_current valid phase activation 2
  have supported : ValidTag tag := by rcases scalar with rfl | rfl <;> simp [ValidTag]
  dsimp only [literal]
  by_cases error : read (reserve s 2) 0 = 4
  · simp only [error, BEq.rfl, ite_true]; exact facts.1
  · simp only [show (read (reserve s 2) 0 == 4) = false from beq_eq_false_iff_ne.mpr error,
      Bool.false_eq_true, ite_false]
    exact literalReady_valid facts.1 current.2 supported (scalar_references _ _ _ _ _ scalar)
      (reserve_room valid phase 2 error)

theorem literal_block_valid {s : Array UInt64} {cap : Nat} {method : UInt64}
    (valid : Heap.Valid s cap) (phase : read s 0 ≠ 4) (activation : kind s (read s 2) = 5) :
    Heap.Valid (literal s 6 method (read s 2)) cap := by
  have facts := reserve_correct valid phase 2
  have current := reserve_current valid phase activation 2
  have capture := live_value facts.1.1 (reserve_live valid phase (root_live s 2 (Or.inl rfl)) 2)
  dsimp only [literal]
  by_cases error : read (reserve s 2) 0 = 4
  · simp only [error, BEq.rfl, ite_true]; exact facts.1
  · simp only [show (read (reserve s 2) 0 == 4) = false from beq_eq_false_iff_ne.mpr error,
      Bool.false_eq_true, ite_false]
    exact literalReady_valid facts.1 current.2 (by simp [ValidTag]) (block_references capture)
      (reserve_room valid phase 2 error)

end Project.Smalltalk.LiteralHeap
