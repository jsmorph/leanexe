import Project.Smalltalk.HeapWrite

namespace Project.Smalltalk.AllocationEffect
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Allocation Project.Smalltalk.FreeList Project.Smalltalk.HeapAllocation

structure Effect (s t : Array UInt64) (cap : Nat) (tag a b c d e f : UInt64) : Prop where
  heap : Heap.Valid t cap
  handle : Handle cap (read s 8)
  last : read t 10 = read s 8
  words : ∀ k : UInt64, k.toNat < 8 → field t (read s 8) k = allocatedWord tag a b c d e f k
  previous : ∀ h : UInt64, Handle cap h → field s h 0 ≠ 0 →
    ∀ k : UInt64, k.toNat < 8 → field t h k = field s h k
  registers : ∀ r : UInt64, r.toNat < 24 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 13 → r ≠ 17 →
    read t r = read s r

theorem allocate_effect {s : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (valid : Graph.Valid s cap) (free : FreeList.Valid s cap (h :: rest))
    (tag a b c d e f : UInt64) (supported : ValidTag tag) (refs : References s cap tag a b c d e f) :
    Effect s (allocate s tag a b c d e f) cap tag a b c d e f := by
  have facts := chain_cons free.1
  have handle : Handle cap (read s 8) := facts.1 ▸ facts.2.1
  refine ⟨allocate_valid valid free tag a b c d e f supported refs, handle, ?_, ?_, ?_, ?_⟩
  · rw [allocate_success free, allocateCell_register valid.1 handle (show (10 : UInt64).toNat < 24 by decide)]
    simp
  · intro k bound
    rw [allocate_success free, allocateCell_field valid.1 handle handle bound]
    simp only [ite_true]
  · intro g other allocated k bound
    rw [allocate_success free]
    exact allocateCell_preserves_other valid.1 handle other bound (allocated_not_head free allocated) ..
  · intro r bound h8 h9 h10 h13 h17
    rw [allocate_success free, allocateCell_register valid.1 handle bound]
    simp only [h8, h9, h10, h13, h17, ite_false]

theorem previous_value {s t : Array UInt64} {cap : Nat} {tag a b c d e f value : UInt64}
    (effect : Effect s t cap tag a b c d e f) (original : HeapWrite.Value s cap value) :
    HeapWrite.Value t cap value := by
  rcases original with zero | allocated
  · exact Or.inl zero
  · exact Or.inr ⟨allocated.1, by rw [effect.previous value allocated.1 allocated.2 0 (by decide)]; exact allocated.2⟩

theorem last_value {s t : Array UInt64} {cap : Nat} {tag a b c d e f : UInt64}
    (effect : Effect s t cap tag a b c d e f) (nonzero : tag ≠ 0) : HeapWrite.Value t cap (read t 10) := by
  rw [effect.last]
  refine Or.inr ⟨effect.handle, ?_⟩
  rw [effect.words 0 (by decide)]
  exact nonzero

theorem free_nonempty {s : Array UInt64} {cap : Nat} {nodes : List UInt64}
    (free : FreeList.Valid s cap nodes) (enough : (1 : UInt64) ≤ read s 9) : ∃ h rest, nodes = h :: rest := by
  cases nodes with
  | nil =>
    have count : (read s 9).toNat = 0 := free.2.1
    have positive : 1 ≤ (read s 9).toNat := UInt64.le_iff_toNat_le.mp enough
    omega
  | cons h rest => exact ⟨h, rest, rfl⟩

end Project.Smalltalk.AllocationEffect
