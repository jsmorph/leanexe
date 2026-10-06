import Project.Smalltalk.AllocationEffect
import Project.Smalltalk.PointerTypes

namespace Project.Smalltalk.TypedAllocation
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.PointerTypes Project.Smalltalk.AllocationEffect Project.Smalltalk.Allocation

def References (s : Array UInt64) (cap : Nat) (tag a b c d e f : UInt64) : Prop :=
  ∀ k : UInt64, k.toNat < 8 → ∀ expected, Required tag k expected →
    Matches s cap expected (allocatedWord tag a b c d e f k)

theorem previous_matches {s t : Array UInt64} {cap : Nat} {tag a b c d e f expected value : UInt64}
    (effect : Effect s t cap tag a b c d e f) (matching : Matches s cap expected value)
    (nonzero : expected ≠ 0) : Matches t cap expected value := by
  rcases matching with zero | child
  · exact Or.inl zero
  · have allocated : field s value 0 ≠ 0 := by rw [child.2]; exact nonzero
    exact Or.inr ⟨child.1, (effect.previous _ child.1 allocated 0 (by decide)).trans child.2⟩

theorem allocate_typed {s : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (valid : Graph.Valid s cap) (typed : PointerTypes.Valid s cap)
    (free : FreeList.Valid s cap (h :: rest)) (tag a b c d e f : UInt64) (supported : ValidTag tag)
    (refs : HeapAllocation.References s cap tag a b c d e f)
    (typedRefs : References s cap tag a b c d e f) :
    PointerTypes.Valid (allocate s tag a b c d e f) cap := by
  have effect := allocate_effect valid free tag a b c d e f supported refs
  intro parent handle allocated k bound expected required
  by_cases fresh : parent = read s 8
  · subst parent
    have newTag : field (allocate s tag a b c d e f) (read s 8) 0 = tag := by
      rw [effect.words 0 (by decide)]; rfl
    rw [newTag] at required
    rw [effect.words k bound]
    exact previous_matches effect (typedRefs k bound expected required) (required_child_nonzero required)
  · have payload := fun (j : UInt64) (offset : j.toNat < 8) =>
      show field (allocate s tag a b c d e f) parent j = field s parent j from by
        rw [FreeList.allocate_success free]
        exact allocateCell_preserves_other valid.1 effect.handle handle offset fresh tag a b c d e f
    rw [payload 0 (by decide)] at allocated required
    rw [payload k bound]
    exact previous_matches effect (typed parent handle allocated k bound expected required)
      (required_child_nonzero required)

theorem link_references {s : Array UInt64} {cap : Nat} {value rest : UInt64}
    (next : Matches s cap 7 rest) : References s cap 7 value rest 0 0 0 0 := by
  intro k _ expected required
  have both : k = 3 ∧ expected = 7 := by simpa [Required] using required
  rcases both with ⟨rfl, rfl⟩
  exact next

theorem scalar_references (s : Array UInt64) (cap : Nat) (tag a b : UInt64)
    (scalar : tag = 1 ∨ tag = 8) : References s cap tag a b 0 0 0 0 := by
  intro k _ expected required
  rcases scalar with rfl | rfl <;> simp [Required] at required

theorem block_references {s : Array UInt64} {cap : Nat} {method capture : UInt64}
    (frame : Matches s cap 5 capture) : References s cap 6 method capture 0 0 0 0 := by
  intro k _ expected required
  have both : k = 3 ∧ expected = 5 := by simpa [Required] using required
  rcases both with ⟨rfl, rfl⟩
  exact frame

end Project.Smalltalk.TypedAllocation
