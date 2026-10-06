import Project.Smalltalk.Heap

namespace Project.Smalltalk.HeapAllocation
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Allocation Project.Smalltalk.FreeList Project.Smalltalk.CollectorPreservation

def References (s : Array UInt64) (cap : Nat) (tag a b c d e f : UInt64) : Prop :=
  ∀ k : UInt64, k.toNat < 8 → PointerField tag k → allocatedWord tag a b c d e f k ≠ 0 →
    Handle cap (allocatedWord tag a b c d e f k) ∧ field s (allocatedWord tag a b c d e f k) 0 ≠ 0

theorem validTag_nonzero {tag : UInt64} (valid : ValidTag tag) : tag ≠ 0 := by
  rcases valid with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem allocated_not_head {s : Array UInt64} {cap : Nat} {h g : UInt64} {rest : List UInt64}
    (free : FreeList.Valid s cap (h :: rest)) (allocated : field s g 0 ≠ 0) : g ≠ read s 8 := by
  have head := chain_cons free.1
  intro eq
  rw [eq, head.1] at allocated
  exact allocated head.2.2.1

theorem allocateCell_root {s : Array UInt64} {cap : Nat} (shape : Shape s cap)
    (head : Handle cap (read s 8)) (tag a b c d e f h : UInt64) :
    Root (allocateCell s tag a b c d e f) h ↔ Root s h := by
  simp only [Root, allocateCell_register shape head (show (2 : UInt64).toNat < 24 by decide),
    allocateCell_register shape head (show (7 : UInt64).toNat < 24 by decide),
    allocateCell_register shape head (show (16 : UInt64).toNat < 24 by decide)]
  simp

theorem allocateCell_allocated {s : Array UInt64} {cap : Nat} {g : UInt64}
    (shape : Shape s cap) (head : Handle cap (read s 8)) (handle : Handle cap g)
    (tag a b c d e f : UInt64) (nonzero : tag ≠ 0) (allocated : field s g 0 ≠ 0) :
    field (allocateCell s tag a b c d e f) g 0 ≠ 0 := by
  rw [allocateCell_field shape head handle (show (0 : UInt64).toNat < 8 by decide)]
  by_cases same : g = read s 8
  · simp only [same, ite_true, allocatedWord, ite_true]
    exact nonzero
  · simp only [same, ite_false]
    exact allocated

/-- Allocation preserves a valid graph when the new tag is supported and
every new nonzero pointer names an already allocated valid handle. -/
theorem allocateCell_graph_valid {s : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (valid : Graph.Valid s cap) (free : FreeList.Valid s cap (h :: rest))
    (tag a b c d e f : UInt64) (supported : ValidTag tag) (refs : References s cap tag a b c d e f) :
    Graph.Valid (allocateCell s tag a b c d e f) cap := by
  have originalShape := valid.1
  have facts := chain_cons free.1
  have head : Handle cap (read s 8) := facts.1 ▸ facts.2.1
  have nonzero := validTag_nonzero supported
  have newTag : field (allocateCell s tag a b c d e f) (read s 8) 0 = tag := by
    rw [allocateCell_field originalShape head head (show (0 : UInt64).toNat < 8 by decide)]
    simp only [ite_true, allocatedWord, ite_true]
  refine ⟨allocateCell_shape originalShape head .., ?_, ?_, ?_⟩
  · intro g root
    have original := valid.2.1 g ((allocateCell_root originalShape head tag a b c d e f g).mp root)
    exact ⟨original.1, allocateCell_allocated originalShape head original.1 tag a b c d e f nonzero original.2⟩
  · intro parent child handle allocated edge
    by_cases same : parent = read s 8
    · subst parent
      rcases edge with ⟨childNonzero, k, bound, pointer, eq⟩
      rw [newTag] at pointer
      rw [allocateCell_field originalShape head head bound] at eq
      simp only [ite_true] at eq
      have original := refs k bound pointer (by rw [eq]; exact childNonzero)
      rw [eq] at original
      exact ⟨original.1, allocateCell_allocated originalShape head original.1 tag a b c d e f nonzero original.2⟩
    · have payload := fun (k : UInt64) (bound : k.toNat < 8) (_ : k ≠ 1) =>
        allocateCell_preserves_other originalShape head handle bound same tag a b c d e f
      rw [allocateCell_preserves_other originalShape head handle (show (0 : UInt64).toNat < 8 by decide)
        same tag a b c d e f] at allocated
      have original := valid.2.2.1 parent child handle allocated ((edge_same payload).mp edge)
      exact ⟨original.1, allocateCell_allocated originalShape head original.1 tag a b c d e f nonzero original.2⟩
  · intro g handle allocated
    by_cases same : g = read s 8
    · rw [same, newTag]
      exact supported
    · rw [allocateCell_preserves_other originalShape head handle (show (0 : UInt64).toNat < 8 by decide)
        same tag a b c d e f] at allocated ⊢
      exact valid.2.2.2 g handle allocated

theorem allocate_valid {s : Array UInt64} {cap : Nat} {h : UInt64} {rest : List UInt64}
    (valid : Graph.Valid s cap) (free : FreeList.Valid s cap (h :: rest))
    (tag a b c d e f : UInt64) (supported : ValidTag tag) (refs : References s cap tag a b c d e f) :
    Heap.Valid (allocate s tag a b c d e f) cap := by
  rw [allocate_success free]
  exact ⟨allocateCell_graph_valid valid free tag a b c d e f supported refs,
    rest, allocateCell_valid valid.1 free tag a b c d e f (validTag_nonzero supported)⟩

/-- The fresh cell is not reachable until a VM write links it from a root or
an existing reachable cell. Allocation alone preserves the old reachability. -/
theorem allocateCell_reachable {s : Array UInt64} {cap : Nat} {h g : UInt64} {rest : List UInt64}
    (valid : Graph.Valid s cap) (free : FreeList.Valid s cap (h :: rest)) (tag a b c d e f : UInt64) :
    Reachable (allocateCell s tag a b c d e f) g ↔ Reachable s g := by
  have facts := chain_cons free.1
  have head : Handle cap (read s 8) := facts.1 ▸ facts.2.1
  have payload := fun {parent : UInt64} (reached : Reachable s parent) =>
    fun (k : UInt64) (bound : k.toNat < 8) (_ : k ≠ 1) =>
      allocateCell_preserves_other valid.1 head (reachable_allocated valid reached).1 bound
        (allocated_not_head free (reachable_allocated valid reached).2) tag a b c d e f
  constructor
  · intro reached
    induction reached with
    | root root => exact .root ((allocateCell_root valid.1 head tag a b c d e f _).mp root)
    | next _ edge ih => exact .next ih ((edge_same (payload ih)).mp edge)
  · intro reached
    induction reached with
    | root root => exact .root ((allocateCell_root valid.1 head tag a b c d e f _).mpr root)
    | next parentReach edge ih => exact .next ih ((edge_same (payload parentReach)).mpr edge)

theorem allocate_empty_valid {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap)
    (free : FreeList.Valid s cap []) (tag a b c d e f : UInt64) :
    Heap.Valid (allocate s tag a b c d e f) cap := by
  rw [allocate_empty free]
  exact Heap.fail_valid ⟨valid, [], free⟩ 9

end Project.Smalltalk.HeapAllocation
