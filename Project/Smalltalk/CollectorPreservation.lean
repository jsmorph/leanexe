import Project.Smalltalk.Collector

namespace Project.Smalltalk.CollectorPreservation
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Collector

theorem pointerField_not_mark {tag k : UInt64} (pointer : PointerField tag k) : k ≠ 1 := by
  rcases pointer with ⟨_, rfl⟩ | ⟨_, offsets⟩ | ⟨_, offsets⟩
  · decide
  · rcases offsets with rfl | rfl | rfl | rfl <;> decide
  · rcases offsets with rfl | rfl <;> decide

theorem edge_same {s t : Array UInt64} {parent child : UInt64}
    (payload : ∀ k : UInt64, k.toNat < 8 → k ≠ 1 → field t parent k = field s parent k) :
    Edge t parent child ↔ Edge s parent child := by
  constructor <;> rintro ⟨nonzero, k, bound, pointer, target⟩
  · rw [payload 0 (by decide) (by decide)] at pointer
    rw [payload k bound (pointerField_not_mark pointer)] at target
    exact ⟨nonzero, k, bound, pointer, target⟩
  · have p := pointerField_not_mark pointer
    refine ⟨nonzero, k, bound, ?_, ?_⟩
    · rw [payload 0 (by decide) (by decide)]; exact pointer
    · rw [payload k bound p]; exact target

theorem collect_root {s : Array UInt64} {cap : Nat}
    (valid : Graph.Valid s cap) (phase : read s 0 ≠ 4) (h : UInt64) :
    Root (collect s) h ↔ Root s h := by
  simp only [Root,
    collect_register valid phase (show (2 : UInt64).toNat < 24 by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    collect_register valid phase (show (7 : UInt64).toNat < 24 by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide),
    collect_register valid phase (show (16 : UInt64).toNat < 24 by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem collect_allocated {s : Array UInt64} {cap : Nat} {h : UInt64}
    (valid : Graph.Valid s cap) (phase : read s 0 ≠ 4) (handle : Handle cap h) :
    field (collect s) h 0 ≠ 0 ↔ Reachable s h := by
  classical
  rcases (collect_correct valid phase).2.2 with ⟨nodes, free, members, _⟩
  have zero := (free.2.2 h handle).trans (members h handle)
  constructor
  · intro allocated
    exact Classical.byContradiction (fun unreachable => allocated (zero.mpr unreachable))
  · intro reached unallocated
    exact (zero.mp unallocated) reached

/-- Collection produces another valid typed heap. Every remaining allocated
cell is reachable, and its outgoing pointers still name allocated cells. -/
theorem collect_valid {s : Array UInt64} {cap : Nat}
    (valid : Graph.Valid s cap) (phase : read s 0 ≠ 4) : Graph.Valid (collect s) cap := by
  have facts := collect_correct valid phase
  refine ⟨facts.1, ?_, ?_, ?_⟩
  · intro h root
    have originalRoot := (collect_root valid phase h).mp root
    have original := valid.2.1 h originalRoot
    exact ⟨original.1, (collect_allocated valid phase original.1).mpr (.root originalRoot)⟩
  · intro parent child handle allocated edge
    have parentReach := (collect_allocated valid phase handle).mp allocated
    have originalEdge := (edge_same (facts.2.1 parent parentReach)).mp edge
    have childReach := Reachable.next parentReach originalEdge
    have childHandle := (reachable_allocated valid childReach).1
    exact ⟨childHandle, (collect_allocated valid phase childHandle).mpr childReach⟩
  · intro h handle allocated
    have reached := (collect_allocated valid phase handle).mp allocated
    rw [facts.2.1 h reached 0 (by decide) (by decide)]
    exact valid.2.2.2 h handle (reachable_allocated valid reached).2

theorem collect_reachable {s : Array UInt64} {cap : Nat} {h : UInt64}
    (valid : Graph.Valid s cap) (phase : read s 0 ≠ 4) :
    Reachable (collect s) h ↔ Reachable s h := by
  have facts := collect_correct valid phase
  constructor
  · intro reached
    have allocated := reachable_allocated (collect_valid valid phase) reached
    exact (collect_allocated valid phase allocated.1).mp allocated.2
  · intro reached
    induction reached with
    | root root => exact .root ((collect_root valid phase _).mpr root)
    | @next parent child parentReach edge ih =>
      exact .next ih ((edge_same (facts.2.1 parent parentReach)).mpr edge)

theorem collect_phase {s : Array UInt64} {cap : Nat}
    (valid : Graph.Valid s cap) (phase : read s 0 ≠ 4) : read (collect s) 0 ≠ 4 := by
  rw [collect_register valid phase (show (0 : UInt64).toNat < 24 by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact phase

/-- Two collections without a VM step between them retain the same live cells
and payloads. Collection statistics and free-list order are not compared. -/
theorem collect_twice_payload {s : Array UInt64} {cap : Nat} {h k : UInt64}
    (valid : Graph.Valid s cap) (phase : read s 0 ≠ 4) (reached : Reachable s h)
    (bound : k.toNat < 8) (notMark : k ≠ 1) :
    field (collect (collect s)) h k = field s h k := by
  rw [(collect_correct (collect_valid valid phase) (collect_phase valid phase)).2.1 h
      ((collect_reachable valid phase).mpr reached) k bound notMark,
    (collect_correct valid phase).2.1 h reached k bound notMark]

end Project.Smalltalk.CollectorPreservation
