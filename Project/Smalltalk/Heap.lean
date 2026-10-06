import Project.Smalltalk.CollectorPreservation

namespace Project.Smalltalk.Heap
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.Collector Project.Smalltalk.CollectorPreservation

def Valid (s : Array UInt64) (cap : Nat) : Prop :=
  Graph.Valid s cap ∧ ∃ nodes, Project.Smalltalk.FreeList.Valid s cap nodes

theorem fail_shape {s : Array UInt64} {cap : Nat} (shape : Shape s cap) (reason : UInt64) :
    Shape (fail s reason) cap := write_shape (write_shape shape (by decide)) (by decide)

theorem fail_field {s : Array UInt64} {cap : Nat} {h k : UInt64} (shape : Shape s cap)
    (handle : Handle cap h) (bound : k.toNat < 8) (reason : UInt64) :
    field (fail s reason) h k = field s h k := by
  rw [field, fail_read shape]
  simp only [cell_index_not_register shape.2.1 handle bound (show (15 : UInt64).toNat < 24 by decide),
    cell_index_not_register shape.2.1 handle bound (show (0 : UInt64).toNat < 24 by decide), ite_false, field]

theorem fail_root {s : Array UInt64} {cap : Nat} (shape : Shape s cap) (reason h : UInt64) :
    Root (fail s reason) h ↔ Root s h := by
  simp only [Root, fail_read shape]
  simp

theorem fail_graph_valid {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap) (reason : UInt64) :
    Graph.Valid (fail s reason) cap := by
  have shape := valid.1
  refine ⟨fail_shape shape reason, ?_, ?_, ?_⟩
  · intro h root
    have original := valid.2.1 h ((fail_root shape reason h).mp root)
    rw [fail_field shape original.1 (show (0 : UInt64).toNat < 8 by decide)]
    exact original
  · intro parent child handle allocated edge
    have same := fun (k : UInt64) (bound : k.toNat < 8) (_ : k ≠ 1) => fail_field shape handle bound reason
    rw [fail_field shape handle (show (0 : UInt64).toNat < 8 by decide)] at allocated
    have original := valid.2.2.1 parent child handle allocated ((edge_same same).mp edge)
    rw [fail_field shape original.1 (show (0 : UInt64).toNat < 8 by decide)]
    exact original
  · intro h handle allocated
    rw [fail_field shape handle (show (0 : UInt64).toNat < 8 by decide)] at allocated ⊢
    exact valid.2.2.2 h handle allocated

theorem fail_valid {s : Array UInt64} {cap : Nat} (valid : Valid s cap) (reason : UInt64) :
    Valid (fail s reason) cap := by
  rcases valid.2 with ⟨nodes, free⟩
  refine ⟨fail_graph_valid valid.1 reason, nodes, ?_⟩
  apply Project.Smalltalk.FreeList.valid_transfer free
  · rw [fail_read valid.1.1]; simp
  · rw [fail_read valid.1.1]; simp
  · intro h handle
    exact ⟨fail_field valid.1.1 handle (by decide) reason, fail_field valid.1.1 handle (by decide) reason⟩

theorem fail_reachable {s : Array UInt64} {cap : Nat} {h : UInt64}
    (valid : Graph.Valid s cap) (reason : UInt64) : Reachable (fail s reason) h ↔ Reachable s h := by
  constructor
  · intro reached
    induction reached with
    | root root => exact .root ((fail_root valid.1 reason _).mp root)
    | @next parent child _ edge ih =>
      have handle := (reachable_allocated valid ih).1
      exact .next ih ((edge_same (fun k bound _ => fail_field valid.1 handle bound reason)).mp edge)
  · intro reached
    induction reached with
    | root root => exact .root ((fail_root valid.1 reason _).mpr root)
    | @next parent child parentReach edge ih =>
      have handle := (reachable_allocated valid parentReach).1
      exact .next ih ((edge_same (fun k bound _ => fail_field valid.1 handle bound reason)).mpr edge)

theorem collect_valid {s : Array UInt64} {cap : Nat} (valid : Graph.Valid s cap) (phase : read s 0 ≠ 4) :
    Valid (collect s) cap := by
  rcases (collect_correct valid phase).2.2 with ⟨nodes, free, _⟩
  exact ⟨CollectorPreservation.collect_valid valid phase, nodes, free⟩

end Project.Smalltalk.Heap
