import Project.Smalltalk.HeapAllocation

namespace Project.Smalltalk.HeapWrite
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.FreeList

def Value (s : Array UInt64) (cap : Nat) (v : UInt64) : Prop :=
  v = 0 ∨ (Handle cap v ∧ field s v 0 ≠ 0)

theorem cell_register {s : Array UInt64} {cap : Nat} {h k v r : UInt64}
    (shape : Shape s cap) (handle : Handle cap h) (offset : k.toNat < 8) (bound : r.toNat < 24) :
    read (write s (address h + k) v) r = read s r :=
  read_write_other _ _ _ _ (cell_index_not_register shape.2.1 handle offset bound)

theorem cell_tag {s : Array UInt64} {cap : Nat} {h k v g : UInt64}
    (shape : Shape s cap) (handle : Handle cap h) (offset : k.toNat < 8) (notTag : k ≠ 0)
    (other : Handle cap g) : field (write s (address h + k) v) g 0 = field s g 0 := by
  rw [field_write_cell shape handle other offset (show (0 : UInt64).toNat < 8 by decide)]
  simp only [Ne.symm notTag, and_false, ite_false]

theorem cell_root {s : Array UInt64} {cap : Nat} {h k v g : UInt64}
    (shape : Shape s cap) (handle : Handle cap h) (offset : k.toNat < 8) :
    Root (write s (address h + k) v) g ↔ Root s g := by
  simp only [Root, cell_register shape handle offset (show (2 : UInt64).toNat < 24 by decide),
    cell_register shape handle offset (show (7 : UInt64).toNat < 24 by decide),
    cell_register shape handle offset (show (16 : UInt64).toNat < 24 by decide)]

theorem write_cell_graph_valid {s : Array UInt64} {cap : Nat} {h k v : UInt64}
    (valid : Graph.Valid s cap) (handle : Handle cap h) (offset : k.toNat < 8) (notTag : k ≠ 0)
    (reference : PointerField (field s h 0) k → Value s cap v) :
    Graph.Valid (write s (address h + k) v) cap := by
  have shape := valid.1
  refine ⟨write_shape shape (cell_index_not_register shape.2.1 handle offset (by decide)), ?_, ?_, ?_⟩
  · intro g root
    have original := valid.2.1 g ((cell_root shape handle offset).mp root)
    rw [cell_tag shape handle offset notTag original.1]
    exact original
  · intro parent child parentHandle allocated edge
    rw [cell_tag shape handle offset notTag parentHandle] at allocated
    rcases edge with ⟨childNonzero, j, bound, pointer, eq⟩
    rw [cell_tag shape handle offset notTag parentHandle] at pointer
    rw [field_write_cell shape handle parentHandle offset bound] at eq
    have childValid : Handle cap child ∧ field s child 0 ≠ 0 := by
      by_cases changed : parent = h ∧ j = k
      · rcases changed with ⟨rfl, rfl⟩
        simp only [true_and, ite_true] at eq
        rcases reference pointer with zero | allocated
        · exact False.elim (childNonzero (eq.symm.trans zero))
        · rw [eq] at allocated
          exact allocated
      · simp only [changed, ite_false] at eq
        exact valid.2.2.1 parent child parentHandle allocated ⟨childNonzero, j, bound, pointer, eq⟩
    rw [cell_tag shape handle offset notTag childValid.1]
    exact childValid
  · intro g other allocated
    rw [cell_tag shape handle offset notTag other] at allocated ⊢
    exact valid.2.2.2 g other allocated

theorem write_cell_free {s : Array UInt64} {cap : Nat} {h k v : UInt64} {nodes : List UInt64}
    (shape : Shape s cap) (free : FreeList.Valid s cap nodes) (handle : Handle cap h)
    (allocated : field s h 0 ≠ 0) (offset : k.toNat < 8) (notTag : k ≠ 0) :
    FreeList.Valid (write s (address h + k) v) cap nodes := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cell_register shape handle offset (show (8 : UInt64).toNat < 24 by decide)]
    apply chain_transfer free.1
    intro g member
    have other := chain_handle free.1 member
    have different : g ≠ h := by
      intro eq
      have zero := chain_tag free.1 member
      rw [eq] at zero
      exact allocated zero
    constructor
    · exact cell_tag shape handle offset notTag other
    · rw [field_write_cell shape handle other offset (show (2 : UInt64).toNat < 8 by decide)]
      simp only [different, false_and, ite_false]
  · rw [cell_register shape handle offset (show (9 : UInt64).toNat < 24 by decide)]
    exact free.2.1
  · intro g other
    rw [cell_tag shape handle offset notTag other]
    exact free.2.2 g other

theorem write_cell_valid {s : Array UInt64} {cap : Nat} {h k v : UInt64}
    (valid : Heap.Valid s cap) (handle : Handle cap h) (allocated : field s h 0 ≠ 0)
    (offset : k.toNat < 8) (notTag : k ≠ 0) (reference : PointerField (field s h 0) k → Value s cap v) :
    Heap.Valid (write s (address h + k) v) cap := by
  rcases valid.2 with ⟨nodes, free⟩
  exact ⟨write_cell_graph_valid valid.1 handle offset notTag reference,
    nodes, write_cell_free valid.1.1 free handle allocated offset notTag⟩

theorem register_root {s : Array UInt64} {cap : Nat} {r v h : UInt64}
    (shape : Shape s cap) (bound : r.toNat < 24) (root : Root (write s r v) h) :
    Root s h ∨ (h = v ∧ (r = 2 ∨ r = 7 ∨ r = 16)) := by
  have register := register_bound shape bound
  rcases root with ⟨nonzero, member⟩
  simp only [read_write _ _ _ _ register, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with one | two | three | current | result | external
  · exact Or.inl ⟨nonzero, by simp [one]⟩
  · exact Or.inl ⟨nonzero, by simp [two]⟩
  · exact Or.inl ⟨nonzero, by simp [three]⟩
  · by_cases same : (2 : UInt64) = r
    · exact Or.inr ⟨by simpa only [same, ite_true] using current, Or.inl same.symm⟩
    · exact Or.inl ⟨nonzero, by simp only [same, ite_false] at current; simp [current]⟩
  · by_cases same : (7 : UInt64) = r
    · exact Or.inr ⟨by simpa only [same, ite_true] using result, Or.inr (Or.inl same.symm)⟩
    · exact Or.inl ⟨nonzero, by simp only [same, ite_false] at result; simp [result]⟩
  · by_cases same : (16 : UInt64) = r
    · exact Or.inr ⟨by simpa only [same, ite_true] using external, Or.inr (Or.inr same.symm)⟩
    · exact Or.inl ⟨nonzero, by simp only [same, ite_false] at external; simp [external]⟩

theorem write_register_valid {s : Array UInt64} {cap : Nat} {r v : UInt64}
    (valid : Heap.Valid s cap) (bound : r.toNat < 24) (notCapacity : r ≠ 14)
    (notHead : r ≠ 8) (notCount : r ≠ 9)
    (reference : (r = 2 ∨ r = 7 ∨ r = 16) → Value s cap v) : Heap.Valid (write s r v) cap := by
  have shape := valid.1.1
  have payload := fun {h : UInt64} (handle : Handle cap h) =>
    fun (k : UInt64) (offset : k.toNat < 8) => field_write_register shape handle offset bound (v := v)
  refine ⟨⟨write_shape shape notCapacity, ?_, ?_, ?_⟩, ?_⟩
  · intro h root
    have original : Handle cap h ∧ field s h 0 ≠ 0 := by
      rcases register_root shape bound root with old | ⟨same, changed⟩
      · exact valid.1.2.1 h old
      · rcases reference changed with zero | value
        · exact False.elim (root.1 (same.trans zero))
        · rw [← same] at value; exact value
    rw [payload original.1 0 (by decide)]
    exact original
  · intro parent child handle allocated edge
    rw [payload handle 0 (by decide)] at allocated
    have original := valid.1.2.2.1 parent child handle allocated
      ((Project.Smalltalk.CollectorPreservation.edge_same (fun k offset _ => payload handle k offset)).mp edge)
    rw [payload original.1 0 (by decide)]
    exact original
  · intro h handle allocated
    rw [payload handle 0 (by decide)] at allocated ⊢
    exact valid.1.2.2.2 h handle allocated
  · rcases valid.2 with ⟨nodes, free⟩
    refine ⟨nodes, valid_transfer free ?_ ?_ (fun h handle => ⟨payload handle 0 (by decide), payload handle 2 (by decide)⟩)⟩
    · exact read_write_other _ _ _ _ notHead
    · exact read_write_other _ _ _ _ notCount

theorem value_after_register {s : Array UInt64} {cap : Nat} {r v value : UInt64}
    (shape : Shape s cap) (bound : r.toNat < 24) (original : Value s cap value) :
    Value (write s r v) cap value := by
  rcases original with zero | allocated
  · exact Or.inl zero
  · exact Or.inr ⟨allocated.1, by
      rw [field_write_register shape allocated.1 (show (0 : UInt64).toNat < 8 by decide) bound]
      exact allocated.2⟩

end Project.Smalltalk.HeapWrite
