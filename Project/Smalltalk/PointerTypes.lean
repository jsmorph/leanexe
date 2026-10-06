import Project.Smalltalk.Reachability

namespace Project.Smalltalk.PointerTypes
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Graph
open Project.Smalltalk.HeapWrite Project.Smalltalk.Reachability

def Required (parent offset child : UInt64) : Prop :=
  (parent = 4 ∧ offset = 3 ∧ child = 7) ∨
  (parent = 5 ∧ (offset = 4 ∨ offset = 5) ∧ child = 5) ∨
  (parent = 5 ∧ (offset = 6 ∨ offset = 7) ∧ child = 7) ∨
  (parent = 6 ∧ offset = 3 ∧ child = 5) ∨
  (parent = 7 ∧ offset = 3 ∧ child = 7)

def Matches (s : Array UInt64) (cap : Nat) (tag value : UInt64) : Prop :=
  value = 0 ∨ (Handle cap value ∧ field s value 0 = tag)

def Valid (s : Array UInt64) (cap : Nat) : Prop :=
  ∀ h, Handle cap h → field s h 0 ≠ 0 → ∀ k : UInt64, k.toNat < 8 →
    ∀ tag, Required (field s h 0) k tag → Matches s cap tag (field s h k)

theorem required_pointer {parent offset child : UInt64} (required : Required parent offset child) :
    PointerField parent offset := by
  rcases required with ⟨rfl, rfl, rfl⟩ | ⟨rfl, offset, rfl⟩ | ⟨rfl, offset, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simp [PointerField]
  · rcases offset with rfl | rfl <;> simp [PointerField]
  · rcases offset with rfl | rfl <;> simp [PointerField]
  · simp [PointerField]
  · simp [PointerField]

theorem required_child_nonzero {parent offset child : UInt64} (required : Required parent offset child) :
    child ≠ 0 := by
  rcases required with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> decide

theorem matches_value {s : Array UInt64} {cap : Nat} {tag value : UInt64}
    (matching : Matches s cap tag value) (nonzero : tag ≠ 0) : Value s cap value := by
  rcases matching with zero | cell
  · exact Or.inl zero
  · exact Or.inr ⟨cell.1, by rw [cell.2]; exact nonzero⟩

theorem matches_after_cell {s : Array UInt64} {cap : Nat} {h k v tag value : UInt64}
    (shape : Shape s cap) (handle : Handle cap h) (bound : k.toNat < 8) (notTag : k ≠ 0)
    (matching : Matches s cap tag value) : Matches (write s (address h + k) v) cap tag value := by
  rcases matching with zero | cell
  · exact Or.inl zero
  · exact Or.inr ⟨cell.1, by rw [cell_tag shape handle bound notTag cell.1]; exact cell.2⟩

theorem write_cell_valid {s : Array UInt64} {cap : Nat} {h k v : UInt64}
    (shape : Shape s cap) (typed : Valid s cap) (handle : Handle cap h)
    (bound : k.toNat < 8) (notTag : k ≠ 0)
    (newValue : ∀ tag, Required (field s h 0) k tag → Matches s cap tag v) :
    Valid (write s (address h + k) v) cap := by
  intro parent parentHandle allocated j offset tag required
  rw [cell_tag shape handle bound notTag parentHandle] at allocated required
  rw [field_write_cell shape handle parentHandle bound offset]
  by_cases changed : parent = h ∧ j = k
  · rcases changed with ⟨rfl, rfl⟩
    simp only [true_and, ite_true]
    exact matches_after_cell shape handle bound notTag (newValue tag required)
  · simp only [changed, ite_false]
    exact matches_after_cell shape handle bound notTag (typed parent parentHandle allocated j offset tag required)

theorem write_register_valid {s : Array UInt64} {cap : Nat} {r v : UInt64}
    (shape : Shape s cap) (typed : Valid s cap) (bound : r.toNat < 24) : Valid (write s r v) cap := by
  intro parent handle allocated k offset tag required
  have same := fun {h : UInt64} (hh : Handle cap h) =>
    fun (j : UInt64) (hj : j.toNat < 8) => field_write_register shape hh hj bound (v := v)
  rw [same handle 0 (by decide)] at allocated required
  rw [same handle k offset]
  rcases typed parent handle allocated k offset tag required with zero | child
  · exact Or.inl zero
  · exact Or.inr ⟨child.1, by rw [same child.1 0 (by decide)]; exact child.2⟩

end Project.Smalltalk.PointerTypes
