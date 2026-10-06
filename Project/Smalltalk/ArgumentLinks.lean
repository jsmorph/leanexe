import Project.Smalltalk.PointerTypes

namespace Project.Smalltalk.ArgumentLinks
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.Traversal Project.Smalltalk.PointerTypes

theorem follow_zero (s : Array UInt64) (n : Nat) : follow s 7 3 n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [follow, ih, hop, kind]

theorem follow_add (s : Array UInt64) (head : UInt64) (a b : Nat) :
    follow s 7 3 (a + b) head = follow s 7 3 b (follow s 7 3 a head) := by
  induction b with
  | zero => simp only [Nat.add_zero, follow]
  | succ b ih =>
    change hop s 7 3 (follow s 7 3 (a + b) head) = hop s 7 3 (follow s 7 3 b (follow s 7 3 a head))
    exact congrArg (hop s 7 3) ih

theorem hop_typed {s : Array UInt64} {cap : Nat} {head : UInt64}
    (shape : Shape s cap) (typed : PointerTypes.Valid s cap)
    (matching : Matches s cap 7 head) : Matches s cap 7 (hop s 7 3 head) := by
  rcases matching with rfl | cell
  · simp [hop, kind]; exact Or.inl rfl
  · have tag : kind s head = 7 := (kind_eq_field shape cell.1).trans cell.2
    simp only [hop, tag, ite_true]
    exact typed head cell.1 (by rw [cell.2]; decide) 3 (by decide) 7 (by simp [Required, cell.2])

theorem follow_typed {s : Array UInt64} {cap : Nat} {head : UInt64}
    (shape : Shape s cap) (typed : PointerTypes.Valid s cap)
    (matching : Matches s cap 7 head) (n : Nat) : Matches s cap 7 (follow s 7 3 n head) := by
  induction n with
  | zero => exact matching
  | succ n ih => exact hop_typed shape typed ih

theorem walk_unclamped {s : Array UInt64} {cap : Nat} {head count : UInt64}
    (shape : Shape s cap) (within : count.toNat ≤ cap) :
    walk s head count = follow s 7 3 count.toNat head := by
  have bound : count ≤ read s 14 := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [shape.2.2.2]; exact within
  rw [walk_eq_follow]
  have minimum : min count (read s 14) = count := by simp [min, bound]
  rw [minimum]

theorem earlier_nonzero {s : Array UInt64} {head : UInt64} {last earlier : Nat}
    (within : earlier ≤ last) (accepted : follow s 7 3 last head ≠ 0) :
    follow s 7 3 earlier head ≠ 0 := by
  intro zero
  have split : last = earlier + (last - earlier) := by omega
  rw [split, follow_add, zero, follow_zero] at accepted
  exact accepted rfl

/-- The receiver-link guard also validates all preceding operand links. -/
theorem send_argument {s : Array UInt64} {cap : Nat} {args nargs index : UInt64}
    (valid : Graph.Valid s cap) (typed : PointerTypes.Valid s cap)
    (arguments : Matches s cap 7 args) (bounded : nargs.toNat < cap)
    (accepted : kind s (walk s args nargs) = 7) (earlier : index.toNat ≤ nargs.toNat) :
    Handle cap (walk s args index) ∧ field s (walk s args index) 0 = 7 ∧
      HeapWrite.Value s cap (field s (walk s args index) 2) := by
  have finalNonzero : walk s args nargs ≠ 0 := by
    intro zero
    rw [zero] at accepted
    simp [kind] at accepted
  have last : follow s 7 3 nargs.toNat args ≠ 0 := by
    rw [← walk_unclamped valid.1 (by omega)]; exact finalNonzero
  have earlierNonzero : walk s args index ≠ 0 := by
    rw [walk_unclamped valid.1 (by omega)]
    exact earlier_nonzero earlier last
  have matching : Matches s cap 7 (walk s args index) := by
    rw [walk_unclamped valid.1 (by omega)]
    exact follow_typed valid.1 typed arguments _
  rcases matching with zero | cell
  · exact False.elim (earlierNonzero zero)
  · exact ⟨cell.1, cell.2, Reachability.pointer_value valid cell.1
      (by rw [cell.2]; decide) (by decide) (by simp [PointerField, cell.2])⟩

end Project.Smalltalk.ArgumentLinks
