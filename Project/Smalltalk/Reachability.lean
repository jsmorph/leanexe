import Project.Smalltalk.Traversal
import Project.Smalltalk.HeapWrite

namespace Project.Smalltalk.Reachability
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.Traversal Project.Smalltalk.HeapWrite

def Live (s : Array UInt64) (h : UInt64) : Prop := h = 0 ∨ Reachable s h

theorem live_value {s : Array UInt64} {cap : Nat} {h : UInt64}
    (valid : Graph.Valid s cap) (live : Live s h) : Value s cap h := by
  rcases live with zero | reached
  · exact Or.inl zero
  · exact Or.inr (reachable_allocated valid reached)

theorem root_live (s : Array UInt64) (r : UInt64) (root : r = 2 ∨ r = 7 ∨ r = 16) : Live s (read s r) := by
  by_cases zero : read s r = 0
  · exact Or.inl zero
  · refine Or.inr (.root ⟨zero, ?_⟩)
    rcases root with rfl | rfl | rfl <;> simp

theorem kind_handle {s : Array UInt64} {cap : Nat} {h tag : UInt64}
    (shape : Shape s cap) (nonzero : tag ≠ 0) (cell : kind s h = tag) : Handle cap h := by
  have hNonzero : h ≠ 0 := by
    intro zero
    subst h
    simp only [kind, BEq.rfl, Bool.true_or, ite_true] at cell
    exact nonzero cell.symm
  have upper : ¬ read s 14 < h := by
    intro outside
    simp only [kind, outside, decide_true, Bool.or_true, ite_true] at cell
    exact nonzero cell.symm
  have lower : 1 ≤ h.toNat := by
    have nz : h.toNat ≠ 0 := by
      intro zero
      exact hNonzero (UInt64.toNat_inj.mp zero)
    omega
  refine ⟨lower, ?_⟩
  rw [UInt64.lt_iff_toNat_lt, shape.2.2.2] at upper
  omega

theorem pointer_value {s : Array UInt64} {cap : Nat} {h k : UInt64}
    (valid : Graph.Valid s cap) (handle : Handle cap h) (allocated : field s h 0 ≠ 0)
    (bound : k.toNat < 8) (pointer : PointerField (field s h 0) k) : Value s cap (field s h k) := by
  by_cases zero : field s h k = 0
  · exact Or.inl zero
  · exact Or.inr (valid.2.2.1 h _ handle allocated ⟨zero, k, bound, pointer, rfl⟩)

theorem pointer_live {s : Array UInt64} {h k : UInt64}
    (reached : Reachable s h) (bound : k.toNat < 8) (pointer : PointerField (field s h 0) k) :
    Live s (field s h k) := by
  by_cases zero : field s h k = 0
  · exact Or.inl zero
  · exact Or.inr (.next reached ⟨zero, k, bound, pointer, rfl⟩)

theorem live_reached {s : Array UInt64} {h tag : UInt64}
    (live : Live s h) (nonzero : tag ≠ 0) (cell : kind s h = tag) : Reachable s h := by
  rcases live with zero | reached
  · subst h
    simp only [kind, BEq.rfl, Bool.true_or, ite_true] at cell
    exact False.elim (nonzero cell.symm)
  · exact reached

theorem hop_live {s : Array UInt64} {cap : Nat} {head tag next : UInt64}
    (valid : Graph.Valid s cap) (live : Live s head) (nonzero : tag ≠ 0)
    (bound : next.toNat < 8) (pointer : PointerField tag next) : Live s (hop s tag next head) := by
  unfold hop
  split
  · rename_i cell
    have reached := live_reached live nonzero cell
    apply pointer_live reached bound
    rw [← kind_eq_field valid.1 (reachable_allocated valid reached).1, cell]
    exact pointer
  · exact Or.inl rfl

theorem follow_live {s : Array UInt64} {cap : Nat} {head tag next : UInt64}
    (valid : Graph.Valid s cap) (live : Live s head) (nonzero : tag ≠ 0)
    (bound : next.toNat < 8) (pointer : PointerField tag next) (count : Nat) :
    Live s (follow s tag next count head) := by
  induction count with
  | zero => exact live
  | succ count ih => exact hop_live valid ih nonzero bound pointer

theorem walk_live {s : Array UInt64} {cap : Nat} {head : UInt64}
    (valid : Graph.Valid s cap) (live : Live s head) (count : UInt64) : Live s (walk s head count) := by
  rw [walk_eq_follow]
  exact follow_live valid live (by decide) (by decide) (by simp [PointerField]) _

theorem lexical_live {s : Array UInt64} {cap : Nat} {head : UInt64}
    (valid : Graph.Valid s cap) (live : Live s head) (count : UInt64) : Live s (lexical s head count) := by
  rw [lexical_eq_follow]
  exact follow_live valid live (by decide) (by decide) (by simp [PointerField]) _

theorem guarded_field_live {s : Array UInt64} {cap : Nat} {h tag k : UInt64}
    (valid : Graph.Valid s cap) (live : Live s h) (nonzero : tag ≠ 0)
    (bound : k.toNat < 8) (pointer : PointerField tag k) :
    Live s (if kind s h == tag then field s h k else 0) := by
  simpa only [hop, beq_iff_eq] using hop_live valid live nonzero bound pointer

theorem localSlot_live {s : Array UInt64} {cap : Nat} {act : UInt64}
    (valid : Graph.Valid s cap) (live : Live s act) (index depth : UInt64) :
    Live s (localSlot s act index depth) := by
  have lexical := lexical_live valid live depth
  have head := guarded_field_live valid lexical (show (5 : UInt64) ≠ 0 by decide)
    (show (6 : UInt64).toNat < 8 by decide) (by simp [PointerField])
  have slot := walk_live valid head index
  let h := walk s (if kind s (LeanExe.Smalltalk.Runtime.lexical s act depth) == 5 then
    field s (LeanExe.Smalltalk.Runtime.lexical s act depth) 6 else 0) index
  change Live s (if index ≥ read s 14 || depth ≥ read s 14 || kind s h != 7 then 0 else h)
  by_cases rejected : (decide (index ≥ read s 14) || decide (depth ≥ read s 14) || kind s h != 7) = true
  · simp only [rejected, ite_true]; exact Or.inl rfl
  · simp only [rejected]; exact slot

theorem localSlot_tag {s : Array UInt64} {act index depth : UInt64}
    (nonzero : localSlot s act index depth ≠ 0) : kind s (localSlot s act index depth) = 7 := by
  let h := walk s (if kind s (lexical s act depth) == 5 then
    field s (lexical s act depth) 6 else 0) index
  change (if index ≥ read s 14 || depth ≥ read s 14 || kind s h != 7 then 0 else h) ≠ 0 at nonzero
  change kind s (if index ≥ read s 14 || depth ≥ read s 14 || kind s h != 7 then 0 else h) = 7
  by_cases rejected : (decide (index ≥ read s 14) || decide (depth ≥ read s 14) || kind s h != 7) = true
  · simp only [rejected, ite_true] at nonzero; exact False.elim (nonzero rfl)
  · simp only [rejected]
    change kind s h = 7
    apply Classical.byContradiction
    intro different
    have test : (kind s h != 7) = true := bne_iff_ne.mpr different
    simp only [test, Bool.or_true] at rejected
    exact rejected True.intro

theorem self_live {s : Array UInt64} {cap : Nat} {act : UInt64}
    (valid : Graph.Valid s cap) (live : Live s act) : Live s (self s act) := by
  let slot := localSlot s act 0 0
  change Live s (if slot == 0 then 0 else field s slot 2)
  by_cases zero : slot = 0
  · simp only [zero, BEq.rfl, ite_true]; exact Or.inl rfl
  · simp only [show (slot == 0) = false from beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ite_false]
    have reached := live_reached (localSlot_live valid live 0 0) (by decide) (localSlot_tag zero)
    apply pointer_live reached (show (2 : UInt64).toNat < 8 by decide)
    rw [← kind_eq_field valid.1 (reachable_allocated valid reached).1, localSlot_tag zero]
    simp [PointerField]

theorem fieldSlot_live {s : Array UInt64} {cap : Nat}
    (valid : Graph.Valid s cap) (index : UInt64) : Live s (fieldSlot s index) := by
  have receiver := self_live valid (root_live s 2 (Or.inl rfl))
  have head := guarded_field_live valid receiver (show (4 : UInt64) ≠ 0 by decide)
    (show (3 : UInt64).toNat < 8 by decide) (by simp [PointerField])
  have slot := walk_live valid head index
  let h := walk s (if kind s (self s (read s 2)) == 4 then field s (self s (read s 2)) 3 else 0) index
  change Live s (if index ≥ read s 14 || kind s h != 7 then 0 else h)
  by_cases rejected : (decide (index ≥ read s 14) || kind s h != 7) = true
  · simp only [rejected, ite_true]; exact Or.inl rfl
  · simp only [rejected]; exact slot

end Project.Smalltalk.Reachability
