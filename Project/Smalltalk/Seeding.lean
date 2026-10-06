import Project.Smalltalk.SeedMemory

namespace Project.Smalltalk.Seeding
open LeanExe.Smalltalk.Arena Project.Smalltalk.Memory Project.Smalltalk.Loops
open Project.Smalltalk.SeedMemory Project.Smalltalk.InitializationBase

structure Progress (original t : Array UInt64) (cap : Nat) (i : UInt64) : Prop where
  index : i.toNat ≤ cap
  shape : Shape t cap
  registers : ∀ r : UInt64, r.toNat < 24 → read t r = read original r
  cells : ∀ h : UInt64, Handle cap h → ∀ k : UInt64, k.toNat < 8 →
    field t h k = if h.toNat ≤ i.toNat then seededWord (read original 14) h k else 0

theorem progress_step {original t : Array UInt64} {cap : Nat} {i : UInt64}
    (progress : Progress original t cap i) (index : i.toNat < cap) :
    Progress original (seedCell t i) cap (i + 1) := by
  have inc := successor_toNat (i := i) (by have := progress.shape.2.1; omega)
  refine ⟨(successor_handle progress.shape.2.1 index).2, seedCell_shape progress.shape index, ?_, ?_⟩
  · intro r bound
    exact (seedCell_register progress.shape index bound).trans (progress.registers r bound)
  · intro h handle k bound
    rw [seedCell_field progress.shape index handle bound]
    by_cases same : h = i + 1
    · subst h
      have unvisited : ¬(i + 1).toNat ≤ i.toNat := by rw [inc]; omega
      have zero : field t (i + 1) k = 0 := by
        rw [progress.cells _ handle k bound]
        simp only [unvisited, ite_false]
      rw [zero, progress.registers 14 (by decide)]
      simp only [ite_true, Nat.le_refl, seededWord]
    · simp only [same, ite_false]
      rw [progress.cells h handle k bound]
      have different : h.toNat ≠ (i + 1).toNat := by intro eq; exact same (UInt64.toNat_inj.mp eq)
      have equivalent : h.toNat ≤ i.toNat ↔ h.toNat ≤ (i + 1).toNat := by
        rw [inc]
        rw [inc] at different
        omega
      simp only [equivalent]

def seeding (s : Array UInt64) : Array UInt64 :=
  (LeanExe.repeatWhile (read s 14) ((0 : UInt64), s)
    (fun st => st.1 < read s 14) (fun st => seedNext st.2 st.1)).2

theorem seeding_complete {s : Array UInt64} {cap : Nat} (shape : Shape s cap)
    (zeros : ∀ h : UInt64, Handle cap h → ∀ k : UInt64, k.toNat < 8 → field s h k = 0) :
    Shape (seeding s) cap ∧
    (∀ r : UInt64, r.toNat < 24 → read (seeding s) r = read s r) ∧
    ∀ h : UInt64, Handle cap h → ∀ k : UInt64, k.toNat < 8 →
      field (seeding s) h k = seededWord (read s 14) h k := by
  let P := fun st : UInt64 × Array UInt64 => Progress s st.2 cap st.1
  have initial : P (0, s) := by
    refine ⟨Nat.zero_le _, shape, fun _ _ => rfl, ?_⟩
    intro h handle k bound
    have unvisited : ¬h.toNat ≤ (0 : UInt64).toNat := by have := handle.1; simp only [UInt64.reduceToNat]; omega
    simp only [unvisited, ite_false]
    exact zeros h handle k bound
  have step : ∀ st, P st → decide (st.1 < read s 14) = true → P (seedNext st.2 st.1) := by
    rintro ⟨i, t⟩ progress test
    have index : i.toNat < cap := by
      have index := of_decide_eq_true test
      simpa only [UInt64.lt_iff_toNat_lt, shape.2.2.2] using index
    exact progress_step progress index
  have invariant := repeat_invariant P _ _ step (read s 14) (0, s) initial
  have endIndex := counted_index (fun t i => seedCell t i) (read s 14)
    (by rw [shape.2.2.2]; exact shape.2.1) (read s 14).toNat 0 s (by simp)
  have index : (LeanExe.repeatWhile (read s 14) ((0 : UInt64), s)
      (fun st => st.1 < read s 14) (fun st => seedNext st.2 st.1)).1.toNat = cap := by
    simpa only [LeanExe.repeatWhile, seedNext, UInt64.reduceToNat, Nat.zero_add, shape.2.2.2] using endIndex
  refine ⟨invariant.shape, invariant.registers, ?_⟩
  intro h handle k bound
  have words := invariant.cells h handle k bound
  have visited : h.toNat ≤ (LeanExe.repeatWhile (read s 14) ((0 : UInt64), s)
      (fun st => st.1 < read s 14) (fun st => seedNext st.2 st.1)).1.toNat := by
    rw [index]; exact handle.2
  simpa only [seeding, visited, ite_true] using words

theorem init_eq_seeding (requested stress : UInt64) :
    init requested stress = seeding (headers (capacity requested) stress) := by
  have bounds := capacity_bounds requested
  have cap : read (headers (capacity requested) stress) 14 = capacity requested := by
    rw [headers_read bounds.2]
    simp
  unfold seeding
  rw [cap]
  change (LeanExe.repeatWhile (capacity requested) ((0 : UInt64), headers (capacity requested) stress)
    (fun (i, _) => i < capacity requested) (fun (i, t) => seedNext t i)).2 = _
  have condition : (fun st : UInt64 × Array UInt64 => match st with | (i, _) => decide (i < capacity requested)) =
      (fun st => decide (st.1 < capacity requested)) := by funext st; cases st; rfl
  have action : (fun st : UInt64 × Array UInt64 => match st with | (i, t) => seedNext t i) =
      (fun st => seedNext st.2 st.1) := by funext st; cases st; rfl
  rw [condition, action]

theorem init_cells (requested stress : UInt64) :
    Shape (init requested stress) (capacity requested).toNat ∧
    (∀ r : UInt64, r.toNat < 24 → read (init requested stress) r = read (headers (capacity requested) stress) r) ∧
    ∀ h : UInt64, Handle (capacity requested).toNat h → ∀ k : UInt64, k.toNat < 8 →
      field (init requested stress) h k = seededWord (capacity requested) h k := by
  have bounds := capacity_bounds requested
  have facts := seeding_complete (headers_shape bounds.1 bounds.2 stress)
    (fun _ handle _ bound => headers_field bounds.2 stress handle bound)
  rw [init_eq_seeding]
  have cap : read (headers (capacity requested) stress) 14 = capacity requested := by
    rw [headers_read bounds.2]
    simp
  rw [cap] at facts
  exact facts

end Project.Smalltalk.Seeding
