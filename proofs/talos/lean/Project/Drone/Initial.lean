import Project.Drone.Costs

namespace Project.Drone.Initial
open LeanExe.Examples.Drone Costs

theorem initial_eq : initial = (List.range 45).foldl (fun row state =>
    let c : UInt64 := if state == 0 then 0 else infinity
    ((row.push c).push c).push 0) (#[] : Array UInt64) := by
  simp only [initial, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', stateCount]
  rfl

set_option maxRecDepth 10000 in
/-- Closed finite checks are reduced by the Lean kernel. -/
theorem initial_fields (state : Nat) (hs : state < stateCount) :
    initial[3*state]! = (if state=0 then 0 else infinity) ∧
    initial[3*state+1]! = (if state=0 then 0 else infinity) ∧
    initial[3*state+2]! = 0 := by
  rw [initial_eq]
  have h : ∀ s : Fin 45,
      initial[3*s.val]! = (if s.val=0 then 0 else infinity) ∧
      initial[3*s.val+1]! = (if s.val=0 then 0 else infinity) ∧
      initial[3*s.val+2]! = 0 := by rw [initial_eq]; decide
  rw [← initial_eq]
  exact h ⟨state, hs⟩

set_option maxRecDepth 10000 in
theorem initial_size : initial.size = 135 := by rw [initial_eq]; decide

theorem initial_finite (state : Nat) (hs : state < stateCount) :
    initial[3*state]! < infinity ↔ state=0 := by
  rw [(initial_fields state hs).1]
  split
  · simp_all [infinity, UInt64.lt_iff_toNat_lt]
  · simp_all

theorem initial_bound : rowBound 0 initial := by
  intro state hs hfinite
  have h := (initial_finite state hs).mp hfinite
  subst state
  have hfields := initial_fields 0 (by decide)
  simp only [ite_true] at hfields
  rw [hfields.1, hfields.2.1]
  decide

#print axioms initial_fields
#print axioms initial_bound
end Project.Drone.Initial
