import Project.Drone.Selection
import Project.Drone.Timing

/-! The costs in a row stay exact and bounded: an admitted predecessor adds its edge's ticks and
the target's altitude above the floor without wrapping, and the first row and every advance of
a bounded row are bounded. -/

namespace Project.Drone

open LeanExe.Examples.Drone Arithmetic Selection Timing Optimality

/-- Element `state` of the first row. -/
def initialChoice (state : UInt64) : Choice :=
  ⟨if state == 0 then 0 else infinity, if state == 0 then 0 else infinity, 0⟩

theorem initial_build : initial = LeanExe.build 45 initialChoice := rfl

namespace Costs

/-- The finite choices of a row at station `layer` cost at most `layer` maximal edges. -/
def rowBound (layer : Nat) (row : Array Choice) : Prop :=
  ∀ state : UInt64, state.toNat < 45 → row[state.toNat]!.time < infinity →
    row[state.toNat]!.time.toNat ≤ layer * 63019320 ∧ row[state.toNat]!.excess.toNat ≤ layer * 200

theorem excess_nat (r target : UInt64) (hr : r.toNat ≤ 1000100) (ht : target.toNat < 45) :
    (altitude r target - r).toNat = target.toNat / 5 * 25 := by
  have hb := altitude_bounds r target hr ht
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hb.1), altitude_nat r target hr ht]
  omega

/-- An admitted predecessor of a bounded row, as natural numbers, with no wrap. -/
theorem predecessor_exact (layer : Nat) (row : Array Choice) (hbound : rowBound layer row)
    (hlayer : layer ≤ 63) (r0 r1 : UInt64) (hr0 : r0.toNat ≤ 1000100) (hr1 : r1.toNat ≤ 1000100)
    (source target : UInt64) (hs : source.toNat < 45) (ht : target.toNat < 45)
    (hold : row[source.toNat]!.time < infinity)
    (hedge : 0 < edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source)
      (speed target)) :
    let c := predecessor r0 r1 row[source.toNat]! target source
    let dt := edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source)
      (speed target)
    c.time.toNat = row[source.toNat]!.time.toNat + dt.toNat ∧
    c.excess.toNat = row[source.toNat]!.excess.toNat + target.toNat / 5 * 25 ∧
    c.parent = source ∧
    c.time.toNat ≤ (layer + 1) * 63019320 ∧
    c.excess.toNat ≤ (layer + 1) * 200 ∧ c.time < infinity := by
  obtain ⟨htime, hexcess⟩ := hbound source hs hold
  have hdt := edge_cost_bound r0 r1 (altitude r0 source) (altitude r1 target) (speed source)
    (speed target) (altitude_bounds r0 source hr0 hs).2 (altitude_bounds r1 target hr1 ht).2
  have hexc := excess_nat r1 target hr1 ht
  have htadd : (row[source.toNat]!.time + edgeTicks r0 r1 (altitude r0 source)
      (altitude r1 target) (speed source) (speed target)).toNat =
      row[source.toNat]!.time.toNat + (edgeTicks r0 r1 (altitude r0 source) (altitude r1 target)
        (speed source) (speed target)).toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have headd : (row[source.toNat]!.excess + (altitude r1 target - r1)).toNat =
      row[source.toNat]!.excess.toNat + target.toNat / 5 * 25 := by
    rw [UInt64.toNat_add, hexc]; exact Nat.mod_eq_of_lt (by omega)
  simp only [predecessor, hold, hedge, decide_true, Bool.and_self, ite_true]
  refine ⟨htadd, headd, trivial, by omega, by omega, ?_⟩
  rw [UInt64.lt_iff_toNat_lt, htadd]
  change _ < 1000000000000
  omega

/-- A finite `best` over a bounded row has an admitted parent and exact, bounded costs. -/
theorem best_parent (layer : Nat) (row : Array Choice) (hbound : rowBound layer row)
    (hlayer : layer ≤ 63) (r0 r1 : UInt64) (hr0 : r0.toNat ≤ 1000100) (hr1 : r1.toNat ≤ 1000100)
    (target sources : UInt64) (ht : target.toNat < 45) (hsources : sources.toNat ≤ 45)
    (hfinite : (best r0 r1 row 0 target sources).time < infinity) :
    ∃ source : UInt64, source.toNat < sources.toNat ∧ row[source.toNat]!.time < infinity ∧
      0 < edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source)
        (speed target) ∧
      (best r0 r1 row 0 target sources).parent = source ∧
      (best r0 r1 row 0 target sources).time.toNat = row[source.toNat]!.time.toNat +
        (edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source)
          (speed target)).toNat ∧
      (best r0 r1 row 0 target sources).excess.toNat =
        row[source.toNat]!.excess.toNat + target.toNat / 5 * 25 ∧
      (best r0 r1 row 0 target sources).time.toNat ≤ (layer + 1) * 63019320 ∧
      (best r0 r1 row 0 target sources).excess.toNat ≤ (layer + 1) * 200 := by
  obtain ⟨source, hs, hold, hedge, heq⟩ := finite_best r0 r1 row 0 target sources hfinite
  simp only [UInt64.zero_add] at hold heq
  have h := predecessor_exact layer row hbound hlayer r0 r1 hr0 hr1 source target (by omega) ht
    hold hedge
  rw [heq]
  exact ⟨source, hs, hold, hedge, h.2.2.1, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem sourceCount_le (last : Bool) (target : UInt64) : (sourceCount last target).toNat ≤ 45 := by
  unfold sourceCount
  split <;> decide

/-- An advance of a bounded row is bounded. -/
theorem advance_bound (layer : Nat) (row : Array Choice) (hbound : rowBound layer row)
    (hlayer : layer ≤ 63) (r0 r1 : UInt64) (hr0 : r0.toNat ≤ 1000100) (hr1 : r1.toNat ≤ 1000100)
    (last : Bool) : rowBound (layer + 1) (advance r0 r1 last row 0) := by
  intro target ht hfinite
  rw [advance_get _ _ _ _ _ _ ht] at hfinite ⊢
  obtain ⟨_, _, _, _, _, _, _, htime, hexcess⟩ := best_parent layer row hbound hlayer r0 r1 hr0
    hr1 target (sourceCount last target) ht (sourceCount_le last target) hfinite
  exact ⟨htime, hexcess⟩

theorem initial_get (state : UInt64) (hs : state.toNat < 45) :
    initial[state.toNat]! = initialChoice state := by
  rw [initial_build, build_get _ _ _ hs, UInt64.ofNat_toNat]

theorem initial_finite (state : UInt64) (hs : state.toNat < 45) :
    initial[state.toNat]!.time < infinity ↔ state = 0 := by
  rw [initial_get state hs]
  unfold initialChoice
  by_cases h : state = 0 <;> simp [h] <;> decide

theorem initial_zero : initial[(0 : UInt64).toNat]! = ⟨0, 0, 0⟩ := by
  rw [initial_get 0 (by decide)]
  rfl

theorem initial_bound : rowBound 0 initial := by
  intro state hs hfinite
  have h := (initial_finite state hs).mp hfinite
  subst h
  rw [initial_zero]
  decide

end Costs

end Project.Drone
