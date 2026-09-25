import Project.Drone.Rows
import Project.Drone.Timing

namespace Project.Drone.Costs
open LeanExe.Examples.Drone Arithmetic Selection Rows Timing

def rowBound (layer : Nat) (row : Array UInt64) : Prop :=
  ∀ state, state < stateCount → row[3*state]! < infinity →
    row[3*state]!.toNat ≤ layer*63019320 ∧ row[3*state+1]!.toNat ≤ layer*200

theorem excess_nat (r : UInt64) (target : Nat) (hr : r.toNat ≤ 1000100)
    (ht : target < stateCount) :
    (altitude r target-r).toNat = (target/5)*25 := by
  have hb := altitude_bounds r target hr ht
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hb.1), altitude_nat r target hr ht]
  omega

/-- Natural-number interpretation of an actual admitted predecessor, with
all additions proved free of UInt64 wrap. -/
theorem predecessor_exact (layer : Nat) (previous : Array UInt64)
    (hbound : rowBound layer previous) (hlayer : layer ≤ 63)
    (r0 r1 : UInt64) (hr0 : r0.toNat ≤ 1000100) (hr1 : r1.toNat ≤ 1000100)
    (source target : Nat) (hs : source < stateCount) (ht : target < stateCount)
    (hold : previous[3*source]! < infinity)
    (hedge : 0 < edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source) (speed target)) :
    let c := predecessor r0 r1 previous target source
    let dt := edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source) (speed target)
    c.time.toNat = previous[3*source]!.toNat+dt.toNat ∧
    c.excess.toNat = previous[3*source+1]!.toNat+(target/5)*25 ∧
    c.parent.toNat = source ∧
    c.time.toNat ≤ (layer+1)*63019320 ∧
    c.excess.toNat ≤ (layer+1)*200 ∧ c.time < infinity := by
  obtain ⟨htime, hexcess⟩ := hbound source hs hold
  have hdt := edge_cost_bound r0 r1 (altitude r0 source) (altitude r1 target) (speed source) (speed target)
    (altitude_bounds r0 source hr0 hs).2 (altitude_bounds r1 target hr1 ht).2
  have htime' : previous[3*source]!.toNat ≤ 3970217160 := by omega
  have hexcess' : previous[3*source+1]!.toNat ≤ 12600 := by omega
  have hs' : source < 45 := hs
  have ht' : target < 45 := ht
  have hexc := excess_nat r1 target hr1 ht
  have htadd : (previous[3*source]!+edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source) (speed target)).toNat =
      previous[3*source]!.toNat+(edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source) (speed target)).toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have headd : (previous[3*source+1]!+(altitude r1 target-r1)).toNat = previous[3*source+1]!.toNat+(target/5)*25 := by
    rw [UInt64.toNat_add, hexc]; exact Nat.mod_eq_of_lt (by omega)
  have hp : source.toUInt64.toNat = source := UInt64.toNat_ofNat_of_lt' (by change source < 18446744073709551616; omega)
  simp only [predecessor, hold, hedge, and_self, if_true]
  rw [htadd, headd, hp]
  refine ⟨rfl, rfl, rfl, by omega, by omega, ?_⟩
  rw [UInt64.lt_iff_toNat_lt, htadd]
  change _ < 1000000000000
  omega

/-- A finite scan has a valid stored parent and exact (non-wrapping) costs. -/
theorem best_parent (layer : Nat) (previous : Array UInt64)
    (hbound : rowBound layer previous) (hlayer : layer ≤ 63)
    (r0 r1 : UInt64) (hr0 : r0.toNat ≤ 1000100) (hr1 : r1.toNat ≤ 1000100)
    (target : Nat) (ht : target < stateCount)
    (hfinite : (bestPredecessor stateCount r0 r1 previous target).time < infinity) :
    ∃ source, source < stateCount ∧
      previous[3*source]! < infinity ∧
      0 < edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source) (speed target) ∧
      (bestPredecessor stateCount r0 r1 previous target).parent.toNat = source ∧
      (bestPredecessor stateCount r0 r1 previous target).time.toNat =
        previous[3*source]!.toNat+(edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source) (speed target)).toNat ∧
      (bestPredecessor stateCount r0 r1 previous target).excess.toNat =
        previous[3*source+1]!.toNat+(target/5)*25 ∧
      (bestPredecessor stateCount r0 r1 previous target).time.toNat ≤ (layer+1)*63019320 ∧
      (bestPredecessor stateCount r0 r1 previous target).excess.toNat ≤ (layer+1)*200 := by
  obtain ⟨source, hs, hold, hedge, heq⟩ := finite_scan_predecessor stateCount r0 r1 previous target hfinite
  have h := predecessor_exact layer previous hbound hlayer r0 r1 hr0 hr1 source target hs ht hold hedge
  rw [heq]
  exact ⟨source, hs, hold, hedge, h.2.2.1, h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- The actual row transition preserves bounded costs. -/
theorem advance_bound (layer : Nat) (previous : Array UInt64)
    (hbound : rowBound layer previous) (hlayer : layer ≤ 63)
    (r0 r1 : UInt64) (hr0 : r0.toNat ≤ 1000100) (hr1 : r1.toNat ≤ 1000100)
    (last : Bool) : rowBound (layer+1) (advance r0 r1 last previous) := by
  intro target ht hfinite
  have htime := advance_word r0 r1 last previous target 0 ht (by decide)
  have hexcess := advance_word r0 r1 last previous target 1 ht (by decide)
  simp only [word, Nat.add_zero, if_true] at htime
  simp only [word, Nat.one_ne_zero, ite_false, ite_true] at hexcess
  rw [htime] at hfinite ⊢
  rw [hexcess]
  unfold entry at hfinite ⊢
  split at hfinite
  · rename_i ha
    rw [if_pos ha]
    obtain ⟨_, _, _, _, _, _, _, htime, hexcess⟩ :=
      best_parent layer previous hbound hlayer r0 r1 hr0 hr1 target ht hfinite
    exact ⟨htime, hexcess⟩
  · simp [unreachable] at hfinite

#print axioms predecessor_exact
#print axioms best_parent
#print axioms advance_bound
end Project.Drone.Costs
