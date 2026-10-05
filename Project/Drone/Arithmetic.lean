import Project.Drone.Sqrt

/-! The word arithmetic of the planner's states and rest durations, as natural numbers, within
the bounds of the planner's inputs. -/

namespace Project.Drone.Arithmetic

open LeanExe.Examples.Drone

/-- A bound on every altitude: a floor of at most 1,000,100 plus 8 · 25. -/
def heightLimit : Nat := 1000300

theorem distance_nat (a b : UInt64) :
    (distance a b).toNat = if b.toNat ≤ a.toNat then a.toNat - b.toNat else b.toNat - a.toNat := by
  unfold distance
  by_cases h : b ≤ a
  · rw [if_pos h, UInt64.toNat_sub_of_le a b h, if_pos (UInt64.le_iff_toNat_le.mp h)]
  · rw [if_neg h, if_neg (by simpa only [← UInt64.le_iff_toNat_le] using h)]
    exact UInt64.toNat_sub_of_le b a (by rw [UInt64.le_iff_toNat_le] at *; omega)

theorem distance_le (a b : UInt64) (ha : a.toNat ≤ heightLimit) (hb : b.toNat ≤ heightLimit) :
    (distance a b).toNat ≤ heightLimit := by
  rw [distance_nat]
  split <;> omega

theorem speed_nat (state : UInt64) : (speed state).toNat = state.toNat % 5 * 5 := by
  unfold speed
  rw [UInt64.toNat_mul, UInt64.toNat_mod]
  have : state.toNat % 5 < 5 := Nat.mod_lt _ (by decide)
  exact Nat.mod_eq_of_lt (by simp; omega)

theorem speed_le (state : UInt64) : (speed state).toNat ≤ 20 := by
  rw [speed_nat]
  have := Nat.mod_lt state.toNat (by decide : 0 < 5)
  omega

theorem altitude_nat (r state : UInt64) (hr : r.toNat ≤ 1000100) (hs : state.toNat < 45) :
    (altitude r state).toNat = r.toNat + state.toNat / 5 * 25 := by
  unfold altitude
  have hp : (state / 5 * 25).toNat = state.toNat / 5 * 25 := by
    rw [UInt64.toNat_mul, UInt64.toNat_div]
    exact Nat.mod_eq_of_lt (by simp; omega)
  rw [UInt64.toNat_add, hp]
  exact Nat.mod_eq_of_lt (by simp; omega)

theorem altitude_bounds (r state : UInt64) (hr : r.toNat ≤ 1000100) (hs : state.toNat < 45) :
    r.toNat ≤ (altitude r state).toNat ∧ (altitude r state).toNat ≤ heightLimit := by
  rw [altitude_nat r state hr hs]
  unfold heightLimit
  omega

private theorem triple_nat (d : UInt64) (hd : d.toNat ≤ heightLimit) :
    (3 * d).toNat = 3 * d.toNat := by
  rw [UInt64.toNat_mul]
  unfold heightLimit at hd
  exact Nat.mod_eq_of_lt (by simp; omega)

private theorem rate_ceiling_nat (d : UInt64) (hd : d.toNat ≤ heightLimit) :
    ((3 * d + 39) / 40).toNat = (3 * d.toNat + 39) / 40 := by
  rw [UInt64.toNat_div, UInt64.toNat_add, triple_nat d hd]
  unfold heightLimit at hd
  rw [Nat.mod_eq_of_lt (by simp; omega)]
  rfl

private theorem accel_ceiling_nat (d : UInt64) (hd : d.toNat ≤ heightLimit) :
    ((3 * d + 1) / 2).toNat = (3 * d.toNat + 1) / 2 := by
  rw [UInt64.toNat_div, UInt64.toNat_add, triple_nat d hd]
  unfold heightLimit at hd
  rw [Nat.mod_eq_of_lt (by simp; omega)]
  rfl

private theorem max_nat (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  change (if a ≤ b then b else a).toNat = max a.toNat b.toNat
  by_cases h : a ≤ b
  · rw [if_pos h, max_eq_right (UInt64.le_iff_toNat_le.mp h)]
  · rw [if_neg h, max_eq_left (by rw [UInt64.le_iff_toNat_le] at h; omega)]

/-- The rest duration meets the horizontal and vertical limits, and its upper bound keeps
reachable costs below the infinity sentinel. -/
theorem restSeconds_bounds (d : UInt64) (hd : d.toNat ≤ heightLimit) :
    25 ≤ (restSeconds d).toNat ∧
    3 * d.toNat ≤ 40 * (restSeconds d).toNat ∧
    3 * d.toNat ≤ 2 * (restSeconds d).toNat ^ 2 ∧
    (restSeconds d).toNat ≤ 75023 := by
  have ha := accel_ceiling_nat d hd
  have hr := rate_ceiling_nat d hd
  have hd' : d.toNat ≤ 1000300 := hd
  have hs := Sqrt.ceilSqrt_correct ((3 * d + 1) / 2) (by rw [ha]; omega)
  unfold restSeconds
  simp only
  rw [max_nat, max_nat, hr]
  let q := (ceilSqrt ((3 * d + 1) / 2)).toNat
  have hq : q ≤ 65536 := hs.1
  have hqs : (3 * d.toNat + 1) / 2 ≤ q * q := by rw [← ha]; exact hs.2.1
  let t := max 25 (max ((3 * d.toNat + 39) / 40) q)
  have ht25 : 25 ≤ t := le_max_left _ _
  have htr : (3 * d.toNat + 39) / 40 ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have htq : q ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
  have hsq : q * q ≤ t * t := Nat.mul_self_le_mul_self htq
  have htrb : (3 * d.toNat + 39) / 40 ≤ 75023 := by omega
  have htb : t ≤ 75023 := max_le (by decide) (max_le htrb (by omega))
  change 25 ≤ t ∧ 3 * d.toNat ≤ 40 * t ∧ 3 * d.toNat ≤ 2 * t ^ 2 ∧ t ≤ 75023
  refine ⟨ht25, by omega, ?_, htb⟩
  nlinarith [show 3 * d.toNat ≤ 2 * ((3 * d.toNat + 1) / 2) by omega]

end Project.Drone.Arithmetic
