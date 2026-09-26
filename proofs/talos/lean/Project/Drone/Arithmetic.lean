import Project.Drone.Sqrt
import Lean.Elab.Tactic.Omega

namespace Project.Drone.Arithmetic
open LeanExe.Examples.Drone

-- A finite boundary keeps all operation-by-operation overflow obligations local.
def heightLimit : Nat := 1000300

theorem distance_nat (a b : UInt64) :
    (distance a b).toNat = if b.toNat ≤ a.toNat then a.toNat-b.toNat else b.toNat-a.toNat := by
  unfold distance
  by_cases h : b ≤ a
  · rw [if_pos h, UInt64.toNat_sub_of_le a b h,
      if_pos ((UInt64.le_iff_toNat_le).mp h)]
  · rw [if_neg h, if_neg (by simpa only [← UInt64.le_iff_toNat_le] using h)]
    exact UInt64.toNat_sub_of_le b a (by
      rw [UInt64.le_iff_toNat_le] at *
      omega)

theorem distance_le (a b : UInt64) (ha : a.toNat ≤ heightLimit)
    (hb : b.toNat ≤ heightLimit) : (distance a b).toNat ≤ heightLimit := by
  rw [distance_nat]
  split <;> omega

theorem speed_nat (state : Nat) : (speed state).toNat = (state % 5)*5 := by
  have h : state % 5 < 5 := Nat.mod_lt _ (by decide)
  have hc : ((state % 5).toUInt64).toNat = state % 5 :=
    UInt64.toNat_ofNat_of_lt' (by change state % 5 < 18446744073709551616; omega)
  unfold speed
  rw [UInt64.toNat_mul, hc]
  change ((state % 5)*5) % 18446744073709551616 = (state % 5)*5
  exact Nat.mod_eq_of_lt (by omega)

theorem speed_le (state : Nat) : (speed state).toNat ≤ 20 := by
  rw [speed_nat]
  have := Nat.mod_lt state (by decide : 0 < 5)
  omega

theorem altitude_nat (r : UInt64) (state : Nat) (hr : r.toNat ≤ 1000100)
    (hs : state < stateCount) :
    (altitude r state).toNat = r.toNat+(state/5)*25 := by
  dsimp [stateCount] at hs
  have hc : ((state/5).toUInt64).toNat = state/5 :=
    UInt64.toNat_ofNat_of_lt' (by change state/5 < 18446744073709551616; omega)
  have hp : ((state/5).toUInt64*25).toNat = (state/5)*25 := by
    rw [UInt64.toNat_mul, hc]
    change ((state/5)*25) % 18446744073709551616 = (state/5)*25
    exact Nat.mod_eq_of_lt (by omega)
  unfold altitude
  rw [UInt64.toNat_add, hp]
  exact Nat.mod_eq_of_lt (by omega)

theorem altitude_bounds (r : UInt64) (state : Nat) (hr : r.toNat ≤ 1000100)
    (hs : state < stateCount) :
    r.toNat ≤ (altitude r state).toNat ∧ (altitude r state).toNat ≤ heightLimit := by
  rw [altitude_nat r state hr hs]
  dsimp [stateCount] at hs
  dsimp [heightLimit]
  omega

private theorem triple_nat (d : UInt64) (hd : d.toNat ≤ heightLimit) :
    (3*d).toNat = 3*d.toNat := by
  rw [UInt64.toNat_mul]
  change (3*d.toNat) % 18446744073709551616 = 3*d.toNat
  apply Nat.mod_eq_of_lt
  dsimp [heightLimit] at hd
  omega

private theorem rate_ceiling_nat (d : UInt64) (hd : d.toNat ≤ heightLimit) :
    ((3*d+39)/40).toNat = (3*d.toNat+39)/40 := by
  rw [UInt64.toNat_div, UInt64.toNat_add, triple_nat d hd]
  simp only [UInt64.toNat_ofNat]
  norm_num
  rw [Nat.mod_eq_of_lt (by dsimp [heightLimit] at hd; omega)]

private theorem accel_ceiling_nat (d : UInt64) (hd : d.toNat ≤ heightLimit) :
    ((3*d+1)/2).toNat = (3*d.toNat+1)/2 := by
  rw [UInt64.toNat_div, UInt64.toNat_add, triple_nat d hd]
  simp only [UInt64.toNat_ofNat]
  norm_num
  rw [Nat.mod_eq_of_lt (by dsimp [heightLimit] at hd; omega)]

private theorem max_nat (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  change (if a ≤ b then b else a).toNat = max a.toNat b.toNat
  by_cases h : a ≤ b
  · rw [if_pos h, max_eq_right ((UInt64.le_iff_toNat_le).mp h)]
  · rw [if_neg h, max_eq_left (by rw [UInt64.le_iff_toNat_le] at h; omega)]

/-- The actual UInt64 rest duration meets the horizontal and vertical limits.
The upper bound also separates reachable costs from the infinity sentinel. -/
theorem restSeconds_bounds (d : UInt64) (hd : d.toNat ≤ heightLimit) :
    25 ≤ (restSeconds d).toNat ∧
    3*d.toNat ≤ 40*(restSeconds d).toNat ∧
    3*d.toNat ≤ 2*((restSeconds d).toNat)^2 ∧
    (restSeconds d).toNat ≤ 75023 := by
  have ha := accel_ceiling_nat d hd
  have hr := rate_ceiling_nat d hd
  have hs := Sqrt.ceilSqrt_correct ((3*d+1)/2) (by
    rw [ha]; dsimp [heightLimit] at hd; omega)
  have hd' : d.toNat ≤ 1000300 := hd
  unfold restSeconds
  rw [max_nat, max_nat, hr]
  change 25 ≤ max 25 (max ((3*d.toNat+39)/40) _) ∧ _
  let q := (ceilSqrt ((3*d+1)/2)).toNat
  have hq : q ≤ 65536 := hs.1
  have hqs : (3*d.toNat+1)/2 ≤ q*q := by rw [← ha]; exact hs.2.1
  let t := max 25 (max ((3*d.toNat+39)/40) q)
  have ht25 : 25 ≤ t := le_max_left _ _
  have htr : (3*d.toNat+39)/40 ≤ t := le_trans (le_max_left _ _) (le_max_right _ _)
  have htq : q ≤ t := le_trans (le_max_right _ _) (le_max_right _ _)
  have hsq : q*q ≤ t*t := Nat.mul_self_le_mul_self htq
  have htrb : (3*d.toNat+39)/40 ≤ 75023 := by omega
  have htb : t ≤ 75023 := max_le (by decide) (max_le htrb (by omega))
  change 25 ≤ t ∧ 3*d.toNat ≤ 40*t ∧ 3*d.toNat ≤ 2*t^2 ∧ t ≤ 75023
  refine ⟨ht25, by omega, ?_, htb⟩
  nlinarith [show 3*d.toNat ≤ 2*((3*d.toNat+1)/2) by omega]

#print axioms restSeconds_bounds
end Project.Drone.Arithmetic
