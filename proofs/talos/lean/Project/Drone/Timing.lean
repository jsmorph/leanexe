import Project.Drone.Dynamics

namespace Project.Drone.Timing
open LeanExe.Examples.Drone Arithmetic Edges Dynamics

/-- Accepted moving edges return the exact integer tick formula. -/
theorem accepted_ticks (r0 r1 z0 z1 u v : UInt64)
    (h : 0 < edgeTicks r0 r1 z0 z1 u v) (ht : u+v ≠ 0) :
    edgeTicks r0 r1 z0 z1 u v = 33600/((u+v)/5) := by
  simp only [edgeTicks, Id.run, pure, BEq.beq, decide_eq_true_eq] at h ⊢
  split at h
  · contradiction
  · rename_i ht'
    rw [if_neg ht']
    split at h
    · simp at h
    · rename_i ha
      rw [if_neg ha]
      split at h
      · simp at h
      · rename_i hv
        rw [if_neg hv]
        split at h
        · simp at h
        · rename_i hz
          rw [if_neg hz]
          split at h
          · rename_i hr
            rw [if_pos hr]
            split at h
            · simp at h
            · rename_i hc
              rw [if_neg hc]
          · rename_i hr
            rw [if_neg hr]
            split at h
            · simp at h
            · rename_i hc
              rw [if_neg hc]

theorem rest_ticks (r0 r1 z0 z1 : UInt64)
    (hz0 : z0.toNat ≤ heightLimit) (hz1 : z1.toNat ≤ heightLimit) :
    (edgeTicks r0 r1 z0 z1 0 0).toNat = 840*(restSeconds (distance z0 z1)).toNat := by
  have hb := (restSeconds_bounds (distance z0 z1) (distance_le z0 z1 hz0 hz1)).2.2.2
  simp only [edgeTicks, Id.run, pure]
  change (840*restSeconds (distance z0 z1)).toNat = _
  rw [UInt64.toNat_mul]
  change (840*(restSeconds (distance z0 z1)).toNat)%18446744073709551616 = _
  exact Nat.mod_eq_of_lt (by omega)

/-- Every all-stop primitive is admitted and has a bounded positive cost. -/
theorem rest_admitted (r0 r1 z0 z1 : UInt64)
    (hz0 : z0.toNat ≤ heightLimit) (hz1 : z1.toNat ≤ heightLimit) :
    0 < edgeTicks r0 r1 z0 z1 0 0 ∧
    (edgeTicks r0 r1 z0 z1 0 0).toNat ≤ 63019320 := by
  have hb := restSeconds_bounds (distance z0 z1) (distance_le z0 z1 hz0 hz1)
  rw [UInt64.lt_iff_toNat_lt, rest_ticks r0 r1 z0 z1 hz0 hz1]
  change 0 < 840*(restSeconds (distance z0 z1)).toNat ∧ _
  omega

theorem moving_tick_fraction (k : Nat) (hk0 : 1 ≤ k) (hk1 : k ≤ 8) :
    ((33600/k:Nat):ℝ)/840 = 200/(5*(k:ℝ)) := by
  have h : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 := by omega
  rcases h with h|h|h|h|h|h|h|h <;> subst k <;> norm_num

/-- The moving edge's UInt64 tick count encodes its real duration exactly. -/
theorem state_ticks_exact (r0 r1 z0 z1 : UInt64) (source target : Nat)
    (hedge : 0 < edgeTicks r0 r1 z0 z1 (speed source) (speed target))
    (ht : speed source+speed target ≠ 0) :
    real (edgeTicks r0 r1 z0 z1 (speed source) (speed target))/840 =
      200/(real (speed source)+real (speed target)) := by
  have hs := Nat.mod_lt source (by decide : 0<5)
  have hv := Nat.mod_lt target (by decide : 0<5)
  have hsum := (products_nat 0 (speed source) (speed target) (by decide)
    (speed_le source) (speed_le target)).1
  rw [speed_nat, speed_nat] at hsum
  have hn : (speed source+speed target).toNat ≠ 0 := fun h => ht (UInt64.toNat_inj.mp h)
  have hk0 : 1 ≤ source%5+target%5 := by omega
  have hk1 : source%5+target%5 ≤ 8 := by omega
  have hdiv : ((speed source+speed target)/5).toNat = source%5+target%5 := by
    rw [UInt64.toNat_div, hsum]
    change (source%5*5+target%5*5)/5 = source%5+target%5
    omega
  rw [accepted_ticks r0 r1 z0 z1 _ _ hedge ht]
  dsimp [real]
  rw [UInt64.toNat_div, hdiv, speed_nat, speed_nat]
  change ((33600/(source%5+target%5):Nat):ℝ)/840 = _
  rw [moving_tick_fraction _ hk0 hk1]
  push_cast
  congr 1
  ring

/-- Every edge has a bounded cost, whether admitted or rejected. -/
theorem edge_cost_bound (r0 r1 z0 z1 u v : UInt64)
    (hz0 : z0.toNat ≤ heightLimit) (hz1 : z1.toNat ≤ heightLimit) :
    (edgeTicks r0 r1 z0 z1 u v).toNat ≤ 63019320 := by
  have hr := restSeconds_bounds (distance z0 z1) (distance_le z0 z1 hz0 hz1)
  have hrest : (840*restSeconds (distance z0 z1)).toNat ≤ 63019320 := by
    rw [UInt64.toNat_mul]
    change (840*(restSeconds (distance z0 z1)).toNat)%18446744073709551616 ≤ _
    exact le_trans (Nat.mod_le _ _) (by omega)
  have hmove : (33600/((u+v)/5)).toNat ≤ 63019320 := by
    rw [UInt64.toNat_div]
    change 33600/((u+v)/5).toNat ≤ _
    exact le_trans (Nat.div_le_self _ _) (by decide)
  simp only [edgeTicks, Id.run, pure]
  split
  · exact hrest
  · split
    · decide
    · split
      · decide
      · split
        · decide
        · split <;> split
          all_goals first | decide | exact hmove

#print axioms state_ticks_exact
#print axioms rest_admitted
#print axioms edge_cost_bound
end Project.Drone.Timing
