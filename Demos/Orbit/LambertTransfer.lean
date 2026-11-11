import Demos.Orbit.LambertSound
import Demos.Orbit.LambertTime

/-!
The transfer that an accepted result of Lambert's program states.  `lambertBox_accepts` states
that status 0 shows `t > 0`, `μ > 0`, and `(r1 × r2) · k ≠ 0` for every input in the boxes, and
`lambertBox_transfer` combines L4 with the theorems on Izzo's orbit: for every input in the
boxes, the intervals contain the root `x*` and Izzo's velocities `v1` and `v2` at it, the states
`(r1, v1)` and `(r2, v2)` have one orbit whose angular momentum `h` has `h · k > 0`, a
velocity at `r1` starts an elliptic transfer to `r2` in the time `t` in the direction of `k`
exactly when `x* < 1` and it is `v1`, and when `x* < 1` a solution of Newton's equation goes
from `(r1, v1)` to `(r2, v2)` in the time `t`.
-/

namespace Demos.Orbit

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 V3 Real
open CodeLib.IEEE64 (value Finite)

/-- The axis `k` of the direction of motion from its binary64 components. -/
noncomputable def axisOf (kx ky kz : Float) : V3 :=
  ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩

/-- A result of `lambertBox` with status 0 shows `t > 0`, `μ > 0`, and `(r1 × r2) · k ≠ 0` for
every input in the boxes. -/
theorem lambertBox_accepts {x1 y1 z1 x2 y2 z2 t mu : Interval} {kx ky kz : Float}
    (hs : (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).status = 0) {r1 r2 : V3} {t' μ : ℝ}
    (b1 : InBox x1 y1 z1 r1) (b2 : InBox x2 y2 z2 r2) (ht : Contains t t')
    (hμ : Contains mu μ) :
    0 < t' ∧ 0 < μ ∧ dot (cross r1 r2) (axisOf kx ky kz) ≠ 0 := by
  have hd := direction.encloses (powLog := noTable) (powExp := noTable)
    b1.encloses.1 b1.encloses.2.1 b1.encloses.2.2 b2.encloses.1 b2.encloses.2.1
    b2.encloses.2.2 (point_encloses kx) (point_encloses ky) (point_encloses kz)
  rw [← directionI_tables, direction_eq'] at hd
  unfold lambertBox lambertBoxWith at hs
  dsimp only at hs
  generalize directionI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 (point kx) (point ky)
    (point kz) = d at hd hs
  generalize geometryI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 t mu (signOf d) = g
    at hs
  split_ifs at hs with hv hp hdir hg hT
  · have cd := hd hdir.1
    refine ⟨ht.pos_of_lo hp.1, hμ.pos_of_lo hp.2, ?_⟩
    rcases hdir.2 with h | h
    · exact (cd.pos_of_lo h).ne'
    · exact (cd.neg_of_hi h).ne
  all_goals simp [noTransfer] at hs

/-- **An accepted result states the transfer.**  For a result of `lambertBox` with status 0
and every input in the boxes, the intervals contain the root `x*` of Izzo's equation and the
components of Izzo's velocities `v1` at `r1` and `v2` at `r2` at `x*` (L4).  The states
`(r1, v1)` and `(r2, v2)` have one orbit, whose angular momentum `r1 × v1` has a positive
component along `k`.  A velocity `v` at `r1` starts a motion in the direction of `k` that first
reaches `r2` along an ellipse after the time `t` exactly when `x* < 1` and `v = v1`, and when
`x* < 1` a solution of Newton's equation goes from `(r1, v1)` to `(r2, v2)` in the time `t`. -/
theorem lambertBox_transfer {x1 y1 z1 x2 y2 z2 t mu : Interval} {kx ky kz : Float}
    (hs : (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).status = 0) {r1 r2 : V3} {t' μ : ℝ}
    (b1 : InBox x1 y1 z1 r1) (b2 : InBox x2 y2 z2 r2) (ht : Contains t t')
    (hμ : Contains mu μ) :
    Inside (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz)
        (solution r1 r2 t' μ (axisOf kx ky kz)) ∧
      orbitOf μ r2 (izzoV2 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))) =
        orbitOf μ r1 (izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))) ∧
      0 < dot (cross r1 (izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))))
        (axisOf kx ky kz) ∧
      (∀ v : V3, (EllipticTransfer μ r1 v r2 t' ∧ 0 < dot (cross r1 v) (axisOf kx ky kz)) ↔
        (izzoRoot r1 r2 t' μ (axisOf kx ky kz) < 1 ∧
          v = izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz)))) ∧
      (izzoRoot r1 r2 t' μ (axisOf kx ky kz) < 1 →
        NewtonTransfer μ r1
          (izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))) r2
          (izzoV2 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))) t') := by
  obtain ⟨ht0, hμ0, hD⟩ := lambertBox_accepts hs b1 b2 ht hμ
  obtain ⟨-, -, -, hin⟩ := lambertBox_sound hs b1 b2 ht hμ
  obtain ⟨horb, -, -, -, -, hk⟩ := izzo_orbit hμ0 hD (izzoRoot r1 r2 t' μ (axisOf kx ky kz))
  exact ⟨hin, horb, hk, lambert_elliptic hμ0 ht0 hD, lambert_newton hμ0 ht0 hD⟩

/-- **The transfer on endpoints.** -/
theorem lambertBounds_transfer {x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo
    thi mulo muhi kx ky kz : Float} {r1 r2 : V3} {t' μ : ℝ}
    (hs : (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi mulo
      muhi kx ky kz).status = 0)
    (c1 : Between x1lo x1hi r1.x ∧ Between y1lo y1hi r1.y ∧ Between z1lo z1hi r1.z)
    (c2 : Between x2lo x2hi r2.x ∧ Between y2lo y2hi r2.y ∧ Between z2lo z2hi r2.z)
    (ct : Between tlo thi t') (cμ : Between mulo muhi μ) :
    Inside (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
        mulo muhi kx ky kz)
        (solution r1 r2 t' μ (axisOf kx ky kz)) ∧
      orbitOf μ r2 (izzoV2 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))) =
        orbitOf μ r1 (izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))) ∧
      0 < dot (cross r1 (izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))))
        (axisOf kx ky kz) ∧
      (∀ v : V3, (EllipticTransfer μ r1 v r2 t' ∧ 0 < dot (cross r1 v) (axisOf kx ky kz)) ↔
        (izzoRoot r1 r2 t' μ (axisOf kx ky kz) < 1 ∧
          v = izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz)))) ∧
      (izzoRoot r1 r2 t' μ (axisOf kx ky kz) < 1 →
        NewtonTransfer μ r1
          (izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))) r2
          (izzoV2 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))) t') := by
  have hin : (make x1lo x1hi).status = 0 ∧ (make y1lo y1hi).status = 0 ∧
      (make z1lo z1hi).status = 0 ∧ (make x2lo x2hi).status = 0 ∧ (make y2lo y2hi).status = 0 ∧
      (make z2lo z2hi).status = 0 ∧ (make tlo thi).status = 0 ∧ (make mulo muhi).status = 0 := by
    unfold lambertBounds lambertBoundsWith lambertBoxWith at hs
    dsimp only at hs
    split_ifs at hs with hv
    all_goals first
      | (simp only [Bool.and_eq_true] at hv
         obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨v1, v2⟩, v3⟩, v4⟩, v5⟩, v6⟩, v7⟩, v8⟩, -⟩, -⟩, -⟩ := hv
         exact ⟨valid_status v1, valid_status v2, valid_status v3, valid_status v4,
           valid_status v5, valid_status v6, valid_status v7, valid_status v8⟩)
      | simp [noTransfer] at hs
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hin
  unfold lambertBounds lambertBoundsWith at hs ⊢
  exact lambertBox_transfer hs
    ⟨contains_make a1 c1.1, contains_make a2 c1.2.1, contains_make a3 c1.2.2⟩
    ⟨contains_make a4 c2.1, contains_make a5 c2.2.1, contains_make a6 c2.2.2⟩
    (contains_make a7 ct) (contains_make a8 cμ)

end Demos.Orbit
