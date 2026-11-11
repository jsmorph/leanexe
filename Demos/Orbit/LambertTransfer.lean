import Demos.Orbit.LambertSound
import Demos.Orbit.LambertTime

/-!
The transfer that an accepted result of Lambert's program states.  `lambertBox_accepts` states
that status 0 shows `t > 0`, `μ > 0`, and `(r1 × r2) · k ≠ 0` for every input in the boxes, and
`lambertBox_transfer` combines L4 with `lambert_newton`: for every input in the boxes, exactly
one solution of Newton's equation starts at `r1` in the direction of `k` and first reaches `r2`
at the time `t`, and the six intervals of the result contain its velocities at `r1` and `r2`.
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

/-- **An accepted result states the transfer.**  For a result of `lambertBox` with status 0 and
every input in the boxes, exactly one pair of velocities `(v, v')` has a solution of Newton's
equation that starts at `(r1, v)` with `(r1 × v) · k > 0` and first reaches `r2` at the time `t`
with the velocity `v'`, and the intervals of the result contain the components of `v` and `v'`.
The pair is Izzo's `(v1(x*), v2(x*))` (`lambert_newton`), and the interval of `x` contains `x*`
(L4). -/
theorem lambertBox_transfer {x1 y1 z1 x2 y2 z2 t mu : Interval} {kx ky kz : Float}
    (hs : (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).status = 0) {r1 r2 : V3} {t' μ : ℝ}
    (b1 : InBox x1 y1 z1 r1) (b2 : InBox x2 y2 z2 r2) (ht : Contains t t')
    (hμ : Contains mu μ) :
    (∃! p : V3 × V3,
        NewtonTransfer μ r1 p.1 r2 p.2 t' ∧ 0 < dot (cross r1 p.1) (axisOf kx ky kz)) ∧
      ∀ v v' : V3, NewtonTransfer μ r1 v r2 v' t' ∧ 0 < dot (cross r1 v) (axisOf kx ky kz) →
        InBox (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).v1x
            (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).v1y
            (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).v1z v ∧
          InBox (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).v2x
            (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).v2y
            (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).v2z v' := by
  obtain ⟨ht0, hμ0, hD⟩ := lambertBox_accepts hs b1 b2 ht hμ
  obtain ⟨-, -, -, hin⟩ := lambertBox_sound hs b1 b2 ht hμ
  have hL := lambert_newton hμ0 ht0 hD (k := axisOf kx ky kz)
  refine ⟨⟨(izzoV1 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz)),
      izzoV2 μ r1 r2 (axisOf kx ky kz) (izzoRoot r1 r2 t' μ (axisOf kx ky kz))),
      (hL _ _).mpr ⟨rfl, rfl⟩, fun p hp => ?_⟩, fun v v' hv => ?_⟩
  · obtain ⟨h1, h2⟩ := (hL _ _).mp hp
    exact Prod.ext h1 h2
  · obtain ⟨rfl, rfl⟩ := (hL _ _).mp hv
    obtain ⟨-, c1, c2, c3, c4, c5, c6⟩ := hin
    exact ⟨⟨c1, c2, c3⟩, ⟨c4, c5, c6⟩⟩

/-- **The transfer on endpoints.** -/
theorem lambertBounds_transfer {x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo
    thi mulo muhi kx ky kz : Float} {r1 r2 : V3} {t' μ : ℝ}
    (hs : (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi mulo
      muhi kx ky kz).status = 0)
    (c1 : Between x1lo x1hi r1.x ∧ Between y1lo y1hi r1.y ∧ Between z1lo z1hi r1.z)
    (c2 : Between x2lo x2hi r2.x ∧ Between y2lo y2hi r2.y ∧ Between z2lo z2hi r2.z)
    (ct : Between tlo thi t') (cμ : Between mulo muhi μ) :
    (∃! p : V3 × V3,
        NewtonTransfer μ r1 p.1 r2 p.2 t' ∧ 0 < dot (cross r1 p.1) (axisOf kx ky kz)) ∧
      ∀ v v' : V3, NewtonTransfer μ r1 v r2 v' t' ∧ 0 < dot (cross r1 v) (axisOf kx ky kz) →
        InBox (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
              mulo muhi kx ky kz).v1x
            (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
              mulo muhi kx ky kz).v1y
            (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
              mulo muhi kx ky kz).v1z v ∧
          InBox (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
              mulo muhi kx ky kz).v2x
            (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
              mulo muhi kx ky kz).v2y
            (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
              mulo muhi kx ky kz).v2z v' := by
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
