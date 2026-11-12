import Demos.Orbit.GibbsBox

/-!
Soundness of Gibbs' interval program.  `gibbsBox_sound` (G2) states that the intervals of a
result with status 0 contain the velocity at `r2` of every orbit with positions `r1`, `r2`, `r3`
in the three boxes in the order of motion, for every `μ` in its interval, and `gibbsBox_no_orbit`
(G3) states that no orbit has positions in the three boxes when the status is 1.
`gibbsBounds_sound` restates G2 for the program on endpoints.
-/

namespace Demos.Orbit

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 V3
open CodeLib.IEEE64 (value Finite)

/-- The point `r` lies in the box of the three intervals. -/
def InBox (x y z : Interval) (r : V3) : Prop := Contains x r.x ∧ Contains y r.y ∧ Contains z r.z

theorem gibbsCoords_eq (μ : ℝ) (r1 r2 r3 : V3) :
    gibbsCoords r1.x r1.y r1.z r2.x r2.y r2.z r3.x r3.y r3.z μ =
      ((gibbs μ r1 r2 r3).x, (gibbs μ r1 r2 r3).y, (gibbs μ r1 r2 r3).z) := by
  simp only [gibbsCoords, lengthOf, crossOf, weighted, sqr, gibbs, gibbsN, gibbsD, gibbsS,
    V3.norm, dot, smul_x, smul_y, smul_z, add_x, add_y, add_z, cross_x, cross_y, cross_z]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring_nf

theorem triple_eq (r1 r2 r3 : V3) :
    triple r1.x r1.y r1.z r2.x r2.y r2.z r3.x r3.y r3.z = dot r1 (cross r2 r3) := by
  simp only [triple, dot, cross_x, cross_y, cross_z]

theorem gibbsCoordsI_tables (x1 y1 z1 x2 y2 z2 x3 y3 z3 mu : Interval) :
    gibbsCoordsI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 x3 y3 z3 mu =
      gibbsCoordsI Trig.invPi Trig.halfPi noTable noTable x1 y1 z1 x2 y2 z2 x3 y3 z3 mu := rfl

theorem tripleI_tables (x1 y1 z1 x2 y2 z2 x3 y3 z3 : Interval) :
    tripleI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 x3 y3 z3 =
      tripleI Trig.invPi Trig.halfPi noTable noTable x1 y1 z1 x2 y2 z2 x3 y3 z3 := rfl

theorem InBox.encloses {x y z : Interval} {r : V3} (h : InBox x y z r) :
    Encloses x r.x ∧ Encloses y r.y ∧ Encloses z r.z :=
  ⟨fun _ => h.1, fun _ => h.2.1, fun _ => h.2.2⟩

/-- Three positions on the path of one orbit lie in a plane through the origin. -/
theorem triple_zero {μ : ℝ} {o : Conic} {r1 r2 r3 : V3} (h1 : OnPath μ o r1)
    (h2 : OnPath μ o r2) (h3 : OnPath μ o r3) : dot r1 (cross r2 r3) = 0 := by
  rw [cross_eq_smul h1.1 h2.2.2.1 h3.2.2.1, dot_smul, h1.2.2.1, mul_zero]

variable {x1 y1 z1 x2 y2 z2 x3 y3 z3 mu : Interval} {μ : ℝ} {o : Conic} {r1 r2 r3 : V3}

/-- **G2.**  The intervals of a result with status 0 contain the velocity at `r2` of every orbit
with positions in the three boxes in the order of motion, for every `μ` in its interval. -/
theorem gibbsBox_sound (hs : (gibbsBox x1 y1 z1 x2 y2 z2 x3 y3 z3 mu).status = 0)
    (hμ : Contains mu μ) (b1 : InBox x1 y1 z1 r1) (b2 : InBox x2 y2 z2 r2)
    (b3 : InBox x3 y3 z3 r3) (h1 : OnPath μ o r1) (h2 : OnPath μ o r2) (h3 : OnPath μ o r3)
    (hD : 0 < dot (gibbsD r1 r2 r3) o.h) :
    InBox (gibbsBox x1 y1 z1 x2 y2 z2 x3 y3 z3 mu).vx (gibbsBox x1 y1 z1 x2 y2 z2 x3 y3 z3 mu).vy
      (gibbsBox x1 y1 z1 x2 y2 z2 x3 y3 z3 mu).vz (velocityAt μ o r2) := by
  have henc := gibbsCoords.encloses (powLog := noTable) (powExp := noTable)
    b1.encloses.1 b1.encloses.2.1 b1.encloses.2.2 b2.encloses.1 b2.encloses.2.1 b2.encloses.2.2
    b3.encloses.1 b3.encloses.2.1 b3.encloses.2.2 (fun _ => hμ)
  rw [← gibbsCoordsI_tables, gibbsCoords_eq] at henc
  simp only [gibbsBox] at hs ⊢
  split_ifs at hs ⊢ with hv hm ht hok
  · simp [noVelocity] at hs
  · simp only [Bool.and_eq_true, beq_iff_eq] at hok
    have hμ0 : 0 < μ := hμ.pos_of_lo hm
    rw [(gibbs_velocity hμ0 h1 h2 h3 hD).2] at henc
    exact ⟨henc.1 hok.1.1, henc.2.1 hok.1.2, henc.2.2 hok.2⟩
  · simp [noVelocity] at hs
  · simp [noVelocity] at hs
  · simp [noVelocity] at hs

/-- **G3.**  When the status is 1, no orbit has a position in each of the three boxes. -/
theorem gibbsBox_no_orbit (hs : (gibbsBox x1 y1 z1 x2 y2 z2 x3 y3 z3 mu).status = 1)
    (b1 : InBox x1 y1 z1 r1) (b2 : InBox x2 y2 z2 r2) (b3 : InBox x3 y3 z3 r3)
    (h1 : OnPath μ o r1) (h2 : OnPath μ o r2) (h3 : OnPath μ o r3) : False := by
  have henc := triple.encloses (powLog := noTable) (powExp := noTable)
    b1.encloses.1 b1.encloses.2.1 b1.encloses.2.2 b2.encloses.1 b2.encloses.2.1 b2.encloses.2.2
    b3.encloses.1 b3.encloses.2.1 b3.encloses.2.2
  rw [← tripleI_tables, triple_eq, triple_zero h1 h2 h3] at henc
  simp only [gibbsBox] at hs
  split_ifs at hs with hv hm ht hok
  · have c := henc ht.1
    rcases ht.2 with h | h
    · exact lt_irrefl _ (c.pos_of_lo h)
    · exact lt_irrefl _ (c.neg_of_hi h)
  all_goals simp [noVelocity] at hs

theorem valid_status {a : Interval} (h : valid a = true) : a.status = 0 := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

/-- The inputs of a result with status 0 are accepted. -/
theorem gibbsBox_inputs (hs : (gibbsBox x1 y1 z1 x2 y2 z2 x3 y3 z3 mu).status = 0) :
    x1.status = 0 ∧ y1.status = 0 ∧ z1.status = 0 ∧ x2.status = 0 ∧ y2.status = 0 ∧
      z2.status = 0 ∧ x3.status = 0 ∧ y3.status = 0 ∧ z3.status = 0 ∧ mu.status = 0 := by
  simp only [gibbsBox] at hs
  split_ifs at hs with hv
  all_goals first
    | (simp only [Bool.and_eq_true] at hv
       obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨v1, v2⟩, v3⟩, v4⟩, v5⟩, v6⟩, v7⟩, v8⟩, v9⟩, v10⟩ := hv
       exact ⟨valid_status v1, valid_status v2, valid_status v3, valid_status v4,
         valid_status v5, valid_status v6, valid_status v7, valid_status v8, valid_status v9,
         valid_status v10⟩)
    | simp [noVelocity] at hs

/-- The real numbers between the values of two endpoints. -/
def Between (lo hi : Float) (x : ℝ) : Prop := value lo.toBits ≤ x ∧ x ≤ value hi.toBits

theorem contains_make {lo hi : Float} {x : ℝ} (h : (make lo hi).status = 0)
    (hx : Between lo hi x) : Contains (make lo hi) x :=
  (make_sound h).2.2.2 x hx.1 hx.2

/-- **G2 on endpoints.**  For a result of `gibbsBounds` with status 0, each real coordinate
between its endpoints, and each `μ` between its endpoints, the intervals contain the velocity at
`r2` of every orbit through the three positions in the order of motion. -/
theorem gibbsBounds_sound {x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi x3lo x3hi
    y3lo y3hi z3lo z3hi mulo muhi : Float}
    (hs : (gibbsBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi x3lo x3hi
      y3lo y3hi z3lo z3hi mulo muhi).status = 0)
    (c1 : Between x1lo x1hi r1.x ∧ Between y1lo y1hi r1.y ∧ Between z1lo z1hi r1.z)
    (c2 : Between x2lo x2hi r2.x ∧ Between y2lo y2hi r2.y ∧ Between z2lo z2hi r2.z)
    (c3 : Between x3lo x3hi r3.x ∧ Between y3lo y3hi r3.y ∧ Between z3lo z3hi r3.z)
    (cμ : Between mulo muhi μ)
    (h1 : OnPath μ o r1) (h2 : OnPath μ o r2) (h3 : OnPath μ o r3)
    (hD : 0 < dot (gibbsD r1 r2 r3) o.h) :
    InBox (gibbsBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi x3lo x3hi
        y3lo y3hi z3lo z3hi mulo muhi).vx
      (gibbsBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi x3lo x3hi
        y3lo y3hi z3lo z3hi mulo muhi).vy
      (gibbsBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi x3lo x3hi
        y3lo y3hi z3lo z3hi mulo muhi).vz (velocityAt μ o r2) := by
  unfold gibbsBounds at hs ⊢
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := gibbsBox_inputs hs
  exact gibbsBox_sound hs (contains_make a10 cμ)
    ⟨contains_make a1 c1.1, contains_make a2 c1.2.1, contains_make a3 c1.2.2⟩
    ⟨contains_make a4 c2.1, contains_make a5 c2.2.1, contains_make a6 c2.2.2⟩
    ⟨contains_make a7 c3.1, contains_make a8 c3.2.1, contains_make a9 c3.2.2⟩ h1 h2 h3 hD

end Demos.Orbit
