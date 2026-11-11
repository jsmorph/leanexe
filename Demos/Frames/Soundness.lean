import Demos.Frames.Program

/-!
What an accepted result of each program states about the model.  `gmst_sound` states that the
interval of an accepted angle contains the sidereal angle of every second of the argument's
interval, less one whole number of turns, and `temeToEcef_sound` that the intervals of an accepted
position contain the Earth-fixed position of every TEME position, second, and polar motion of the
arguments' intervals.
-/

open Real

namespace Demos.Frames

open Library.Numerics.Interval Library.Numerics.Float64 LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite)

/-- The real number `x` lies between the values of `lo` and `hi`. -/
def Within (lo hi : Float) (x : ℝ) : Prop := value lo.toBits ≤ x ∧ x ≤ value hi.toBits

theorem contains_make {lo hi : Float} (h : (make lo hi).status = 0) {x : ℝ} (hx : Within lo hi x) :
    Contains (make lo hi) x :=
  (make_sound h).2.2.2 x hx.1 hx.2

theorem within_of_make {lo hi : Float} (h : (make lo hi).status = 0) :
    Finite lo.toBits ∧ Finite hi.toBits ∧ value lo.toBits ≤ value hi.toBits :=
  ⟨(make_sound h).1, (make_sound h).2.1, (make_sound h).2.2.1⟩

/-- The interval of a day below `2³²` holds its value. -/
theorem encloses_day {d : UInt64} (hd : d.toNat < 2 ^ 32) :
    Encloses (ofInt d.toInt64) (d.toNat : ℝ) :=
  encloses_ofInt' (m := (d.toNat : ℤ))
    (by rw [Signed64Value.toInt_toInt64]; split <;> omega)
    (by rw [Int.natAbs_natCast]; omega) (by push_cast; rfl)

theorem natAbs_of_bounds {n : Int64}
    (h : (decide (-9007199254740992 ≤ n) && decide (n ≤ 9007199254740992)) = true) :
    n.toInt.natAbs ≤ 2 ^ 53 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, Int64.le_iff_toInt_le] at h
  have e1 : (-9007199254740992 : Int64).toInt = -9007199254740992 := by decide
  have e2 : (9007199254740992 : Int64).toInt = 9007199254740992 := by decide
  rw [e1, e2] at h
  omega

/-- The interval of `angleWith` encloses the sidereal angle of every point of `s`, less one whole
number of turns. -/
theorem angleWith_encloses {d : UInt64} {s : Interval} (hd : d.toNat < 2 ^ 32) :
    ∃ k : ℤ, ∀ x, Contains s x → Encloses (angleWith Trig.invPi Trig.halfPi d s)
      (Model.gmst82 (Model.julian d.toNat x) - 2 * π * k) := by
  unfold angleWith
  generalize hw : gmstSecondsI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi
    (ofInt d.toInt64) s = w
  by_cases h1 : (w.status == 0) = true
  · simp only [h1, ite_true]
    generalize floorOf (mid w / 86400.0) = n
    by_cases h2 : (decide (-9007199254740992 ≤ n) && decide (n ≤ 9007199254740992)) = true
    · simp only [h2, ite_true]
      have hn := natAbs_of_bounds h2
      refine ⟨(d.toNat : ℤ) - 51544 + n.toInt, fun x hx => ?_⟩
      have hW : Encloses w (gmstSeconds d.toNat x) :=
        hw ▸ gmstSeconds.encloses (encloses_day hd) (fun _ => hx)
      have ht := turns.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hW (encloses_ofInt (n := n) hn rfl)
      rw [turns_eq] at ht
      have e : Model.gmst82 (Model.julian (d.toNat : ℝ) x) -
          2 * π * (((d.toNat : ℝ) - 51544) + (n.toInt : ℝ)) =
          Model.gmst82 (Model.julian (d.toNat : ℝ) x) -
            2 * π * (((d.toNat : ℤ) - 51544 + n.toInt : ℤ) : ℝ) := by push_cast; ring
      rwa [e] at ht
    · simp only [h2, Bool.false_eq_true, ite_false]
      exact ⟨0, fun _ _ h => absurd h (by decide)⟩
  · simp only [h1, Bool.false_eq_true, ite_false]
    exact ⟨0, fun _ _ h => absurd h (by decide)⟩

/-- The values of the integers −1 and 7 as floats. -/
theorem range_values : Finite ((-1 : Int64).toFloat).toBits ∧
    value ((-1 : Int64).toFloat).toBits = -1 ∧ Finite ((7 : Int64).toFloat).toBits ∧
    value ((7 : Int64).toFloat).toBits = 7 := by
  obtain ⟨f1, v1⟩ := Signed64Value.toFloat_exact (-1) (by decide)
  obtain ⟨f7, v7⟩ := Signed64Value.toFloat_exact 7 (by decide)
  have e1 : ((-1 : Int64).toInt : ℝ) = -1 := by
    have : (-1 : Int64).toInt = -1 := by decide
    rw [this]; norm_num
  have e7 : ((7 : Int64).toInt : ℝ) = 7 := by
    have : (7 : Int64).toInt = 7 := by decide
    rw [this]; norm_num
  exact ⟨f1, v1.trans e1, f7, v7.trans e7⟩

/-- **Sidereal time.**  An accepted result of `gmst` has a day below `2³²`, finite ordered
arguments, and finite endpoints in `[−1, 7]`, and some integer `k` puts the sidereal angle of
every second `s` of the argument's interval, less `2πk`, in the result's interval. -/
theorem gmst_sound {d : UInt64} {lo hi : Float} (h : (gmst d lo hi).status = 0) :
    d.toNat < 2 ^ 32 ∧ Finite lo.toBits ∧ Finite hi.toBits ∧ value lo.toBits ≤ value hi.toBits ∧
      Finite (gmst d lo hi).lo.toBits ∧ Finite (gmst d lo hi).hi.toBits ∧
      -1 ≤ value (gmst d lo hi).lo.toBits ∧ value (gmst d lo hi).hi.toBits ≤ 7 ∧
      ∃ k : ℤ, ∀ s, Within lo hi s →
        Within (gmst d lo hi).lo (gmst d lo hi).hi
          (Model.gmst82 (Model.julian d.toNat s) - 2 * π * k) := by
  unfold gmst gmstWith at h ⊢
  by_cases h1 : (decide (d < 4294967296) && (make lo hi).status == 0) = true
  · simp only [h1, ite_true] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
    have hd : d.toNat < 2 ^ 32 := by
      have := UInt64.lt_iff_toNat_lt.1 h1.1; simpa using this
    obtain ⟨k, hk⟩ := angleWith_encloses (s := make lo hi) hd
    generalize angleWith Trig.invPi Trig.halfPi d (make lo hi) = r at h hk ⊢
    by_cases h2 : (r.status == 0 && decide ((-1 : Int64).toFloat ≤ r.lo) &&
        decide (r.hi ≤ (7 : Int64).toFloat)) = true
    · simp only [h2, ite_true] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
      obtain ⟨⟨hr, hlo⟩, hhi⟩ := h2
      obtain ⟨f1, f2, f3⟩ := within_of_make h1.2
      have c0 := hk (value lo.toBits) (contains_make h1.2 ⟨le_rfl, f3⟩) hr
      obtain ⟨fm1, vm1, f7, v7⟩ := range_values
      refine ⟨hd, f1, f2, f3, c0.2.1, c0.2.2.1, ?_, ?_, k,
        fun s hs => (hk s (contains_make h1.2 hs) hr).2.2.2⟩
      · have := (le_iff_value fm1 c0.2.1).mp hlo; rwa [vm1] at this
      · have := (le_iff_value c0.2.2.1 f7).mp hhi; rwa [v7] at this
    · simp only [h2, Bool.false_eq_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [h1, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- **The Earth-fixed frame.**  An accepted result of `temeToEcef` has a day below `2³²`, and its
three intervals contain the components of the Earth-fixed position `R1(−yp) R2(−xp) R3(θ) r` for
the sidereal angle `θ` of every second `s` and every polar motion `xp`, `yp` and TEME position `r`
of the arguments' intervals. -/
theorem temeToEcef_sound {d : UInt64}
    {slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi : Float}
    (h : (temeToEcef d slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi).status = 0) :
    d.toNat < 2 ^ 32 ∧
      ∀ s xp yp x y z, Within slo shi s → Within xplo xphi xp → Within yplo yphi yp →
        Within xlo xhi x → Within ylo yhi y → Within zlo zhi z →
        let r := temeToEcef d slo shi xplo xphi yplo yphi xlo xhi ylo yhi zlo zhi
        let e := Model.earthFixed (Model.gmst82 (Model.julian d.toNat s)) xp yp (x, y, z)
        Contains r.x e.1 ∧ Contains r.y e.2.1 ∧ Contains r.z e.2.2 := by
  unfold temeToEcef temeToEcefWith at h ⊢
  by_cases h1 : (decide (d < 4294967296) && (make slo shi).status == 0 &&
      (make xplo xphi).status == 0 && (make yplo yphi).status == 0 &&
      (make xlo xhi).status == 0 && (make ylo yhi).status == 0 &&
      (make zlo zhi).status == 0) = true
  · simp only [h1, ite_true] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
    obtain ⟨⟨⟨⟨⟨⟨hd', hs⟩, hxp⟩, hyp⟩, hx⟩, hy⟩, hz⟩ := h1
    have hd : d.toNat < 2 ^ 32 := by
      have := UInt64.lt_iff_toNat_lt.1 hd'; simpa using this
    generalize hr : toEarthI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi
      (angleWith Trig.invPi Trig.halfPi d (make slo shi)) (make xplo xphi) (make yplo yphi)
      (make xlo xhi) (make ylo yhi) (make zlo zhi) = r at h ⊢
    by_cases h2 : (r.1.status == 0 && r.2.1.status == 0 && r.2.2.status == 0) = true
    · simp only [h2, ite_true] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨r1, r2⟩, r3⟩ := h2
      obtain ⟨k, hk⟩ := angleWith_encloses (s := make slo shi) hd
      refine ⟨hd, fun s xp yp x y z hs' hxp' hyp' hx' hy' hz' => ?_⟩
      have rel := toEarth.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) (hk s (contains_make hs hs'))
        (fun _ => contains_make hxp hxp') (fun _ => contains_make hyp hyp')
        (fun _ => contains_make hx hx') (fun _ => contains_make hy hy')
        (fun _ => contains_make hz hz')
      rw [hr, toEarth_periodic, toEarth_eq] at rel
      exact ⟨rel.1 r1, rel.2.1 r2, rel.2.2 r3⟩
    · simp only [h2, Bool.false_eq_true, ite_false, noVec] at h
      exact absurd h (by decide)
  · simp only [h1, Bool.false_eq_true, ite_false, noVec] at h
    exact absurd h (by decide)

/-! ### Geodetic coordinates -/

/-- **Geodetic to Cartesian.**  The intervals of an accepted result of `toCartesian` contain the
position of every latitude, longitude, and height of the arguments' intervals. -/
theorem toCartesian_sound {latlo lathi lonlo lonhi hlo hhi : Float}
    (h : (toCartesian latlo lathi lonlo lonhi hlo hhi).status = 0) :
    ∀ φ lon hh, Within latlo lathi φ → Within lonlo lonhi lon → Within hlo hhi hh →
      let r := toCartesian latlo lathi lonlo lonhi hlo hhi
      let e := Model.position φ lon hh
      Contains r.x e.1 ∧ Contains r.y e.2.1 ∧ Contains r.z e.2.2 := by
  unfold toCartesian toCartesianWith at h ⊢
  by_cases h1 : ((make latlo lathi).status == 0 && (make lonlo lonhi).status == 0 &&
      (make hlo hhi).status == 0) = true
  · simp only [h1, ite_true] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨ha, hb⟩, hc⟩ := h1
    generalize hr : cartesianI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi (make latlo lathi)
      (make lonlo lonhi) (make hlo hhi) = r at h ⊢
    by_cases h2 : (r.1.status == 0 && r.2.1.status == 0 && r.2.2.status == 0) = true
    · simp only [h2, ite_true] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨r1, r2⟩, r3⟩ := h2
      intro φ lon hh hφ hl hh'
      have rel := cartesian.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi)
        (fun _ => contains_make ha hφ) (fun _ => contains_make hb hl) (fun _ => contains_make hc hh')
      rw [hr, cartesian_eq] at rel
      exact ⟨rel.1 r1, rel.2.1 r2, rel.2.2 r3⟩
    · simp only [h2, Bool.false_eq_true, ite_false, noVec] at h
      exact absurd h (by decide)
  · simp only [h1, Bool.false_eq_true, ite_false, noVec] at h
    exact absurd h (by decide)

/-- The interval of `widen e r s` contains `x` when `r` encloses a residual `ρ`, `s` a slope bound
`σ`, and `x` lies within `|ρ|/σ` of the value of `e` for `σ > 0`. -/
theorem widen_encloses {e : Float} {r s : Interval} {ρ σ x : ℝ} (hr : Encloses r ρ)
    (hs : Encloses s σ) (hb : 0 < σ → |value e.toBits - x| ≤ |ρ| / σ) :
    Encloses (widen e r s) x := by
  intro h
  unfold widen at h ⊢
  have hbound := encloses_div (encloses_abs hr) hs
  by_cases hb0 : ((div (abs r) s).status == 0) = true
  · by_cases hs0 : 0 < s.lo
    · simp only [hb0, hs0, ite_true] at h ⊢
      obtain ⟨se, sm, hc⟩ := add_sound h
      obtain ⟨-, -, -, hmk⟩ := make_sound sm
      have cB := hbound (beq_iff_eq.mp hb0)
      obtain ⟨-, sS, -⟩ := div_sound (beq_iff_eq.mp hb0)
      have spos : 0 < σ := (hs sS).pos_of_lo hs0
      have habs := abs_le.mp ((hb spos).trans cB.2.2.2.2)
      obtain ⟨-, vn⟩ := neg_value cB.2.2.1
      have he : Encloses (point e) (value e.toBits) := fun h => (point_sound h).2
      have hr' := hc (value e.toBits) (x - value e.toBits) (he se)
        (hmk _ (by rw [vn]; linarith [habs.2]) (by linarith [habs.1]))
      rwa [add_sub_cancel] at hr'
    · simp only [hb0, hs0, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hb0, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- `g` holds in its intervals a latitude and a height whose position lies at the distance `p`
from the polar axis and at the height `z`, for every longitude. -/
def LatHeight (g : Coords) (p z : ℝ) : Prop :=
  ∃ φ hh, Contains g.lat φ ∧ Contains g.h hh ∧ |φ| < π / 2 ∧ 0 < Model.radius φ + hh ∧
    ∀ lon, Model.position φ lon hh = (p * cos lon, p * sin lon, z)

theorem abs_arctan_lt (u : ℝ) : |arctan u| < π / 2 :=
  abs_lt.2 ⟨neg_pi_div_two_lt_arctan u, arctan_lt_pi_div_two u⟩

/-- An accepted result of `regimeA` shows `p > a e²` and holds a latitude and a height of every
point of its arguments' intervals. -/
theorem regimeA_sound {p z : Interval} (h : (regimeA Trig.invPi Trig.halfPi p z).status = 0)
    {p' z' : ℝ} (hp : Encloses p p') (hz : Encloses z z') (hp0 : 0 < p') :
    Model.a * Model.e2 < p' ∧ LatHeight (regimeA Trig.invPi Trig.halfPi p z) p' z' := by
  unfold regimeA at h ⊢
  have hs : Encloses (slopeAI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi p)
      (p' - Model.a * Model.e2) := slopeA_eq p' ▸ slopeA.encloses hp
  generalize slopeAI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi p = s at h hs ⊢
  by_cases h1 : (s.status == 0) = true
  · by_cases h2 : 0 < s.lo
    · simp only [h1, h2, ite_true] at h ⊢
      have slope : 0 < p' - Model.a * Model.e2 := (hs (beq_iff_eq.mp h1)).pos_of_lo h2
      have grow := fun u₁ u₂ (hu : u₁ ≤ u₂) =>
        Geodetic.growthA Geodetic.c_nonneg Geodetic.m_pos.le p' z' hu
      obtain ⟨u, hu⟩ := (Geodetic.bijective_of_growth slope
        (Geodetic.continuous_kA Geodetic.m_pos.le p' z') grow).2 0
      generalize newtonA (mid p) (mid z) = e at h ⊢
      have he : Encloses (point e) (value e.toBits) := fun h => (point_sound h).2
      have hres := residualA_eq p' z' (value e.toBits) ▸
        residualA.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hp hz he
      have hU := widen_encloses hres hs fun _ =>
        Geodetic.bound_of_growth slope grow hu (value e.toBits)
      have hc := coordsA_eq p' z' u ▸
        coordsA.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hp hz hU
      generalize coordsAI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi p z _ = c at h hc ⊢
      by_cases h3 : (c.1.status == 0 && c.2.status == 0) = true
      · simp only [h3, ite_true]
        simp only [Bool.and_eq_true, beq_iff_eq] at h3
        obtain ⟨hpos, -⟩ := Geodetic.position_of_rootA hp0 hu 0
        exact ⟨by linarith, arctan u, _, hc.1 h3.1, hc.2 h3.2, abs_arctan_lt u, hpos,
          fun lon => (Geodetic.position_of_rootA hp0 hu lon).2⟩
      · simp only [h3, Bool.false_eq_true, ite_false, noCoords] at h
        exact absurd h (by decide)
    · simp only [h1, h2, ite_true, ite_false, noCoords] at h
      exact absurd h (by decide)
  · simp only [h1, Bool.false_eq_true, ite_false, noCoords] at h
    exact absurd h (by decide)

/-- The position of the latitude `−φ` is that of `φ` with `z` negated. -/
theorem position_neg (φ lon hh : ℝ) :
    Model.position (-φ) lon hh = ((Model.position φ lon hh).1, (Model.position φ lon hh).2.1,
      -(Model.position φ lon hh).2.2) := by
  have hr : Model.radius (-φ) = Model.radius φ := by simp only [Model.radius, sin_neg, neg_sq]
  simp only [Model.position, hr, cos_neg, sin_neg, Prod.mk.injEq, true_and]
  ring

theorem radius_neg (φ : ℝ) : Model.radius (-φ) = Model.radius φ := by
  simp only [Model.radius, sin_neg, neg_sq]

/-- The common part of `regimeB` for an interval `w` of positive heights: an accepted slope test
shows `w > a e²/(1 − f)`, and the coordinates enclose the latitude `π/2 − arctan v` and the height
of the root `v` of `ℓ`. -/
theorem coreB {p w : Interval} {p' w' : ℝ} (hp : Encloses p p') (hw : Encloses w w')
    (hp0 : 0 < p') (h1 : (slopeBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi w).status = 0)
    (h2 : 0 < (slopeBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi w).lo) (e : Float) :
    Model.a * Model.e2 / (1 - Model.f) < w' ∧ ∃ v,
      prodRel Encloses Encloses
        (coordsBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi p w
          (widen e (residualBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi p w (point e)) w))
        (π / 2 - arctan v, (p' * v + w' - Model.a * √(v ^ 2 + (1 - Model.e2))) / √(1 + v ^ 2)) ∧
      |π / 2 - arctan v| < π / 2 ∧
      0 < Model.radius (π / 2 - arctan v) +
        (p' * v + w' - Model.a * √(v ^ 2 + (1 - Model.e2))) / √(1 + v ^ 2) ∧
      ∀ lon, Model.position (π / 2 - arctan v) lon
        ((p' * v + w' - Model.a * √(v ^ 2 + (1 - Model.e2))) / √(1 + v ^ 2)) =
          (p' * cos lon, p' * sin lon, w') := by
  have hs : Encloses (slopeBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi w)
      (w' - Model.a * Model.e2 / (1 - Model.f)) := slopeB_eq w' ▸ slopeB.encloses hw
  have excess : 0 < w' - Model.a * Model.e2 / (1 - Model.f) := (hs h1).pos_of_lo h2
  have hcf : 0 ≤ Model.a * Model.e2 / (1 - Model.f) :=
    div_nonneg Geodetic.c_nonneg (by linarith [Geodetic.f_lt_one])
  have hw0 : 0 < w' := by linarith
  have grow := fun v₁ v₂ (hv : v₁ ≤ v₂) =>
    Geodetic.growthB Geodetic.c_nonneg Geodetic.m_pos p' w' hv
  obtain ⟨v, hv⟩ := (Geodetic.bijective_of_growth hw0
    (Geodetic.continuous_lB Geodetic.m_pos p' w') grow).2 0
  have he : Encloses (point e) (value e.toBits) := fun h => (point_sound h).2
  have hres := residualB_eq p' w' (value e.toBits) ▸
    residualB.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hp hw he
  have hV := widen_encloses hres hw fun _ => Geodetic.bound_of_growth hw0 grow hv (value e.toBits)
  have hc := coordsB_eq p' w' v ▸
    coordsB.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hp hw hV
  have vpos := Geodetic.rootB_pos hp0 hw0 hv
  have hφ : |π / 2 - arctan v| < π / 2 := by
    have h0 : 0 < arctan v := by
      have := arctan_strictMono vpos; rwa [arctan_zero] at this
    rw [abs_lt]; constructor <;> linarith [arctan_lt_pi_div_two v, pi_pos]
  exact ⟨by linarith, v, hc, hφ, (Geodetic.position_of_rootB hw0 hv 0).1,
    fun lon => (Geodetic.position_of_rootB hw0 hv lon).2⟩

/-- An accepted result of `regimeB` shows `|z| > a e²/(1 − f)` and holds a latitude and a height
of every point of its arguments' intervals. -/
theorem regimeB_sound {p z : Interval} (h : (regimeB Trig.invPi Trig.halfPi p z).status = 0)
    {p' z' : ℝ} (hp : Encloses p p') (hz : Encloses z z') (hp0 : 0 < p') :
    Model.a * Model.e2 / (1 - Model.f) < |z'| ∧
      LatHeight (regimeB Trig.invPi Trig.halfPi p z) p' z' := by
  unfold regimeB at h ⊢
  by_cases hb : mid z < 0
  · simp only [hb, decide_true, ite_true] at h ⊢
    by_cases h1 : ((slopeBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi (neg z)).status == 0)
        = true
    · by_cases h2 : 0 < (slopeBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi (neg z)).lo
      · simp only [h1, h2, ite_true] at h ⊢
        obtain ⟨hex, v, hc, hφ, hpos, hposn⟩ :=
          coreB hp (encloses_neg hz) hp0 (beq_iff_eq.mp h1) h2 (newtonB (mid p) (mid (neg z)))
        generalize coordsBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi p (neg z) _ = c
          at h hc ⊢
        by_cases h3 : (c.1.status == 0 && c.2.status == 0) = true
        · simp only [h3, ite_true]
          simp only [Bool.and_eq_true, beq_iff_eq] at h3
          have hn : (neg c.1).status = 0 := by simp only [neg, h3.1, beq_self_eq_true, ite_true]
          refine ⟨by rwa [abs_of_neg (by
              have := div_nonneg Geodetic.c_nonneg (by linarith [Geodetic.f_lt_one] :
                (0 : ℝ) ≤ 1 - Model.f)
              linarith)], -(π / 2 - arctan v), _, encloses_neg hc.1 hn, hc.2 h3.2,
            by rwa [abs_neg], by rwa [radius_neg], fun lon => ?_⟩
          rw [position_neg, hposn lon]
          simp only [neg_neg]
        · simp only [h3, Bool.false_eq_true, ite_false, noCoords] at h
          exact absurd h (by decide)
      · simp only [h1, h2, ite_true, ite_false, noCoords] at h
        exact absurd h (by decide)
    · simp only [h1, Bool.false_eq_true, ite_false, noCoords] at h
      exact absurd h (by decide)
  · simp only [hb, decide_false, Bool.false_eq_true, ite_false] at h ⊢
    by_cases h1 : ((slopeBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi z).status == 0) = true
    · by_cases h2 : 0 < (slopeBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi z).lo
      · simp only [h1, h2, ite_true] at h ⊢
        obtain ⟨hex, v, hc, hφ, hpos, hposn⟩ :=
          coreB hp hz hp0 (beq_iff_eq.mp h1) h2 (newtonB (mid p) (mid z))
        generalize coordsBI Trig.invPi Trig.halfPi Trig.invPi Trig.halfPi p z _ = c at h hc ⊢
        by_cases h3 : (c.1.status == 0 && c.2.status == 0) = true
        · simp only [h3, ite_true]
          simp only [Bool.and_eq_true, beq_iff_eq] at h3
          refine ⟨by rwa [abs_of_pos (by
              have := div_nonneg Geodetic.c_nonneg (by linarith [Geodetic.f_lt_one] :
                (0 : ℝ) ≤ 1 - Model.f)
              linarith)], π / 2 - arctan v, _, hc.1 h3.1, hc.2 h3.2, hφ, hpos, hposn⟩
        · simp only [h3, Bool.false_eq_true, ite_false, noCoords] at h
          exact absurd h (by decide)
      · simp only [h1, h2, ite_true, ite_false, noCoords] at h
        exact absurd h (by decide)
    · simp only [h1, Bool.false_eq_true, ite_false, noCoords] at h
      exact absurd h (by decide)

/-- An accepted longitude of a box holds, for every point of the box off the polar axis, an angle
whose cosine and sine times the distance `p` are `x` and `y`. -/
theorem longitude_sound {x y p : Interval}
    (h : (longitude Trig.invPi Trig.halfPi x y p).status = 0) {x' y' : ℝ} (hx : Encloses x x')
    (hy : Encloses y y') (hp : Encloses p (√(x' ^ 2 + y' ^ 2))) (hp0 : 0 < √(x' ^ 2 + y' ^ 2)) :
    ∃ lon, Contains (longitude Trig.invPi Trig.halfPi x y p) lon ∧
      √(x' ^ 2 + y' ^ 2) * cos lon = x' ∧ √(x' ^ 2 + y' ^ 2) * sin lon = y' := by
  unfold longitude at h ⊢
  by_cases hm : 0 ≤ mid x
  · simp only [hm, ite_true] at h ⊢
    have hq := encloses_add hp hx
    generalize add p x = q at h hq ⊢
    by_cases h1 : (q.status == 0 && decide (0 < q.lo)) = true
    · simp only [h1, ite_true] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      have hpos := (hq h1.1).pos_of_lo h1.2
      have hl := lonA.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hy hq h
      exact ⟨_, hl, Geodetic.lonA_spec hp0 hpos⟩
    · simp only [h1, Bool.false_eq_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hm, ite_false] at h ⊢
    have hq := encloses_sub hp hx
    generalize sub p x = q at h hq ⊢
    by_cases h1 : (q.status == 0 && decide (0 < q.lo)) = true
    · simp only [h1, ite_true] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      have hpos := (hq h1.1).pos_of_lo h1.2
      have hl := lonB.encloses (powLog := Trig.invPi) (powExp := Trig.halfPi) hy hq h
      exact ⟨_, hl, Geodetic.lonB_spec hp0 hpos⟩
    · simp only [h1, Bool.false_eq_true, ite_false] at h
      exact absurd h (by decide)

/-- **Cartesian to geodetic.**  Every point of the box of an accepted result of `toGeodetic` lies
in the domain `D` and has geodetic coordinates whose latitude, longitude, and height lie in the
result's intervals. -/
theorem toGeodetic_sound {xlo xhi ylo yhi zlo zhi : Float}
    (h : (toGeodetic xlo xhi ylo yhi zlo zhi).status = 0) :
    ∀ x y z, Within xlo xhi x → Within ylo yhi y → Within zlo zhi z →
      Model.InDomain x y z ∧ -4 ≤ value (toGeodetic xlo xhi ylo yhi zlo zhi).lon.lo.toBits ∧
        value (toGeodetic xlo xhi ylo yhi zlo zhi).lon.hi.toBits ≤ 7 ∧ ∃ φ lon hh,
        Contains (toGeodetic xlo xhi ylo yhi zlo zhi).lat φ ∧
        Contains (toGeodetic xlo xhi ylo yhi zlo zhi).lon lon ∧
        Contains (toGeodetic xlo xhi ylo yhi zlo zhi).h hh ∧ Model.IsGeodetic x y z φ lon hh := by
  intro x' y' z' hx' hy' hz'
  unfold toGeodetic toGeodeticWith at h ⊢
  by_cases h1 : ((make xlo xhi).status == 0 && (make ylo yhi).status == 0 &&
      (make zlo zhi).status == 0) = true
  · simp only [h1, ite_true] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨ha, hb⟩, hc⟩ := h1
    have ex : Encloses (make xlo xhi) x' := fun _ => contains_make ha hx'
    have ey : Encloses (make ylo yhi) y' := fun _ => contains_make hb hy'
    have ez : Encloses (make zlo zhi) z' := fun _ => contains_make hc hz'
    have hp := axis_encloses ex ey
    generalize axisI (make xlo xhi) (make ylo yhi) = p at h hp ⊢
    by_cases h2 : (p.status == 0) = true
    · by_cases h3 : 0 < p.lo
      · simp only [h2, h3, ite_true] at h ⊢
        have hp0 := (hp (beq_iff_eq.mp h2)).pos_of_lo h3
        have hreg : (if mid (abs (make zlo zhi)) ≤ mid p then
              regimeA Trig.invPi Trig.halfPi p (make zlo zhi)
            else regimeB Trig.invPi Trig.halfPi p (make zlo zhi)).status = 0 →
            (Model.a * Model.e2 < √(x' ^ 2 + y' ^ 2) ∨
              Model.a * Model.e2 / (1 - Model.f) < |z'|) ∧
            LatHeight (if mid (abs (make zlo zhi)) ≤ mid p then
              regimeA Trig.invPi Trig.halfPi p (make zlo zhi)
            else regimeB Trig.invPi Trig.halfPi p (make zlo zhi)) (√(x' ^ 2 + y' ^ 2)) z' := by
          split
          · intro hg
            obtain ⟨hA, hlh⟩ := regimeA_sound hg hp ez hp0
            exact ⟨Or.inl hA, hlh⟩
          · intro hg
            obtain ⟨hB, hlh⟩ := regimeB_sound hg hp ez hp0
            exact ⟨Or.inr hB, hlh⟩
        generalize (if mid (abs (make zlo zhi)) ≤ mid p then
            regimeA Trig.invPi Trig.halfPi p (make zlo zhi)
          else regimeB Trig.invPi Trig.halfPi p (make zlo zhi)) = g at h hreg ⊢
        by_cases hg : (g.status == 0) = true
        · simp only [hg, ite_true] at h ⊢
          obtain ⟨hdom, φ, hh, hφ, hhh, habs, hR, hpos⟩ := hreg (beq_iff_eq.mp hg)
          generalize hL : longitude Trig.invPi Trig.halfPi (make xlo xhi) (make ylo yhi) p = L
            at h ⊢
          by_cases h4 : (L.status == 0 && decide ((-4 : Int64).toFloat ≤ L.lo) &&
              decide (L.hi ≤ (7 : Int64).toFloat)) = true
          · simp only [h4, ite_true]
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h4
            obtain ⟨⟨hL0, hlo⟩, hhi⟩ := h4
            obtain ⟨lon, hlon, hcos, hsin⟩ := longitude_sound (by rw [hL]; exact hL0) ex ey hp hp0
            rw [hL] at hlon
            obtain ⟨f4, v4⟩ := Signed64Value.toFloat_exact (-4) (by decide)
            have e4 : (((-4 : Int64).toInt : ℤ) : ℝ) = -4 := by
              have : (-4 : Int64).toInt = -4 := by decide
              rw [this]; norm_num
            obtain ⟨-, -, f7, v7⟩ := range_values
            refine ⟨⟨hp0, hdom⟩, ?_, ?_, φ, lon, hh, hφ, hlon, hhh, habs, hR, ?_⟩
            · have := (le_iff_value f4 hlon.2.1).mp hlo; rwa [v4, e4] at this
            · have := (le_iff_value hlon.2.2.1 f7).mp hhi; rwa [v7] at this
            · rw [hpos lon, hcos, hsin]
          · simp only [h4, Bool.false_eq_true, ite_false, noCoords] at h
            exact absurd h (by decide)
        · simp only [hg, Bool.false_eq_true, ite_false] at h
          exact absurd (beq_iff_eq.mpr h) hg
      · simp only [h2, h3, ite_true, ite_false, noCoords] at h
        exact absurd h (by decide)
    · simp only [h2, Bool.false_eq_true, ite_false, noCoords] at h
      exact absurd h (by decide)
  · simp only [h1, Bool.false_eq_true, ite_false, noCoords] at h
    exact absurd h (by decide)

end Demos.Frames
