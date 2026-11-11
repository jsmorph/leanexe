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

end Demos.Frames
