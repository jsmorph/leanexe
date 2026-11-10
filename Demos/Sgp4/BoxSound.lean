import Demos.Sgp4.Box
import Demos.Sgp4.Model

/-!
Soundness of the enclosing SGP4 program.  For intervals that contain an element set and a time,
`sgp4Box_sound` states that the intervals of a result with status 0 or 6 contain the model's
position and velocity, and `status_sound` states that a status of 0, 1, 2, 4, 6, or 8 is the
model's status.
-/

namespace Demos.Sgp4

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

/-! ### The two status functions -/

theorem initStatus_values (n e deep no : Interval) :
    initStatus n e deep no = 0 ∨ initStatus n e deep no = 2 ∨ initStatus n e deep no = 7 ∨
      initStatus n e deep no = 8 ∨ initStatus n e deep no = 9 := by
  unfold initStatus
  split_ifs <;> simp

theorem stateStatus_values (e1 e2 pl m6 : Interval) (ok : Bool) :
    stateStatus e1 e2 pl m6 ok = 0 ∨ stateStatus e1 e2 pl m6 ok = 1 ∨
      stateStatus e1 e2 pl m6 ok = 4 ∨ stateStatus e1 e2 pl m6 ok = 6 ∨
      stateStatus e1 e2 pl m6 ok = 7 := by
  unfold stateStatus
  split_ifs <;> simp

theorem initStatus_sound {n e deep no : Interval} {n' e' d' no' : ℝ}
    (hn : Encloses n n') (he : Encloses e e') (hd : Encloses deep d') (hno : Encloses no no') :
    (initStatus n e deep no = 0 → (0 < n' ∧ 0 ≤ e' ∧ e' < 1) ∧ d' < 0 ∧ 0 < no') ∧
    (initStatus n e deep no = 8 → (0 < n' ∧ 0 ≤ e' ∧ e' < 1) ∧ 0 ≤ d') ∧
    (initStatus n e deep no = 2 → (0 < n' ∧ 0 ≤ e' ∧ e' < 1) ∧ d' < 0 ∧ no' ≤ 0) := by
  unfold initStatus
  by_cases h1 : (n.status == 0 && e.status == 0) = true
  · simp only [h1, ite_true]
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    have cn := hn h1.1
    have ce := he h1.2
    by_cases h2 : 0 < n.lo ∧ 0 ≤ e.lo ∧ e.hi < 1.0
    · simp only [h2, and_self, ite_true]
      have v : 0 < n' ∧ 0 ≤ e' ∧ e' < 1 :=
        ⟨cn.pos_of_lo h2.1, ce.nonneg_of_lo h2.2.1, ce.lt_one_of_hi h2.2.2⟩
      by_cases h3 : (deep.status == 0 && no.status == 0) = true
      · simp only [h3, ite_true]
        simp only [Bool.and_eq_true, beq_iff_eq] at h3
        have cd := hd h3.1
        have cno := hno h3.2
        by_cases h4 : 0 ≤ deep.lo
        · simp only [h4, ite_true]
          exact ⟨fun h => absurd h (by decide), fun _ => ⟨v, cd.nonneg_of_lo h4⟩,
            fun h => absurd h (by decide)⟩
        · simp only [h4, ite_false]
          by_cases h5 : deep.hi < 0
          · simp only [h5, ite_true]
            by_cases h6 : 0 < no.lo
            · simp only [h6, ite_true]
              exact ⟨fun _ => ⟨v, cd.neg_of_hi h5, cno.pos_of_lo h6⟩,
                fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
            · simp only [h6, ite_false]
              by_cases h7 : no.hi ≤ 0
              · simp only [h7, ite_true]
                exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
                  fun _ => ⟨v, cd.neg_of_hi h5, cno.nonpos_of_hi h7⟩⟩
              · simp only [h7, ite_false]
                refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
          · simp only [h5, ite_false]
            refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
      · simp only [h3, Bool.false_eq_true, ite_false]
        refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
    · simp only [h2, ite_false]
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
  · simp only [h1, Bool.false_eq_true, ite_false]
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)

theorem stateStatus_sound {e1 e2 pl m6 : Interval} {ok : Bool} {em pl' mrt : ℝ}
    (h1 : Encloses e1 (em - 1)) (h2 : Encloses e2 (em + 0.001)) (hp : Encloses pl pl')
    (hm : Encloses m6 (mrt - 1)) :
    (stateStatus e1 e2 pl m6 ok = 1 → 1 ≤ em ∨ em < -0.001) ∧
    (stateStatus e1 e2 pl m6 ok = 4 → ¬(1 ≤ em ∨ em < -0.001) ∧ pl' < 0) ∧
    (stateStatus e1 e2 pl m6 ok = 6 →
      ¬(1 ≤ em ∨ em < -0.001) ∧ ¬pl' < 0 ∧ mrt < 1 ∧ ok = true) ∧
    (stateStatus e1 e2 pl m6 ok = 0 →
      ¬(1 ≤ em ∨ em < -0.001) ∧ ¬pl' < 0 ∧ ¬mrt < 1 ∧ ok = true) := by
  unfold stateStatus
  by_cases a : (e1.status == 0 && e2.status == 0) = true
  · simp only [a, ite_true]
    simp only [Bool.and_eq_true, beq_iff_eq] at a
    have c1 := h1 a.1
    have c2 := h2 a.2
    by_cases b : 0 ≤ e1.lo ∨ e2.hi < 0
    · simp only [b, ite_true]
      refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun h => absurd h (by decide),
        fun h => absurd h (by decide)⟩
      rcases b with b | b
      · exact Or.inl (by linarith [c1.nonneg_of_lo b])
      · exact Or.inr (by linarith [c2.neg_of_hi b])
    · simp only [b, ite_false]
      by_cases c : e1.hi < 0 ∧ 0 ≤ e2.lo
      · simp only [c, and_self, ite_true]
        have ne : ¬(1 ≤ em ∨ em < -0.001) := by
          have u1 := c1.neg_of_hi c.1
          have u2 := c2.nonneg_of_lo c.2
          intro h
          rcases h with h | h <;> linarith
        by_cases d : (pl.status == 0) = true
        · simp only [d, ite_true]
          have cp := hp (beq_iff_eq.mp d)
          by_cases e : pl.hi < 0
          · simp only [e, ite_true]
            exact ⟨fun h => absurd h (by decide), fun _ => ⟨ne, cp.neg_of_hi e⟩,
              fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
          · simp only [e, ite_false]
            by_cases f : 0 ≤ pl.lo
            · simp only [f, ite_true]
              have np : ¬pl' < 0 := not_lt.mpr (cp.nonneg_of_lo f)
              by_cases g : (m6.status == 0 && ok) = true
              · simp only [g, ite_true]
                simp only [Bool.and_eq_true, beq_iff_eq] at g
                have cm := hm g.1
                by_cases i : m6.hi < 0
                · simp only [i, ite_true]
                  exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
                    fun _ => ⟨ne, np, by linarith [cm.neg_of_hi i], g.2⟩,
                    fun h => absurd h (by decide)⟩
                · simp only [i, ite_false]
                  by_cases j : 0 ≤ m6.lo
                  · simp only [j, ite_true]
                    exact ⟨fun h => absurd h (by decide), fun h => absurd h (by decide),
                      fun h => absurd h (by decide),
                      fun _ => ⟨ne, np, by linarith [cm.nonneg_of_lo j], g.2⟩⟩
                  · simp only [j, ite_false]
                    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
              · simp only [g, Bool.false_eq_true, ite_false]
                refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
            · simp only [f, ite_false]
              refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
        · simp only [d, Bool.false_eq_true, ite_false]
          refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
      · simp only [c, ite_false]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
  · simp only [a, Bool.false_eq_true, ite_false]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)

/-! ### The model's status from its tests -/

namespace Model

theorem status_deep {el : Elements} {t : ℝ} (hv : Valid el) (hp : 225 ≤ period el) :
    status el t = 8 := by
  simp [status, hv, hp]

theorem status_motion {el : Elements} {t : ℝ} (hv : Valid el) (hp : period el < 225)
    (hn : meanMotion el ≤ 0) : status el t = 2 := by
  simp [status, hv, not_le.mpr hp, hn]

theorem status_eccentricity {el : Elements} {t : ℝ} (hv : Valid el) (hp : period el < 225)
    (hn : 0 < meanMotion el) (he : 1 ≤ eccentricity el t ∨ eccentricity el t < -0.001) :
    status el t = 1 := by
  simp only [status, not_not.mpr hv, not_le.mpr hp, not_le.mpr hn, he, ite_true, ite_false]

theorem status_semilatus {el : Elements} {t : ℝ} (hv : Valid el) (hp : period el < 225)
    (hn : 0 < meanMotion el) (he : ¬(1 ≤ eccentricity el t ∨ eccentricity el t < -0.001))
    (hl : semilatus el t < 0) : status el t = 4 := by
  simp only [status, not_not.mpr hv, not_le.mpr hp, not_le.mpr hn, he, hl, ite_true, ite_false]

theorem status_radius {el : Elements} {t : ℝ} (hv : Valid el) (hp : period el < 225)
    (hn : 0 < meanMotion el) (he : ¬(1 ≤ eccentricity el t ∨ eccentricity el t < -0.001))
    (hl : ¬semilatus el t < 0) (hr : radius el t < 1) : status el t = 6 := by
  simp only [status, not_not.mpr hv, not_le.mpr hp, not_le.mpr hn, he, hl, hr, ite_true,
    ite_false]

theorem status_none {el : Elements} {t : ℝ} (hv : Valid el) (hp : period el < 225)
    (hn : 0 < meanMotion el) (he : ¬(1 ≤ eccentricity el t ∨ eccentricity el t < -0.001))
    (hl : ¬semilatus el t < 0) (hr : ¬radius el t < 1) : status el t = 0 := by
  simp only [status, not_not.mpr hv, not_le.mpr hp, not_le.mpr hn, he, hl, hr, ite_false]

end Model

/-! ### The program -/

/-- The intervals of an element set contain it. -/
def Input (n e incl node argp m bstar : Interval) (el : Model.Elements) : Prop :=
  Encloses n el.n ∧ Encloses e el.e ∧ Encloses incl el.incl ∧ Encloses node el.node ∧
    Encloses argp el.argp ∧ Encloses m el.m ∧ Encloses bstar el.bstar

/-- The intervals of a result contain the model's position and velocity. -/
def Inside (b : Box) (el : Model.Elements) (t : ℝ) : Prop :=
  Contains b.x (Model.position el t).1 ∧ Contains b.y (Model.position el t).2.1 ∧
    Contains b.z (Model.position el t).2.2 ∧ Contains b.vx (Model.velocity el t).1 ∧
    Contains b.vy (Model.velocity el t).2.1 ∧ Contains b.vz (Model.velocity el t).2.2

variable {logTab expTab : Array UInt64} {n e incl node argp m bstar t : Interval}
  {el : Model.Elements} {t' : ℝ}

theorem init_constants (hi : Input n e incl node argp m bstar el) :
    (enclosure_relation% 35)
      (initBoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar).2
      (Model.constants el) :=
  Spec.wgs72.encloses hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2.1 hi.2.2.2.2.2.2

theorem init_status (hi : Input n e incl node argp m bstar el) :
    ((initBoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar).1 = 0 →
      Model.Valid el ∧ Model.period el < 225 ∧ 0 < Model.meanMotion el) ∧
    ((initBoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar).1 = 8 →
      Model.Valid el ∧ 225 ≤ Model.period el) ∧
    ((initBoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar).1 = 2 →
      Model.Valid el ∧ Model.period el < 225 ∧ Model.meanMotion el ≤ 0) := by
  have hc := init_constants (logTab := logTab) (expTab := expTab) hi
  have limit : Encloses (ofInt 225) (225 : ℝ) :=
    encloses_ofInt' (m := 225) (by decide +kernel) (by decide +kernel) (by norm_num)
  obtain ⟨a, b, c⟩ := initStatus_sound hi.1 hi.2.1 (encloses_sub hc.1 limit) hc.2.1
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨v, d, p⟩ := a h
    exact ⟨v, by unfold Model.period; linarith, p⟩
  · obtain ⟨v, d⟩ := b h
    exact ⟨v, by unfold Model.period; linarith⟩
  · obtain ⟨v, d, p⟩ := c h
    exact ⟨v, by unfold Model.period; linarith, p⟩

/-- What each status of a result implies. -/
theorem box_cases (hi : Input n e incl node argp m bstar el) (ht : Encloses t t') {b : Box}
    (hbox : b = sgp4BoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar t) :
    (b.status = 8 → Model.Valid el ∧ 225 ≤ Model.period el) ∧
    (b.status = 2 → Model.Valid el ∧ Model.period el < 225 ∧ Model.meanMotion el ≤ 0) ∧
    (b.status = 1 → Model.Valid el ∧ Model.period el < 225 ∧ 0 < Model.meanMotion el ∧
      (1 ≤ Model.eccentricity el t' ∨ Model.eccentricity el t' < -0.001)) ∧
    (b.status = 4 → Model.Valid el ∧ Model.period el < 225 ∧ 0 < Model.meanMotion el ∧
      ¬(1 ≤ Model.eccentricity el t' ∨ Model.eccentricity el t' < -0.001) ∧
      Model.semilatus el t' < 0) ∧
    (b.status = 6 → Model.Valid el ∧ Model.period el < 225 ∧ 0 < Model.meanMotion el ∧
      ¬(1 ≤ Model.eccentricity el t' ∨ Model.eccentricity el t' < -0.001) ∧
      ¬Model.semilatus el t' < 0 ∧ Model.radius el t' < 1 ∧ Inside b el t') ∧
    (b.status = 0 → Model.Valid el ∧ Model.period el < 225 ∧ 0 < Model.meanMotion el ∧
      ¬(1 ≤ Model.eccentricity el t' ∨ Model.eccentricity el t' < -0.001) ∧
      ¬Model.semilatus el t' < 0 ∧ ¬Model.radius el t' < 1 ∧ Inside b el t') := by
  have hc := init_constants (logTab := logTab) (expTab := expTab) hi
  have hinit := init_status (logTab := logTab) (expTab := expTab) hi
  have hval : ∀ k : UInt64,
      (initBoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar).1 = k →
      k = 0 ∨ k = 2 ∨ k = 7 ∨ k = 8 ∨ k = 9 := fun k hk => by
    rw [← hk]
    exact initStatus_values _ _ _ _
  simp only [sgp4BoxWith, propagateBoxWith] at hbox
  generalize initBoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar = r
    at hc hinit hval hbox
  by_cases h0 : (r.1 == 0) = true
  · simp only [h0, ite_true] at hbox
    obtain ⟨hv, hp, hn⟩ := hinit.1 (beq_iff_eq.mp h0)
    have hs := Spec.wgs72State.encloses (powLog := logTab) (powExp := expTab) ht hc
    generalize Spec.wgs72StateI Trig.invPi Trig.halfPi logTab expTab t r.2 = s
      at hs hbox
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9⟩ := hs
    have one : Encloses (ofInt 1) (1 : ℝ) :=
      encloses_ofInt' (m := 1) (by decide +kernel) (by decide +kernel) (by norm_num)
    have milli : Encloses (ratio 1 1000) (0.001 : ℝ) :=
      encloses_ratio' (m := 1) (k := 1000) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by norm_num)
    generalize hok : (s.2.2.2.1.status == 0 && s.2.2.2.2.1.status == 0 &&
      s.2.2.2.2.2.1.status == 0 && s.2.2.2.2.2.2.1.status == 0 &&
      s.2.2.2.2.2.2.2.1.status == 0 && s.2.2.2.2.2.2.2.2.status == 0) = ok at hbox
    have facts := stateStatus_sound (ok := ok) (encloses_sub s1 one) (encloses_add s1 milli) s2
      (encloses_sub s3 one)
    have sval := stateStatus_values (sub s.1 (ofInt 1)) (add s.1 (ratio 1 1000)) s.2.1
      (sub s.2.2.1 (ofInt 1)) ok
    generalize stateStatus (sub s.1 (ofInt 1)) (add s.1 (ratio 1 1000)) s.2.1
      (sub s.2.2.1 (ofInt 1)) ok = st at facts sval hbox
    have inside : ok = true → b.x = s.2.2.2.1 → b.y = s.2.2.2.2.1 → b.z = s.2.2.2.2.2.1 →
        b.vx = s.2.2.2.2.2.2.1 → b.vy = s.2.2.2.2.2.2.2.1 → b.vz = s.2.2.2.2.2.2.2.2 →
        Inside b el t' := fun hk e1 e2 e3 e4 e5 e6 => by
      rw [← hok] at hk
      simp only [Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨⟨⟨⟨⟨k1, k2⟩, k3⟩, k4⟩, k5⟩, k6⟩ := hk
      unfold Inside
      rw [e1, e2, e3, e4, e5, e6]
      exact ⟨s4 k1, s5 k2, s6 k3, s7 k4, s8 k5, s9 k6⟩
    by_cases h6 : (st == 0 || st == 6) = true
    · simp only [h6, ite_true] at hbox
      have bs : b.status = st := by rw [hbox]
      have h06 : st = 0 ∨ st = 6 := by simpa [Bool.or_eq_true, beq_iff_eq] using h6
      have ins : ok = true → Inside b el t' := fun hk =>
        inside hk (by rw [hbox]) (by rw [hbox]) (by rw [hbox]) (by rw [hbox]) (by rw [hbox])
          (by rw [hbox])
      rw [bs]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rcases h06 with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
      · rcases h06 with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
      · rcases h06 with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
      · rcases h06 with h' | h' <;> rw [h'] at h <;> exact absurd h (by decide)
      · obtain ⟨f1, f2, f3, f4⟩ := facts.2.2.1 h
        exact ⟨hv, hp, hn, f1, f2, f3, ins f4⟩
      · obtain ⟨f1, f2, f3, f4⟩ := facts.2.2.2 h
        exact ⟨hv, hp, hn, f1, f2, f3, ins f4⟩
    · simp only [h6, Bool.false_eq_true, ite_false] at hbox
      have bs : b.status = st := by rw [hbox]; rfl
      have n06 : ¬st = 0 ∧ ¬st = 6 := by
        simpa [Bool.or_eq_true, beq_iff_eq, not_or] using h6
      rw [bs]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · rcases sval with v | v | v | v | v <;> rw [v] at h <;> exact absurd h (by decide)
      · rcases sval with v | v | v | v | v <;> rw [v] at h <;> exact absurd h (by decide)
      · exact ⟨hv, hp, hn, facts.1 h⟩
      · obtain ⟨f1, f2⟩ := facts.2.1 h
        exact ⟨hv, hp, hn, f1, f2⟩
      · exact absurd h n06.2
      · exact absurd h n06.1
  · simp only [h0, Bool.false_eq_true, ite_false] at hbox
    have bs : b.status = r.1 := by rw [hbox]; rfl
    have r0 : ¬r.1 = 0 := fun h => h0 (beq_iff_eq.mpr h)
    have vals := hval r.1 rfl
    rw [bs]
    refine ⟨hinit.2.1, hinit.2.2, fun h => ?_, fun h => ?_, fun h => ?_, fun h => absurd h r0⟩
    · rcases vals with v | v | v | v | v <;> rw [v] at h <;> exact absurd h (by decide)
    · rcases vals with v | v | v | v | v <;> rw [v] at h <;> exact absurd h (by decide)
    · rcases vals with v | v | v | v | v <;> rw [v] at h <;> exact absurd h (by decide)

/-- **`sgp4Box_sound`.**  For intervals that contain an element set and a time, the intervals of
a result with status 0 or 6 contain the model's position and velocity. -/
theorem sgp4Box_sound (hi : Input n e incl node argp m bstar el) (ht : Encloses t t')
    (hs : (sgp4BoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar t).status
        = 0 ∨
      (sgp4BoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar t).status
        = 6) :
    Inside (sgp4BoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar t) el
      t' := by
  obtain ⟨-, -, -, -, c6, c0⟩ := box_cases hi ht rfl
  rcases hs with h | h
  · exact (c0 h).2.2.2.2.2.2
  · exact (c6 h).2.2.2.2.2.2

/-- **`status_sound`.**  For intervals that contain an element set and a time, a status of 0, 1,
2, 4, 6, or 8 is the status of the model. -/
theorem status_sound (hi : Input n e incl node argp m bstar el) (ht : Encloses t t') {k : UInt64}
    (hk : (sgp4BoxWith Trig.invPi Trig.halfPi logTab expTab n e incl node argp m bstar t).status
      = k)
    (hs : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8) : Model.status el t' = k := by
  obtain ⟨c8, c2, c1, c4, c6, c0⟩ := box_cases hi ht rfl
  rw [hk] at c8 c2 c1 c4 c6 c0
  rcases hs with v | v | v | v | v | v
  · obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := c0 v
    rw [v]; exact Model.status_none a1 a2 a3 a4 a5 a6
  · obtain ⟨a1, a2, a3, a4⟩ := c1 v
    rw [v]; exact Model.status_eccentricity a1 a2 a3 a4
  · obtain ⟨a1, a2, a3⟩ := c2 v
    rw [v]; exact Model.status_motion a1 a2 a3
  · obtain ⟨a1, a2, a3, a4, a5⟩ := c4 v
    rw [v]; exact Model.status_semilatus a1 a2 a3 a4 a5
  · obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := c6 v
    rw [v]; exact Model.status_radius a1 a2 a3 a4 a5 a6
  · obtain ⟨a1, a2⟩ := c8 v
    rw [v]; exact Model.status_deep a1 a2

end Demos.Sgp4
