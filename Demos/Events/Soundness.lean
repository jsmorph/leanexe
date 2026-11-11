import Demos.Events.Isolation

/-!
The theorems of `events` over its input array.  `Condition xs t` is the event's condition at
`t` minutes for the Kepler trajectory of the input.  For a valid input, `events_cover` states
that every time of the window at which the condition holds lies in a returned run (E1),
`events_holds` that the condition holds at every time of a run labeled 1 (E2), `events_within`
that every run lies in the window (E3), `events_near` the first two for the shadow of every
trajectory within the padding of the Kepler trajectory (E4), and `events_crossing` that every
crossing lies in a run and is an end of every run labeled 1 that holds it (E5).
`events_invalid` states that status 2 marks the inputs that `valid` rejects.
-/

namespace Demos.Events

open LeanExe.ProofKit LeanExe.Dialect Library.Numerics.Bounds Library.Numerics.Interval
open Library.Numerics.Float64 Demos.Screening
open CodeLib.IEEE64 (value Finite)

/-! ### The model of an input -/

/-- The orbit of an input's elements. -/
noncomputable def orbitOfInput (xs : Array Float) : Orbit :=
  orbitOf (rd xs 1) (rd xs 2) (rd xs 3) (rd xs 4) (rd xs 5) (rd xs 6) (rd xs 7)

/-- The gravitational parameter of an input. -/
noncomputable def muOf (xs : Array Float) : ℝ := val (rd xs 8)

/-- The position of the Kepler trajectory of an input at `t` minutes. -/
noncomputable def positionOf (xs : Array Float) (t : ℝ) : V3 :=
  (orbitOfInput xs).position (muOf xs) t

/-- The Sun's direction at `t` minutes, for minute 0 at the input's day. -/
noncomputable abbrev sunOf (xs : Array Float) (t : ℝ) : V3 := sunAt (val (rd xs 9)) t

/-- The vector `b` of an input. -/
noncomputable def vecOf (xs : Array Float) : V3 := (val (rd xs 16), val (rd xs 17), val (rd xs 18))

/-- The condition of the input's event at `t` minutes: the shadow of the cone of half-angle
`α` for event 1, and `b` within `β` of the Sun for events 2 and 3, fixed in the inertial frame
or in the orbit's radial, along-track, and cross-track frame. -/
def Condition (xs : Array Float) (t : ℝ) : Prop :=
  if rd xs 12 == 1.0 then
    InShadow (val (rd xs 13)) (val (rd xs 14)) (positionOf xs t) (sunOf xs t)
  else if rd xs 12 == 2.0 then Within (vecOf xs) (sunOf xs t) (val (rd xs 13))
  else Within (rsw (muOf xs) (orbitOfInput xs) (vecOf xs) t) (sunOf xs t) (val (rd xs 13))

/-- A crossing of a condition in the window `[t0, t1]`: a time of the window with times of the
window arbitrarily close to it at which the condition holds and at which it fails. -/
def Crossing (C : ℝ → Prop) (t0 t1 c : ℝ) : Prop :=
  t0 ≤ c ∧ c ≤ t1 ∧ ∀ ε > 0, (∃ t, t0 ≤ t ∧ t ≤ t1 ∧ |t - c| < ε ∧ C t) ∧
    (∃ t, t0 ≤ t ∧ t ≤ t1 ∧ |t - c| < ε ∧ ¬ C t)

/-! ### The facts of a valid input -/

/-- The facts that `valid` establishes. -/
structure Facts (xs : Array Float) : Prop where
  orbit : (orbitOfInput xs).Valid
  t0 : Finite (rd xs 10).toBits
  t1 : Finite (rd xs 11).toBits
  cap : (rd xs 20).toUInt64.toNat ≤ 1048576
  pad : (rd xs 12 == 1.0) = true → 0 ≤ val (rd xs 15)

theorem valid_facts {xs : Array Float} (h : valid xs = true) : Facts xs := by
  simp only [valid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsz, hfin⟩, -⟩, ha⟩, he0⟩, he1⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hev⟩, -⟩,
    hc⟩ := h
  have fin := allFinite_spec hfin
  rw [hsz] at fin
  have f : ∀ i < 21, Finite (rd xs (UInt64.ofNat i)).toBits := fun i hi => fin i (by simpa using hi)
  simp only [isWhole, Bool.and_eq_true, decide_eq_true_eq] at hc
  have u1 : ∀ x : UInt64, x ≤ 1048576 → x.toNat ≤ 1048576 := fun x hx => by
    have := UInt64.le_iff_toNat_le.mp hx
    simpa using this
  refine ⟨⟨pos_of_lt (f 1 (by norm_num)) ha, nonneg_of_le (f 2 (by norm_num)) he0,
      lt_one_of_lt (f 2 (by norm_num)) he1⟩, f 10 (by norm_num), f 11 (by norm_num), u1 _ hc.2,
    fun h1 => ?_⟩
  unfold eventOk at hev
  rw [if_pos h1] at hev
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hev
  exact nonneg_of_le (f 15 (by norm_num)) hev.2

/-! ### The real side of each event -/

/-! ### The functions of an event at a time -/

section Parts

variable {ev : Ev} {mu : ℝ} {orb : Orbit} {d0 ca sa R nb : ℝ}

theorem sunDir_encl (hd : Encloses ev.d0 d0) (m : Float) :
    let s := Spec.sunDirI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi ev.d0 (point m)
    Encloses s.1 (sunAt d0 (val m)).1 ∧ Encloses s.2.1 (sunAt d0 (val m)).2.1 ∧
      Encloses s.2.2 (sunAt d0 (val m)).2.2 :=
  Spec.sunDir.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) hd (encloses_point m)

theorem partsAt_shadow (hc : ev.code = 1) (ho : Encl ev.o mu orb) (hd : Encloses ev.d0 d0)
    (hca : Encloses ev.ca ca) (hsa : Encloses ev.sa sa) (hR : Encloses ev.radius R) (m : Float) :
    Encloses (partsAt Trig.invPi Trig.halfPi ev m).1
        (dot (orb.position mu (val m)) (sunAt d0 (val m))) ∧
      Encloses (partsAt Trig.invPi Trig.halfPi ev m).2
        (shadowG2 ca sa R (orb.position mu (val m)) (sunAt d0 (val m))) := by
  have r := positionAt_encl ho m
  have s := sunDir_encl hd m
  have e := Spec.shadowParts.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) r.1 r.2.1
    r.2.2 s.1 s.2.1 s.2.2 hca hsa hR
  rw [Spec.shadowParts_eq] at e
  unfold partsAt
  simp only [hc, beq_self_eq_true, ite_true]
  exact e

theorem partsAt_inertial (hc : ev.code = 2) (hd : Encloses ev.d0 d0) (hca : Encloses ev.ca ca)
    (hnb : Encloses ev.nb nb) {b : V3} (h1 : Encloses ev.b1 b.1) (h2 : Encloses ev.b2 b.2.1)
    (h3 : Encloses ev.b3 b.2.2) (m : Float) :
    Encloses (partsAt Trig.invPi Trig.halfPi ev m).1 (vectorG nb ca b (sunAt d0 (val m))) ∧
      Encloses (partsAt Trig.invPi Trig.halfPi ev m).2 (vectorG nb ca b (sunAt d0 (val m))) := by
  have s := sunDir_encl hd m
  have e := Spec.vectorPart.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) hnb hca h1 h2
    h3 s.1 s.2.1 s.2.2
  rw [Spec.vectorPart_eq] at e
  unfold partsAt
  simp only [hc]
  exact ⟨e, e⟩

theorem partsAt_rsw (hc : ev.code = 3) (ho : Encl ev.o mu orb) (hd : Encloses ev.d0 d0)
    (hca : Encloses ev.ca ca) (hnb : Encloses ev.nb nb) {b : V3} (h1 : Encloses ev.b1 b.1)
    (h2 : Encloses ev.b2 b.2.1) (h3 : Encloses ev.b3 b.2.2) (m : Float) :
    Encloses (partsAt Trig.invPi Trig.halfPi ev m).1
        (vectorG nb ca (rsw mu orb b (val m)) (sunAt d0 (val m))) ∧
      Encloses (partsAt Trig.invPi Trig.halfPi ev m).2
        (vectorG nb ca (rsw mu orb b (val m)) (sunAt d0 (val m))) := by
  have r := positionAt_encl ho m
  have s := sunDir_encl hd m
  have v := Spec.rswVec.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) r.1 r.2.1 r.2.2
    ho.px ho.py ho.pz ho.qx ho.qy ho.qz h1 h2 h3
  rw [Spec.rswVec_eq] at v
  have e := Spec.vectorPart.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) hnb hca v.1
    v.2.1 v.2.2 s.1 s.2.1 s.2.2
  rw [Spec.vectorPart_eq] at e
  unfold partsAt
  simp only [hc]
  exact ⟨e, e⟩

end Parts

/-! ### The real side of each event -/

section Sides

variable {xs : Array Float}

/-- The cosine and sine of the input's angle. -/
noncomputable def cosA (xs : Array Float) : ℝ := Real.cos (rad (val (rd xs 13)))

noncomputable def sinA (xs : Array Float) : ℝ := Real.sin (rad (val (rd xs 13)))

/-- The shadow's functions, rate bounds, and margins. -/
noncomputable def shadowSide (xs : Array Float) : Parts where
  g1 t := dot (positionOf xs t) (sunOf xs t)
  g2 t := shadowG2 (cosA xs) (sinA xs) (val (rd xs 14)) (positionOf xs t) (sunOf xs t)
  L1 := shadowRate (muOf xs) (orbitOfInput xs)
  L2 := (|cosA xs| + |sinA xs|) * shadowRate (muOf xs) (orbitOfInput xs)
  W1 := val (rd xs 15)
  W2 := (|cosA xs| + |sinA xs|) * val (rd xs 15)

/-- The inertial vector's function and rate bound, used for both parts. -/
noncomputable def inertialSide (xs : Array Float) : Parts where
  g1 t := vectorG (norm3 (vecOf xs)) (cosA xs) (vecOf xs) (sunOf xs t)
  g2 t := vectorG (norm3 (vecOf xs)) (cosA xs) (vecOf xs) (sunOf xs t)
  L1 := norm3 (vecOf xs) * (sunRate / 1440)
  L2 := norm3 (vecOf xs) * (sunRate / 1440)
  W1 := 0
  W2 := 0

/-- The function and rate bound of a vector in the orbit's frame, used for both parts. -/
noncomputable def rswSide (xs : Array Float) : Parts where
  g1 t := vectorG (norm3 (vecOf xs)) (cosA xs) (rsw (muOf xs) (orbitOfInput xs) (vecOf xs) t)
    (sunOf xs t)
  g2 t := vectorG (norm3 (vecOf xs)) (cosA xs) (rsw (muOf xs) (orbitOfInput xs) (vecOf xs) t)
    (sunOf xs t)
  L1 := rswRate (muOf xs) (orbitOfInput xs) (vecOf xs)
  L2 := rswRate (muOf xs) (orbitOfInput xs) (vecOf xs)
  W1 := 0
  W2 := 0

/-- The orbit's intervals of an input. -/
def objectOf (xs : Array Float) : Obj :=
  object Trig.invPi Trig.halfPi (rd xs 8) (rd xs 1) (rd xs 2) (rd xs 3) (rd xs 4) (rd xs 5)
    (rd xs 6) (rd xs 7)

/-- The intervals of the input's angle. -/
def angleOf (xs : Array Float) : Interval × Interval :=
  Spec.angleI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point (rd xs 13))

/-- The interval of the length of `b`. -/
def lengthOf (xs : Array Float) : Interval :=
  Spec.lengthI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (point (rd xs 16)) (point (rd xs 17))
    (point (rd xs 18))

/-- The intervals of the rate bounds. -/
def ratesOf (xs : Array Float) : Interval × Interval × Interval × Interval :=
  Spec.ratesI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (objectOf xs).speed
    (objectOf xs).apogee (objectOf xs).perigee (angleOf xs).1 (angleOf xs).2 (lengthOf xs)
    (point (rd xs 16)) (point (rd xs 17))

/-- The event code that `setup` derives. -/
def codeOf (xs : Array Float) : UInt64 :=
  if rd xs 12 == 1.0 then 1 else if rd xs 12 == 2.0 then 2 else 3

theorem setup_eq : setup Trig.invPi Trig.halfPi xs =
    { code := codeOf xs, o := objectOf xs, d0 := point (rd xs 9), ca := (angleOf xs).1,
      sa := (angleOf xs).2, radius := point (rd xs 14), b1 := point (rd xs 16),
      b2 := point (rd xs 17), b3 := point (rd xs 18), nb := lengthOf xs,
      l1 := if codeOf xs == 1 then (ratesOf xs).1
        else if codeOf xs == 2 then (ratesOf xs).2.2.1 else (ratesOf xs).2.2.2,
      l2 := if codeOf xs == 1 then (ratesOf xs).2.1
        else if codeOf xs == 1 then (ratesOf xs).1
        else if codeOf xs == 2 then (ratesOf xs).2.2.1 else (ratesOf xs).2.2.2,
      w1 := if codeOf xs == 1 then point (rd xs 15) else point 0.0,
      w2 := if codeOf xs == 1 then
          Spec.padI Trig.invPi Trig.halfPi Trig.invPi Trig.invPi (angleOf xs).1 (angleOf xs).2
            (point (rd xs 15))
        else point 0.0 } := rfl

theorem encloses_zero : Encloses (point 0.0) 0 := by
  have := encloses_point (0.0 : Float)
  rwa [val_zero] at this

theorem encl_o : Encl (objectOf xs) (muOf xs) (orbitOfInput xs) := object_encl _ _ _ _ _ _ _ _

theorem encl_angle : Encloses (angleOf xs).1 (cosA xs) ∧ Encloses (angleOf xs).2 (sinA xs) :=
  Spec.angle.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) (encloses_point (rd xs 13))

theorem encl_nb : Encloses (lengthOf xs) (norm3 (vecOf xs)) := by
  have h := Spec.length.encloses (powLog := Trig.invPi) (powExp := Trig.invPi)
    (encloses_point (rd xs 16)) (encloses_point (rd xs 17)) (encloses_point (rd xs 18))
  rw [show Spec.length (val (rd xs 16)) (val (rd xs 17)) (val (rd xs 18)) = norm3 (vecOf xs)
    from Spec.length_eq (vecOf xs)] at h
  exact h

/-- The rate bounds that `setup` computes enclose the model's. -/
theorem encl_rates :
    Encloses (ratesOf xs).1 (shadowRate (muOf xs) (orbitOfInput xs)) ∧
      Encloses (ratesOf xs).2.1 ((|cosA xs| + |sinA xs|) * shadowRate (muOf xs) (orbitOfInput xs)) ∧
      Encloses (ratesOf xs).2.2.1 (norm3 (vecOf xs) * (sunRate / 1440)) ∧
      Encloses (ratesOf xs).2.2.2 (rswRate (muOf xs) (orbitOfInput xs) (vecOf xs)) := by
  have eo := encl_o (xs := xs)
  exact Spec.rates.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) eo.speed eo.apogee
    eo.perigee encl_angle.1 encl_angle.2 encl_nb (encloses_point (rd xs 16))
    (encloses_point (rd xs 17))

theorem field_o : (setup Trig.invPi Trig.halfPi xs).o = objectOf xs := by rw [setup_eq]

theorem field_d0 : Encloses (setup Trig.invPi Trig.halfPi xs).d0 (val (rd xs 9)) := by
  rw [setup_eq]; exact encloses_point _

theorem field_ca : Encloses (setup Trig.invPi Trig.halfPi xs).ca (cosA xs) := by
  rw [setup_eq]; exact encl_angle.1

theorem field_sa : Encloses (setup Trig.invPi Trig.halfPi xs).sa (sinA xs) := by
  rw [setup_eq]; exact encl_angle.2

theorem field_radius : Encloses (setup Trig.invPi Trig.halfPi xs).radius (val (rd xs 14)) := by
  rw [setup_eq]; exact encloses_point _

theorem field_nb : Encloses (setup Trig.invPi Trig.halfPi xs).nb (norm3 (vecOf xs)) := by
  rw [setup_eq]; dsimp only; exact encl_nb

theorem field_b : Encloses (setup Trig.invPi Trig.halfPi xs).b1 (vecOf xs).1 ∧
    Encloses (setup Trig.invPi Trig.halfPi xs).b2 (vecOf xs).2.1 ∧
    Encloses (setup Trig.invPi Trig.halfPi xs).b3 (vecOf xs).2.2 := by
  rw [setup_eq]; exact ⟨encloses_point _, encloses_point _, encloses_point _⟩

theorem encl_obj : Encl (setup Trig.invPi Trig.halfPi xs).o (muOf xs) (orbitOfInput xs) := by
  rw [field_o]; exact encl_o

theorem shadow_sound (F : Facts xs) (h1 : (rd xs 12 == 1.0) = true) :
    Sound (setup Trig.invPi Trig.halfPi xs) (shadowSide xs) := by
  have code : codeOf xs = 1 := by simp only [codeOf, h1, ite_true]
  have hc : (setup Trig.invPi Trig.halfPi xs).code = 1 := by rw [setup_eq]; exact code
  have ek := encl_rates (xs := xs)
  have hp := partsAt_shadow hc encl_obj field_d0 field_ca field_sa field_radius
  refine ⟨fun m => (hp m).1, fun m => (hp m).2, ?_, ?_, ?_, ?_, shadowRate_nonneg F.orbit,
    mul_nonneg (by positivity) (shadowRate_nonneg F.orbit),
    fun t t' => shadow1_lipschitz F.orbit _ t t', fun t t' => shadow2_lipschitz F.orbit _ _ _ _ t t'⟩
  · rw [setup_eq]; simp only [code, beq_self_eq_true, ite_true]; exact ek.1
  · rw [setup_eq]; simp only [code, beq_self_eq_true, ite_true]; exact ek.2.1
  · rw [setup_eq]; simp only [code, beq_self_eq_true, ite_true]; exact encloses_point _
  · rw [setup_eq]; simp only [code, beq_self_eq_true, ite_true]
    exact Spec.pad.encloses (powLog := Trig.invPi) (powExp := Trig.invPi) encl_angle.1
      encl_angle.2 (encloses_point _)

theorem inertial_sound (h1 : (rd xs 12 == 1.0) = false) (h2 : (rd xs 12 == 2.0) = true) :
    Sound (setup Trig.invPi Trig.halfPi xs) (inertialSide xs) := by
  have code : codeOf xs = 2 := by simp only [codeOf, h1, h2, Bool.false_eq_true, ite_true, ite_false]
  have hc : (setup Trig.invPi Trig.halfPi xs).code = 2 := by rw [setup_eq]; exact code
  have ek := encl_rates (xs := xs)
  have hb := field_b (xs := xs)
  have hp := partsAt_inertial hc field_d0 field_ca field_nb hb.1 hb.2.1 hb.2.2
  have n := mul_nonneg (norm3_nonneg (vecOf xs)) (div_nonneg sunRate_nonneg (by norm_num : (0 : ℝ) ≤ 1440))
  refine ⟨fun m => (hp m).1, fun m => (hp m).2, ?_, ?_, ?_, ?_, n, n,
    fun t t' => inertial_lipschitz _ _ _ t t', fun t t' => inertial_lipschitz _ _ _ t t'⟩
  · rw [setup_eq]; simp only [code]; exact ek.2.2.1
  · rw [setup_eq]; simp only [code]; exact ek.2.2.1
  · rw [setup_eq]; simp only [code]; exact encloses_zero
  · rw [setup_eq]; simp only [code]; exact encloses_zero

theorem rsw_sound (F : Facts xs) (h1 : (rd xs 12 == 1.0) = false)
    (h2 : (rd xs 12 == 2.0) = false) :
    Sound (setup Trig.invPi Trig.halfPi xs) (rswSide xs) := by
  have code : codeOf xs = 3 := by simp only [codeOf, h1, h2, Bool.false_eq_true, ite_false]
  have hc : (setup Trig.invPi Trig.halfPi xs).code = 3 := by rw [setup_eq]; exact code
  have ek := encl_rates (xs := xs)
  have hb := field_b (xs := xs)
  have hp := partsAt_rsw hc encl_obj field_d0 field_ca field_nb hb.1 hb.2.1 hb.2.2
  have n : 0 ≤ rswRate (muOf xs) (orbitOfInput xs) (vecOf xs) := by
    have := speed_nonneg (mu := muOf xs) F.orbit
    have := perigee_pos F.orbit
    have := sunRate_nonneg
    have := norm3_nonneg (vecOf xs)
    unfold rswRate turnRate
    positivity
  refine ⟨fun m => (hp m).1, fun m => (hp m).2, ?_, ?_, ?_, ?_, n, n,
    fun t t' => rsw_lipschitz F.orbit _ _ _ t t', fun t t' => rsw_lipschitz F.orbit _ _ _ t t'⟩
  · rw [setup_eq]; simp only [code]; exact ek.2.2.2
  · rw [setup_eq]; simp only [code]; exact ek.2.2.2
  · rw [setup_eq]; simp only [code]; exact encloses_zero
  · rw [setup_eq]; simp only [code]; exact encloses_zero

end Sides

/-! ### The theorems of `events` -/

section Events

variable {xs : Array Float}

theorem events_eq (hv : valid xs = true) :
    events xs = outputOf (isolate Trig.invPi Trig.halfPi (setup Trig.invPi Trig.halfPi xs)
        (rd xs 10) (rd xs 11) (rd xs 19).toUInt64 (rd xs 20).toUInt64)
      (joinRuns (finalRuns Trig.invPi Trig.halfPi (setup Trig.invPi Trig.halfPi xs)
        (isolate Trig.invPi Trig.halfPi (setup Trig.invPi Trig.halfPi xs) (rd xs 10) (rd xs 11)
          (rd xs 19).toUInt64 (rd xs 20).toUInt64).cells)) := by
  unfold events eventsWith
  rw [if_pos hv]

/-- The real side of a valid input's event: its intervals enclose it, its margins are not
negative, and its functions state the condition. -/
theorem side (hv : valid xs = true) :
    ∃ M : Parts, Sound (setup Trig.invPi Trig.halfPi xs) M ∧ 0 ≤ M.W1 ∧ 0 ≤ M.W2 ∧
      ∀ t, Condition xs t ↔ Holds M.g1 M.g2 t := by
  have F := valid_facts hv
  by_cases h1 : (rd xs 12 == 1.0) = true
  · refine ⟨shadowSide xs, shadow_sound F h1, F.pad h1,
      mul_nonneg (by positivity) (F.pad h1), fun t => ?_⟩
    simp only [Condition, h1, ite_true]
    exact inShadow_iff _ _ _ _
  · simp only [Bool.not_eq_true] at h1
    by_cases h2 : (rd xs 12 == 2.0) = true
    · refine ⟨inertialSide xs, inertial_sound h1 h2, le_rfl, le_rfl, fun t => ?_⟩
      simp only [Condition, h1, h2, Bool.false_eq_true, ite_true, ite_false]
      rw [within_iff rfl (sunAt_unit (val (rd xs 9)) t)]
      exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
    · simp only [Bool.not_eq_true] at h2
      refine ⟨rswSide xs, rsw_sound F h1 h2, le_rfl, le_rfl, fun t => ?_⟩
      simp only [Condition, h1, h2, Bool.false_eq_true, ite_false]
      rw [within_iff (rsw_norm F.orbit _ _ _) (sunAt_unit (val (rd xs 9)) t)]
      exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

theorem near_self {M : Parts} (w1 : 0 ≤ M.W1) (w2 : 0 ≤ M.W2) (t : ℝ) : Near M M.g1 M.g2 t := by
  simp only [Near, sub_self, abs_zero]
  exact ⟨w1, w2⟩

/-- The output of a valid input: its status, its covering, its labels, and its window, for any
functions within the margins of the event's functions on the window. -/
theorem events_parts (hv : valid xs = true) {M : Parts} (S : Sound (setup Trig.invPi Trig.halfPi xs) M)
    {h1 h2 : ℝ → ℝ} (hN : ∀ t, val (rd xs 10) ≤ t → t ≤ val (rd xs 11) → Near M h1 h2 t) :
    ((events xs)[0]!.toBits = (0 : UInt64).toFloat.toBits ∨
        (events xs)[0]!.toBits = (1 : UInt64).toFloat.toBits) ∧
      (∀ t, val (rd xs 10) ≤ t → t ≤ val (rd xs 11) → Holds h1 h2 t → Returned (events xs) t) ∧
      (∀ j, 6 + 3 * j < (events xs).size → (events xs)[6 + 3 * j]! = 1.0 →
        ∀ t, val (events xs)[4 + 3 * j]! ≤ t → t ≤ val (events xs)[5 + 3 * j]! →
          Holds h1 h2 t) ∧
      ∀ j, 6 + 3 * j < (events xs).size →
        val (rd xs 10) ≤ val (events xs)[4 + 3 * j]! ∧ val (events xs)[5 + 3 * j]! ≤ val (rd xs 11) := by
  have F := valid_facts hv
  rw [events_eq hv]
  exact output_spec S F.t0 F.t1 hN F.cap

/-- For a valid input, the status is 0 or 1. -/
theorem events_status (hv : valid xs = true) :
    (events xs)[0]!.toBits = (0 : UInt64).toFloat.toBits ∨
      (events xs)[0]!.toBits = (1 : UInt64).toFloat.toBits := by
  obtain ⟨M, S, w1, w2, -⟩ := side hv
  exact (events_parts hv S (h1 := M.g1) (h2 := M.g2) fun t _ _ => near_self w1 w2 t).1

/-- For a valid input, the status and the number of levels completed are those of the search,
which completed all `L` levels with status 0, or stopped with status 1 before a level of more
than `C` cells. -/
theorem events_progress (hv : valid xs = true) :
    let s := isolate Trig.invPi Trig.halfPi (setup Trig.invPi Trig.halfPi xs) (rd xs 10)
      (rd xs 11) (rd xs 19).toUInt64 (rd xs 20).toUInt64
    (events xs)[0]! = s.status.toFloat ∧ (events xs)[3]! = s.levels.toFloat ∧
      ((s.status = 0 ∧ s.levels = (rd xs 19).toUInt64) ∨
        (s.status = 1 ∧ s.levels < (rd xs 19).toUInt64 ∧ (rd xs 20).toUInt64 <
          (refineCells Trig.invPi Trig.halfPi (setup Trig.invPi Trig.halfPi xs) s.cells).size.toUInt64)) := by
  intro s
  rw [events_eq hv]
  refine ⟨?_, ?_, isolate_status _ _ _ _ _⟩
  · simp only [outputOf]
    rw [append_get_left _ _ 0 (by simp)]
    rfl
  · simp only [outputOf]
    rw [append_get_left _ _ 3 (by simp)]
    rfl

/-- **E1.**  For a valid input, every time of the window at which the condition holds lies in a
returned run. -/
theorem events_cover (hv : valid xs = true) {t : ℝ} (ht0 : val (rd xs 10) ≤ t)
    (ht1 : t ≤ val (rd xs 11)) (hc : Condition xs t) : Returned (events xs) t := by
  obtain ⟨M, S, w1, w2, hC⟩ := side hv
  exact (events_parts hv S fun t _ _ => near_self w1 w2 t).2.1 t ht0 ht1 ((hC t).mp hc)

/-- **E2.**  For a valid input, the condition holds at every time of a run labeled 1. -/
theorem events_holds (hv : valid xs = true) {j : Nat} (hj : 6 + 3 * j < (events xs).size)
    (hl : (events xs)[6 + 3 * j]! = 1.0) {t : ℝ} (ha : val (events xs)[4 + 3 * j]! ≤ t)
    (hb : t ≤ val (events xs)[5 + 3 * j]!) : Condition xs t := by
  obtain ⟨M, S, w1, w2, hC⟩ := side hv
  exact (hC t).mpr ((events_parts hv S fun t _ _ => near_self w1 w2 t).2.2.1 j hj hl t ha hb)

/-- **E3.**  For a valid input, every run lies in the window. -/
theorem events_within (hv : valid xs = true) {j : Nat} (hj : 6 + 3 * j < (events xs).size) :
    val (rd xs 10) ≤ val (events xs)[4 + 3 * j]! ∧ val (events xs)[5 + 3 * j]! ≤ val (rd xs 11) := by
  obtain ⟨M, S, w1, w2, -⟩ := side hv
  exact (events_parts hv S (h1 := M.g1) (h2 := M.g2) fun t _ _ => near_self w1 w2 t).2.2.2 j hj

/-- **E4.**  For a valid input of the shadow and a trajectory `ρ` within `δ ≤ P` of the Kepler
trajectory at every time of the window, every time of the window at which `ρ` is in the shadow
lies in a returned run, and `ρ` is in the shadow at every time of a run labeled 1. -/
theorem events_near (hv : valid xs = true) (h1 : (rd xs 12 == 1.0) = true) {ρ : ℝ → V3}
    {δ : ℝ} (hδ : δ ≤ val (rd xs 15))
    (hρ : ∀ t, val (rd xs 10) ≤ t → t ≤ val (rd xs 11) → dist3 (ρ t) (positionOf xs t) ≤ δ) :
    (∀ t, val (rd xs 10) ≤ t → t ≤ val (rd xs 11) →
        InShadow (val (rd xs 13)) (val (rd xs 14)) (ρ t) (sunOf xs t) → Returned (events xs) t) ∧
      ∀ j, 6 + 3 * j < (events xs).size → (events xs)[6 + 3 * j]! = 1.0 →
        ∀ t, val (events xs)[4 + 3 * j]! ≤ t → t ≤ val (events xs)[5 + 3 * j]! →
          InShadow (val (rd xs 13)) (val (rd xs 14)) (ρ t) (sunOf xs t) := by
  have F := valid_facts hv
  have hN : ∀ t, val (rd xs 10) ≤ t → t ≤ val (rd xs 11) →
      Near (shadowSide xs) (fun t => dot (ρ t) (sunOf xs t))
        (fun t => shadowG2 (cosA xs) (sinA xs) (val (rd xs 14)) (ρ t) (sunOf xs t)) t :=
    fun t a b => by
      have h := hρ t a b
      rw [dist3_eq] at h
      obtain ⟨n1, n2⟩ := shadow_near (cosA xs) (sinA xs) (val (rd xs 14)) (sunAt_unit _ t) h
      exact ⟨n1.trans hδ, n2.trans (mul_le_mul_of_nonneg_left hδ (by positivity))⟩
  have P := events_parts hv (shadow_sound F h1) hN
  exact ⟨fun t a b c => P.2.1 t a b ((inShadow_iff _ _ _ _).mp c),
    fun j hj hl t a b => (inShadow_iff _ _ _ _).mpr (P.2.2.1 j hj hl t a b)⟩

/-- A function with a rate bound that is at most 0 at times arbitrarily close to `c` is at most
0 at `c`. -/
theorem closed_of_lip {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ t t', |g t - g t'| ≤ L * |t - t'|) {c : ℝ}
    (h : ∀ ε > 0, ∃ t, |t - c| < ε ∧ g t ≤ 0) : g c ≤ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨t, ht, hg⟩ := h (g c / (L + 1)) (div_pos hc (by linarith))
  have l := (abs_le.mp (hlip c t)).2
  rw [abs_sub_comm c t] at l
  have h3 : L * |t - c| ≤ L * (g c / (L + 1)) := mul_le_mul_of_nonneg_left ht.le hL
  have h4 : L * (g c / (L + 1)) < g c := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **E5.**  For a valid input, every crossing of the window lies in a returned run, and a
crossing in a run labeled 1 is one of its ends. -/
theorem events_crossing (hv : valid xs = true) {c : ℝ}
    (hc : Crossing (Condition xs) (val (rd xs 10)) (val (rd xs 11)) c) :
    Returned (events xs) c ∧ ∀ j, InRun (events xs) j c → (events xs)[6 + 3 * j]! = 1.0 →
      c = val (events xs)[4 + 3 * j]! ∨ c = val (events xs)[5 + 3 * j]! := by
  obtain ⟨M, S, -, -, hC⟩ := side hv
  obtain ⟨c0, c1, hε⟩ := hc
  have hcond : Condition xs c := by
    rw [hC]
    refine ⟨closed_of_lip S.n1 S.lip1 fun ε hε' => ?_, closed_of_lip S.n2 S.lip2 fun ε hε' => ?_⟩
    · obtain ⟨t, -, -, ht, hct⟩ := (hε ε hε').1
      exact ⟨t, ht, ((hC t).mp hct).1⟩
    · obtain ⟨t, -, -, ht, hct⟩ := (hε ε hε').1
      exact ⟨t, ht, ((hC t).mp hct).2⟩
  refine ⟨events_cover hv c0 c1 hcond, fun j ⟨hj, hlo, hhi⟩ hl => ?_⟩
  by_contra hne
  push_neg at hne
  have hlo' : val (events xs)[4 + 3 * j]! < c := lt_of_le_of_ne hlo (Ne.symm hne.1)
  have hhi' : c < val (events xs)[5 + 3 * j]! := lt_of_le_of_ne hhi hne.2
  obtain ⟨t, -, -, ht, hnot⟩ := (hε (min (c - val (events xs)[4 + 3 * j]!)
    (val (events xs)[5 + 3 * j]! - c)) (lt_min (by linarith) (by linarith))).2
  have a := abs_lt.mp ht
  have m1 := min_le_left (c - val (events xs)[4 + 3 * j]!) (val (events xs)[5 + 3 * j]! - c)
  have m2 := min_le_right (c - val (events xs)[4 + 3 * j]!) (val (events xs)[5 + 3 * j]! - c)
  exact hnot (events_holds hv hj hl (by linarith) (by linarith))

/-- Status 2 marks exactly the inputs that `valid` rejects. -/
theorem events_invalid : (events xs)[0]! = 2.0 ↔ valid xs = false := by
  constructor
  · intro h
    by_contra hv
    have hv' : valid xs = true := by simpa using hv
    rcases events_status hv' with s | s <;> rw [h] at s <;> exact absurd s (by decide +kernel)
  · intro h
    unfold events eventsWith
    rw [if_neg (by simp [h])]
    rfl

end Events

end Demos.Events
