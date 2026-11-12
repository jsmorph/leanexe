import Demos.Sgp4.Kepler

/-!
The two-body model of the screening demo over the real numbers.  An object follows the Kepler
orbit of its elements, and its position at a time is the point of its path at the eccentric
anomaly that Kepler's equation gives for that time.  `path_radius` bounds the distance of every
point of a path from the origin by the perigee and apogee radii (M1), `position_path` and
`path_periodic` place every position on the path (M2), and `position_lipschitz` bounds the
distance moved in a time by the speed bound `a n / (1 - e)` times that time (M3).
-/

namespace Demos.Screening

open Real Demos.Sgp4

/-- An angle in degrees in radians. -/
noncomputable def rad (x : ℝ) : ℝ := x * (π / 180)

/-- The Euclidean distance between two points. -/
noncomputable def dist3 (p q : ℝ × ℝ × ℝ) : ℝ :=
  √((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2)

/-- The elements of an object: the semimajor axis in km, the eccentricity, the inclination, the
right ascension of the ascending node, the argument of perigee, and the mean anomaly at the epoch
in degrees, and the epoch in minutes on the window's time scale. -/
structure Orbit where
  a : ℝ
  e : ℝ
  incl : ℝ
  node : ℝ
  argp : ℝ
  m0 : ℝ
  epoch : ℝ

namespace Orbit

/-- The elements of an orbit that the model accepts. -/
def Valid (o : Orbit) : Prop := 0 < o.a ∧ 0 ≤ o.e ∧ o.e < 1

/-- The mean motion in radians per minute for the gravitational parameter `mu` in km³/s². -/
noncomputable def motion (mu : ℝ) (o : Orbit) : ℝ := 60 * √(mu / (o.a * o.a * o.a))

/-- `√(1 - e²)`. -/
noncomputable def beta (o : Orbit) : ℝ := √(1 - o.e * o.e)

/-- The unit vector `P` toward the perigee. -/
noncomputable def toPerigee (o : Orbit) : ℝ × ℝ × ℝ :=
  (cos (rad o.argp) * cos (rad o.node) - sin (rad o.argp) * sin (rad o.node) * cos (rad o.incl),
    cos (rad o.argp) * sin (rad o.node) + sin (rad o.argp) * cos (rad o.node) * cos (rad o.incl),
    sin (rad o.argp) * sin (rad o.incl))

/-- The unit vector `Q` a quarter turn ahead of the perigee. -/
noncomputable def ahead (o : Orbit) : ℝ × ℝ × ℝ :=
  (-sin (rad o.argp) * cos (rad o.node) - cos (rad o.argp) * sin (rad o.node) * cos (rad o.incl),
    -sin (rad o.argp) * sin (rad o.node) + cos (rad o.argp) * cos (rad o.node) * cos (rad o.incl),
    cos (rad o.argp) * sin (rad o.incl))

/-- The point of the path at the eccentric anomaly `E`, in km. -/
noncomputable def path (o : Orbit) (E : ℝ) : ℝ × ℝ × ℝ :=
  let p := o.a * (cos E - o.e)
  let q := o.a * o.beta * sin E
  (p * o.toPerigee.1 + q * o.ahead.1, p * o.toPerigee.2.1 + q * o.ahead.2.1,
    p * o.toPerigee.2.2 + q * o.ahead.2.2)

/-- The eccentric anomaly at `t` minutes, the root of `E - e sin E = M₀ + n (t - τ)`. -/
noncomputable def anomaly (mu : ℝ) (o : Orbit) (t : ℝ) : ℝ :=
  Kepler.root o.e 0 (rad o.m0 + o.motion mu * (t - o.epoch))

/-- The position in km at `t` minutes. -/
noncomputable def position (mu : ℝ) (o : Orbit) (t : ℝ) : ℝ × ℝ × ℝ := o.path (o.anomaly mu t)

/-- The bound `a n / (1 - e)` of the speed in km per minute. -/
noncomputable def speed (mu : ℝ) (o : Orbit) : ℝ := o.a * o.motion mu / (1 - o.e)

end Orbit

/-! ### The distance -/

theorem dist3_nonneg (p q : ℝ × ℝ × ℝ) : 0 ≤ dist3 p q := sqrt_nonneg _

theorem dist3_comm (p q : ℝ × ℝ × ℝ) : dist3 p q = dist3 q p := by
  unfold dist3
  congr 1
  ring

theorem dist3_sq (p q : ℝ × ℝ × ℝ) :
    dist3 p q ^ 2 = (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2 :=
  sq_sqrt (by positivity)

theorem dist3_triangle (p q r : ℝ × ℝ × ℝ) : dist3 p r ≤ dist3 p q + dist3 q r := by
  have hA := dist3_sq p q
  have hB := dist3_sq q r
  have hA0 := dist3_nonneg p q
  have hB0 := dist3_nonneg q r
  generalize dist3 p q = A at hA hA0
  generalize dist3 q r = B at hB hB0
  unfold dist3
  refine sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have cs : (p.1 - q.1) * (q.1 - r.1) + (p.2.1 - q.2.1) * (q.2.1 - r.2.1) +
      (p.2.2 - q.2.2) * (q.2.2 - r.2.2) ≤ A * B := by
    have h2 : ((p.1 - q.1) * (q.1 - r.1) + (p.2.1 - q.2.1) * (q.2.1 - r.2.1) +
        (p.2.2 - q.2.2) * (q.2.2 - r.2.2)) ^ 2 ≤ (A * B) ^ 2 := by
      rw [mul_pow, hA, hB]
      nlinarith [sq_nonneg ((p.1 - q.1) * (q.2.1 - r.2.1) - (p.2.1 - q.2.1) * (q.1 - r.1)),
        sq_nonneg ((p.1 - q.1) * (q.2.2 - r.2.2) - (p.2.2 - q.2.2) * (q.1 - r.1)),
        sq_nonneg ((p.2.1 - q.2.1) * (q.2.2 - r.2.2) - (p.2.2 - q.2.2) * (q.2.1 - r.2.1))]
    exact (abs_le_of_sq_le_sq' h2 (by positivity)).2
  nlinarith [cs, hA, hB]

/-! ### M1: the frame and the radius -/

/-- Two unit vectors at a right angle. -/
structure Frame (P Q : ℝ × ℝ × ℝ) : Prop where
  unitP : P.1 ^ 2 + P.2.1 ^ 2 + P.2.2 ^ 2 = 1
  unitQ : Q.1 ^ 2 + Q.2.1 ^ 2 + Q.2.2 ^ 2 = 1
  orth : P.1 * Q.1 + P.2.1 * Q.2.1 + P.2.2 * Q.2.2 = 0

theorem frame (o : Orbit) : Frame o.toPerigee o.ahead := by
  have hw := sin_sq_add_cos_sq (rad o.argp)
  have ho := sin_sq_add_cos_sq (rad o.node)
  have hi := sin_sq_add_cos_sq (rad o.incl)
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Orbit.toPerigee, Orbit.ahead]
  · linear_combination (cos (rad o.argp) ^ 2 + sin (rad o.argp) ^ 2 * cos (rad o.incl) ^ 2) * ho +
      sin (rad o.argp) ^ 2 * hi + hw
  · linear_combination (sin (rad o.argp) ^ 2 + cos (rad o.argp) ^ 2 * cos (rad o.incl) ^ 2) * ho +
      cos (rad o.argp) ^ 2 * hi + hw
  · linear_combination (cos (rad o.argp) * sin (rad o.argp) * (cos (rad o.incl) ^ 2 - 1)) * ho +
      (cos (rad o.argp) * sin (rad o.argp)) * hi

/-- The squared length of `p P + q Q` for two unit vectors at a right angle. -/
theorem frame_comb {P Q : ℝ × ℝ × ℝ} (h : Frame P Q) (p q : ℝ) :
    (p * P.1 + q * Q.1) ^ 2 + (p * P.2.1 + q * Q.2.1) ^ 2 + (p * P.2.2 + q * Q.2.2) ^ 2 =
      p ^ 2 + q ^ 2 := by
  linear_combination p ^ 2 * h.unitP + q ^ 2 * h.unitQ + 2 * p * q * h.orth

theorem beta_sq {o : Orbit} (hv : o.Valid) : o.beta ^ 2 = 1 - o.e ^ 2 := by
  unfold Orbit.beta
  rw [sq_sqrt (by nlinarith [hv.2.1, hv.2.2])]
  ring

/-- The distance of the path's point at `E` from the origin is `a (1 - e cos E)`. -/
theorem path_norm {o : Orbit} (hv : o.Valid) (E : ℝ) :
    dist3 (o.path E) (0, 0, 0) = o.a * (1 - o.e * cos E) := by
  have hb := beta_sq hv
  have hE := sin_sq_add_cos_sq E
  have hc := frame_comb (frame o) (o.a * (cos E - o.e)) (o.a * o.beta * sin E)
  have hpos : 0 ≤ o.a * (1 - o.e * cos E) := by
    have : o.e * cos E ≤ o.e := by
      nlinarith [cos_le_one E, hv.2.1]
    nlinarith [hv.1, hv.2.2]
  have e2 : (o.a * (cos E - o.e)) ^ 2 + (o.a * o.beta * sin E) ^ 2 =
      (o.a * (1 - o.e * cos E)) ^ 2 := by
    have : (o.a * o.beta * sin E) ^ 2 = o.a ^ 2 * o.beta ^ 2 * sin E ^ 2 := by ring
    rw [this, hb]
    linear_combination (o.a ^ 2 * (1 - o.e ^ 2)) * hE
  unfold dist3
  simp only [Orbit.path, sub_zero]
  rw [hc, e2, sqrt_sq hpos]

/-- **M1.**  Every point of a path lies between the perigee and the apogee radii. -/
theorem path_radius {o : Orbit} (hv : o.Valid) (E : ℝ) :
    o.a * (1 - o.e) ≤ dist3 (o.path E) (0, 0, 0) ∧
      dist3 (o.path E) (0, 0, 0) ≤ o.a * (1 + o.e) := by
  rw [path_norm hv]
  constructor
  · have k : o.e * cos E ≤ o.e := mul_le_of_le_one_right hv.2.1 (cos_le_one E)
    nlinarith [mul_le_mul_of_nonneg_left k hv.1.le]
  · have k : o.e * -1 ≤ o.e * cos E := mul_le_mul_of_nonneg_left (neg_one_le_cos E) hv.2.1
    nlinarith [mul_le_mul_of_nonneg_left k hv.1.le]

/-! ### M2: positions on the path -/

/-- **M2.**  The position at `t` is the point of the path at the eccentric anomaly at `t`. -/
theorem position_path (mu : ℝ) (o : Orbit) (t : ℝ) :
    o.position mu t = o.path (o.anomaly mu t) := rfl

/-- **M2.**  The path repeats with period `2π` in the eccentric anomaly. -/
theorem path_periodic (o : Orbit) (E : ℝ) (k : ℤ) : o.path (E + k * (2 * π)) = o.path E := by
  simp only [Orbit.path, sin_add_int_mul_two_pi, cos_add_int_mul_two_pi]

/-- Every point of the path is its point at an eccentric anomaly in `[0, 2π]`. -/
theorem path_reduce (o : Orbit) (E : ℝ) :
    ∃ E' : ℝ, 0 ≤ E' ∧ E' ≤ 2 * π ∧ o.path E = o.path E' := by
  have hp : 0 < 2 * π := by positivity
  refine ⟨E - ⌊E / (2 * π)⌋ * (2 * π), ?_, ?_, ?_⟩
  · have := Int.floor_le (E / (2 * π))
    have : ⌊E / (2 * π)⌋ * (2 * π) ≤ E / (2 * π) * (2 * π) :=
      mul_le_mul_of_nonneg_right this hp.le
    rw [div_mul_cancel₀ _ hp.ne'] at this
    linarith
  · have := Int.lt_floor_add_one (E / (2 * π))
    have : E / (2 * π) * (2 * π) < (⌊E / (2 * π)⌋ + 1) * (2 * π) :=
      mul_lt_mul_of_pos_right this hp
    rw [div_mul_cancel₀ _ hp.ne'] at this
    linarith
  · have := path_periodic o (E - ⌊E / (2 * π)⌋ * (2 * π)) ⌊E / (2 * π)⌋
    rw [sub_add_cancel] at this
    exact this

/-! ### M3: the speed bound -/

/-- A chord of the unit circle is no longer than its arc. -/
theorem chord_le (E E' : ℝ) : (cos E - cos E') ^ 2 + (sin E - sin E') ^ 2 ≤ (E - E') ^ 2 := by
  have h := one_sub_sq_div_two_le_cos (x := E - E')
  have e : (cos E - cos E') ^ 2 + (sin E - sin E') ^ 2 = 2 - 2 * cos (E - E') := by
    rw [cos_sub]
    linear_combination sin_sq_add_cos_sq E + sin_sq_add_cos_sq E'
  rw [e]
  linarith

/-- Two points of a path lie no farther apart than `a` times the difference of their eccentric
anomalies. -/
theorem path_lipschitz {o : Orbit} (hv : o.Valid) (E E' : ℝ) :
    dist3 (o.path E) (o.path E') ≤ o.a * |E - E'| := by
  have hb := beta_sq hv
  have hf := frame o
  have hchord := chord_le E E'
  have hd : dist3 (o.path E) (o.path E') ^ 2 =
      (o.a * (cos E - o.e) - o.a * (cos E' - o.e)) ^ 2 +
        (o.a * o.beta * sin E - o.a * o.beta * sin E') ^ 2 := by
    rw [dist3_sq]
    simp only [Orbit.path]
    linear_combination frame_comb hf (o.a * (cos E - o.e) - o.a * (cos E' - o.e))
      (o.a * o.beta * sin E - o.a * o.beta * sin E')
  have hle : dist3 (o.path E) (o.path E') ^ 2 ≤ (o.a * |E - E'|) ^ 2 := by
    rw [hd, mul_pow, sq_abs]
    have he2 : 0 ≤ o.e ^ 2 := sq_nonneg _
    have : (o.a * o.beta * sin E - o.a * o.beta * sin E') ^ 2 =
        o.a ^ 2 * (1 - o.e ^ 2) * (sin E - sin E') ^ 2 := by
      rw [← hb]; ring
    rw [this]
    have k1 : (o.a * (cos E - o.e) - o.a * (cos E' - o.e)) ^ 2 =
        o.a ^ 2 * (cos E - cos E') ^ 2 := by ring
    rw [k1]
    have k2 : 0 ≤ o.a ^ 2 * o.e ^ 2 * (sin E - sin E') ^ 2 := by positivity
    have k3 := mul_le_mul_of_nonneg_left hchord (sq_nonneg o.a)
    nlinarith [k2, k3]
  exact (abs_le_of_sq_le_sq' hle (by have := hv.1; positivity)).2

/-- The eccentric anomaly changes by at most the change of the mean anomaly over `1 - e`. -/
theorem root_lipschitz {e : ℝ} (h0 : 0 ≤ e) (h1 : e < 1) (M M' : ℝ) :
    (1 - e) * |Kepler.root e 0 M - Kepler.root e 0 M'| ≤ |M - M'| := by
  have hk : e ^ 2 + (0 : ℝ) ^ 2 < 1 := by nlinarith
  have hs : √(e ^ 2 + (0 : ℝ) ^ 2) = e := by
    rw [zero_pow two_ne_zero, add_zero, sqrt_sq h0]
  have rM := Kepler.root_spec hk M
  have rM' := Kepler.root_spec hk M'
  rcases le_total (Kepler.root e 0 M') (Kepler.root e 0 M) with h | h
  · have g := Kepler.growth e 0 h
    rw [hs, rM, rM'] at g
    rw [abs_of_nonneg (sub_nonneg.2 h)]
    exact g.trans (le_abs_self _)
  · have g := Kepler.growth e 0 h
    rw [hs, rM, rM'] at g
    rw [abs_of_nonpos (sub_nonpos.2 h), abs_sub_comm M M']
    linarith [le_abs_self (M' - M)]

theorem motion_nonneg (mu : ℝ) (o : Orbit) : 0 ≤ o.motion mu := by
  unfold Orbit.motion; positivity

theorem speed_nonneg {mu : ℝ} {o : Orbit} (hv : o.Valid) : 0 ≤ o.speed mu := by
  unfold Orbit.speed
  have := motion_nonneg mu o
  have := hv.1
  have : 0 < 1 - o.e := by linarith [hv.2.2]
  positivity

/-- **M3.**  An object moves at most `a n / (1 - e)` km per minute. -/
theorem position_lipschitz {mu : ℝ} {o : Orbit} (hv : o.Valid) (t t' : ℝ) :
    dist3 (o.position mu t) (o.position mu t') ≤ o.speed mu * |t - t'| := by
  have h1 : 0 < 1 - o.e := by linarith [hv.2.2]
  have hp := path_lipschitz hv (o.anomaly mu t) (o.anomaly mu t')
  have hr := root_lipschitz hv.2.1 hv.2.2 (rad o.m0 + o.motion mu * (t - o.epoch))
    (rad o.m0 + o.motion mu * (t' - o.epoch))
  have hM : |rad o.m0 + o.motion mu * (t - o.epoch) - (rad o.m0 + o.motion mu * (t' - o.epoch))| =
      o.motion mu * |t - t'| := by
    rw [show rad o.m0 + o.motion mu * (t - o.epoch) - (rad o.m0 + o.motion mu * (t' - o.epoch)) =
      o.motion mu * (t - t') by ring, abs_mul, abs_of_nonneg (motion_nonneg mu o)]
  rw [hM] at hr
  have hE : |o.anomaly mu t - o.anomaly mu t'| ≤ o.motion mu * |t - t'| / (1 - o.e) := by
    rw [le_div_iff₀ h1]
    unfold Orbit.anomaly
    linarith
  calc dist3 (o.position mu t) (o.position mu t')
      ≤ o.a * |o.anomaly mu t - o.anomaly mu t'| := hp
    _ ≤ o.a * (o.motion mu * |t - t'| / (1 - o.e)) :=
        mul_le_mul_of_nonneg_left hE hv.1.le
    _ = o.speed mu * |t - t'| := by unfold Orbit.speed; ring

end Demos.Screening
