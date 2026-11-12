import Demos.Screening.Model

/-!
The model of the event-window demo over the real numbers.  The spacecraft follows the Kepler
orbit of `Demos.Screening.Orbit.position`, and the Sun's direction is the U.S. Naval
Observatory's approximate solar coordinates, `sunDir`.  `sun_unit` and `sun_lipschitz` state
that `sunDir` is a unit vector that moves at most `sunRate` radians per day (M1), `axis_sq` that
the shadow's `y` is the distance from the shadow axis, and `rsw_norm` that a vector fixed in the
orbit's radial, along-track, and cross-track frame keeps its length (M2).  The theorems of the
section on rates bound the rate of change of each event's condition functions (M3).
-/

namespace Demos.Events

open Real Demos.Screening

/-- A vector of three real coordinates. -/
abbrev V3 := ℝ × ℝ × ℝ

def dot (u v : V3) : ℝ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def cross (u v : V3) : V3 :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1, u.2.2 * v.1 - u.1 * v.2.2, u.1 * v.2.1 - u.2.1 * v.1)

noncomputable def norm3 (u : V3) : ℝ := √(u.1 * u.1 + u.2.1 * u.2.1 + u.2.2 * u.2.2)

def add3 (u v : V3) : V3 := (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

def sub3 (u v : V3) : V3 := (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)

def smul3 (c : ℝ) (u : V3) : V3 := (c * u.1, c * u.2.1, c * u.2.2)

/-! ### Vectors -/

theorem norm3_nonneg (u : V3) : 0 ≤ norm3 u := sqrt_nonneg _

theorem norm3_sq (u : V3) : norm3 u ^ 2 = dot u u := by
  unfold norm3 dot
  exact sq_sqrt (by nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2.1, mul_self_nonneg u.2.2])

theorem norm3_le_of_sq {u : V3} {k : ℝ} (hk : 0 ≤ k) (h : dot u u ≤ k ^ 2) : norm3 u ≤ k := by
  unfold norm3
  rw [← sqrt_sq hk]
  exact sqrt_le_sqrt (by unfold dot at h; linarith)

/-- Lagrange's identity. -/
theorem lagrange (u v : V3) :
    dot (cross u v) (cross u v) = dot u u * dot v v - dot u v ^ 2 := by
  unfold dot cross
  ring

theorem dot_le (u v : V3) : |dot u v| ≤ norm3 u * norm3 v := by
  have h : dot u v ^ 2 ≤ (norm3 u * norm3 v) ^ 2 := by
    rw [mul_pow, norm3_sq, norm3_sq]
    have := lagrange u v
    have : 0 ≤ dot (cross u v) (cross u v) := by
      unfold dot
      nlinarith [mul_self_nonneg (cross u v).1, mul_self_nonneg (cross u v).2.1,
        mul_self_nonneg (cross u v).2.2]
    linarith
  exact abs_le.mpr (abs_le_of_sq_le_sq' h (mul_nonneg (norm3_nonneg u) (norm3_nonneg v)))

theorem norm3_cross_le (u v : V3) : norm3 (cross u v) ≤ norm3 u * norm3 v := by
  apply norm3_le_of_sq (mul_nonneg (norm3_nonneg u) (norm3_nonneg v))
  rw [lagrange, mul_pow, norm3_sq, norm3_sq]
  nlinarith [sq_nonneg (dot u v)]

theorem norm3_add_le (u v : V3) : norm3 (add3 u v) ≤ norm3 u + norm3 v := by
  apply norm3_le_of_sq (add_nonneg (norm3_nonneg u) (norm3_nonneg v))
  have e : dot (add3 u v) (add3 u v) = dot u u + 2 * dot u v + dot v v := by
    unfold dot add3
    ring
  rw [e, add_sq, ← norm3_sq, ← norm3_sq]
  nlinarith [(abs_le.mp (dot_le u v)).2]

theorem norm3_smul (c : ℝ) (u : V3) : norm3 (smul3 c u) = |c| * norm3 u := by
  unfold norm3 smul3
  rw [← sqrt_sq_eq_abs, ← sqrt_mul (sq_nonneg c)]
  congr 1
  ring

theorem norm3_sub_comm (u v : V3) : norm3 (sub3 u v) = norm3 (sub3 v u) := by
  unfold norm3 sub3
  congr 1
  ring

theorem norm3_sub_le (u v w : V3) : norm3 (sub3 u w) ≤ norm3 (sub3 u v) + norm3 (sub3 v w) := by
  have e : sub3 u w = add3 (sub3 u v) (sub3 v w) := by
    unfold sub3 add3
    ext <;> simp only <;> ring
  rw [e]
  exact norm3_add_le _ _

theorem abs_norm3_sub (u v : V3) : |norm3 u - norm3 v| ≤ norm3 (sub3 u v) := by
  have a := norm3_add_le (sub3 u v) v
  have b := norm3_add_le (sub3 v u) u
  have eu : add3 (sub3 u v) v = u := by
    unfold sub3 add3
    ext <;> simp only <;> ring
  have ev : add3 (sub3 v u) u = v := by
    unfold sub3 add3
    ext <;> simp only <;> ring
  rw [eu] at a
  rw [ev, norm3_sub_comm] at b
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem dist3_eq (p q : V3) : dist3 p q = norm3 (sub3 p q) := by
  unfold dist3 norm3 sub3
  congr 1
  ring

theorem dot_sub (r s r' s' : V3) :
    dot r s - dot r' s' = dot (sub3 r r') s + dot r' (sub3 s s') := by
  unfold dot sub3
  ring

theorem cross_sub (r s r' s' : V3) :
    sub3 (cross r s) (cross r' s') = add3 (cross (sub3 r r') s) (cross r' (sub3 s s')) := by
  unfold cross sub3 add3
  ext <;> simp only <;> ring

/-- The change of a product `r · s` or `|r × s|` is at most `|Δr| |s| + |r'| |Δs|`. -/
theorem dot_change (r s r' s' : V3) :
    |dot r s - dot r' s'| ≤ norm3 (sub3 r r') * norm3 s + norm3 r' * norm3 (sub3 s s') := by
  rw [dot_sub]
  exact (abs_add_le _ _).trans (add_le_add (dot_le _ _) (dot_le _ _))

theorem cross_change (r s r' s' : V3) :
    |norm3 (cross r s) - norm3 (cross r' s')| ≤
      norm3 (sub3 r r') * norm3 s + norm3 r' * norm3 (sub3 s s') := by
  refine (abs_norm3_sub _ _).trans ?_
  rw [cross_sub]
  exact (norm3_add_le _ _).trans (add_le_add (norm3_cross_le _ _) (norm3_cross_le _ _))

/-- The unit vector of `u`. -/
noncomputable def unit3 (u : V3) : V3 := (u.1 / norm3 u, u.2.1 / norm3 u, u.2.2 / norm3 u)

theorem dot_unit {u : V3} (h : 0 < norm3 u) : dot (unit3 u) (unit3 u) = 1 := by
  have h2 := norm3_sq u
  unfold dot unit3
  unfold dot at h2
  field_simp
  linarith

/-- Two unit vectors lie no farther apart than their vectors over the least of their lengths. -/
theorem unit_change {u v : V3} {m : ℝ} (hm : 0 < m) (hu : m ≤ norm3 u) (hv : m ≤ norm3 v) :
    norm3 (sub3 (unit3 u) (unit3 v)) ≤ norm3 (sub3 u v) / m := by
  have hA : 0 < norm3 u := hm.trans_le hu
  have hB : 0 < norm3 v := hm.trans_le hv
  have e1 : dot (sub3 (unit3 u) (unit3 v)) (sub3 (unit3 u) (unit3 v)) =
      dot u u / norm3 u ^ 2 + dot v v / norm3 v ^ 2 - 2 * dot u v / (norm3 u * norm3 v) := by
    unfold dot sub3 unit3
    field_simp
    ring
  have e2 : dot (sub3 u v) (sub3 u v) = dot u u + dot v v - 2 * dot u v := by
    unfold dot sub3
    ring
  have hD := dot_le u v
  apply norm3_le_of_sq (div_nonneg (norm3_nonneg _) hm.le)
  rw [e1, div_pow, norm3_sq (sub3 u v), e2, ← norm3_sq u, ← norm3_sq v,
    div_self (pow_ne_zero 2 hA.ne'), div_self (pow_ne_zero 2 hB.ne')]
  generalize norm3 u = A at hA hu hD
  generalize norm3 v = B at hB hv hD
  generalize dot u v = d at hD
  have hAB : 0 < A * B := mul_pos hA hB
  have hdle : d ≤ A * B := (abs_le.mp hD).2
  have hm2 : m ^ 2 ≤ A * B := by nlinarith
  have hnum : 0 ≤ A ^ 2 + B ^ 2 - 2 * d := by nlinarith [sq_nonneg (A - B)]
  rw [show (1 : ℝ) + 1 - 2 * d / (A * B) = (2 * (A * B) - 2 * d) / (A * B) by
    field_simp; ring]
  calc (2 * (A * B) - 2 * d) / (A * B) ≤ (A ^ 2 + B ^ 2 - 2 * d) / (A * B) := by
        apply div_le_div_of_nonneg_right _ hAB.le
        nlinarith [sq_nonneg (A - B)]
    _ ≤ (A ^ 2 + B ^ 2 - 2 * d) / m ^ 2 :=
        div_le_div_of_nonneg_left hnum (by positivity) hm2

/-! ### M1: the Sun's direction -/

/-- The Sun's ecliptic longitude in degrees at `D` days from J2000.0. -/
noncomputable def sunLon (D : ℝ) : ℝ :=
  280.459 + 0.98564736 * D + 1.915 * sin (rad (357.529 + 0.98560028 * D)) +
    0.020 * sin (2 * rad (357.529 + 0.98560028 * D))

/-- The obliquity of the ecliptic in degrees at `D` days from J2000.0. -/
noncomputable def sunObl (D : ℝ) : ℝ := 23.439 - 0.00000036 * D

/-- The unit vector of ecliptic longitude `lam` and latitude zero in the equatorial frame of an
ecliptic of obliquity `eps`, both in radians. -/
noncomputable def dirOf (lam eps : ℝ) : V3 := (cos lam, cos eps * sin lam, sin eps * sin lam)

/-- The geocentric direction of the Sun at `D` days from J2000.0. -/
noncomputable def sunDir (D : ℝ) : V3 := dirOf (rad (sunLon D)) (rad (sunObl D))

/-- The bound of the Sun's rate in radians per day. -/
noncomputable def sunRate : ℝ :=
  π / 180 * (0.98564736 + (1.915 + 2 * 0.020) * 0.98560028 * (π / 180) + 0.00000036)

theorem dirOf_unit (lam eps : ℝ) : dot (dirOf lam eps) (dirOf lam eps) = 1 := by
  unfold dot dirOf
  linear_combination sin_sq_add_cos_sq lam + sin lam ^ 2 * sin_sq_add_cos_sq eps

theorem norm3_eq_one {u : V3} (h : dot u u = 1) : norm3 u = 1 := by
  have := norm3_sq u
  rw [h] at this
  nlinarith [norm3_nonneg u]

/-- **M1.**  The Sun's direction is a unit vector. -/
theorem sun_unit (D : ℝ) : norm3 (sunDir D) = 1 := norm3_eq_one (dirOf_unit _ _)

theorem dirOf_change (lam eps lam' eps' : ℝ) :
    norm3 (sub3 (dirOf lam eps) (dirOf lam' eps')) ≤ |lam - lam'| + |eps - eps'| := by
  refine (norm3_sub_le _ (dirOf lam' eps) _).trans (add_le_add ?_ ?_)
  · apply norm3_le_of_sq (abs_nonneg _)
    rw [sq_abs]
    have hc := chord_le lam lam'
    have he := sin_sq_add_cos_sq eps
    unfold dot sub3 dirOf
    simp only
    nlinarith
  · apply norm3_le_of_sq (abs_nonneg _)
    rw [sq_abs]
    have hc := chord_le eps eps'
    have hs := sin_sq_le_one lam'
    unfold dot sub3 dirOf
    simp only
    have e : (cos lam' - cos lam') * (cos lam' - cos lam') +
        (cos eps * sin lam' - cos eps' * sin lam') * (cos eps * sin lam' - cos eps' * sin lam') +
        (sin eps * sin lam' - sin eps' * sin lam') * (sin eps * sin lam' - sin eps' * sin lam') =
        sin lam' ^ 2 * ((cos eps - cos eps') ^ 2 + (sin eps - sin eps') ^ 2) := by ring
    rw [e]
    have h0 : 0 ≤ (cos eps - cos eps') ^ 2 + (sin eps - sin eps') ^ 2 := by positivity
    nlinarith

theorem rad_sub (x y : ℝ) : rad x - rad y = (x - y) * (π / 180) := by
  unfold rad; ring

theorem abs_rad_sub (x y : ℝ) : |rad x - rad y| = |x - y| * (π / 180) := by
  rw [rad_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < π / 180)]

theorem sunLon_change (D D' : ℝ) :
    |sunLon D - sunLon D'| ≤
      (0.98564736 + (1.915 + 2 * 0.020) * 0.98560028 * (π / 180)) * |D - D'| := by
  have hg := abs_rad_sub (357.529 + 0.98560028 * D) (357.529 + 0.98560028 * D')
  have hg' : |rad (357.529 + 0.98560028 * D) - rad (357.529 + 0.98560028 * D')| =
      0.98560028 * (π / 180) * |D - D'| := by
    rw [hg, show (357.529 + 0.98560028 * D) - (357.529 + 0.98560028 * D') =
      0.98560028 * (D - D') by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 0.98560028)]
    ring
  have s1 := abs_sin_sub_sin_le (rad (357.529 + 0.98560028 * D))
    (rad (357.529 + 0.98560028 * D'))
  have s2 := abs_sin_sub_sin_le (2 * rad (357.529 + 0.98560028 * D))
    (2 * rad (357.529 + 0.98560028 * D'))
  rw [show 2 * rad (357.529 + 0.98560028 * D) - 2 * rad (357.529 + 0.98560028 * D') =
    2 * (rad (357.529 + 0.98560028 * D) - rad (357.529 + 0.98560028 * D')) by ring, abs_mul,
    abs_two, hg'] at s2
  rw [hg'] at s1
  have e : sunLon D - sunLon D' = 0.98564736 * (D - D') +
      1.915 * (sin (rad (357.529 + 0.98560028 * D)) - sin (rad (357.529 + 0.98560028 * D'))) +
      0.020 * (sin (2 * rad (357.529 + 0.98560028 * D)) -
        sin (2 * rad (357.529 + 0.98560028 * D'))) := by
    unfold sunLon; ring
  rw [e]
  have a1 : |0.98564736 * (D - D')| = 0.98564736 * |D - D'| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 0.98564736)]
  have a2 := abs_mul (1.915 : ℝ) (sin (rad (357.529 + 0.98560028 * D)) -
    sin (rad (357.529 + 0.98560028 * D')))
  have a3 := abs_mul (0.020 : ℝ) (sin (2 * rad (357.529 + 0.98560028 * D)) -
    sin (2 * rad (357.529 + 0.98560028 * D')))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1.915)] at a2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.020)] at a3
  have t1 := abs_add_le (0.98564736 * (D - D') + 1.915 * (sin (rad (357.529 + 0.98560028 * D)) -
    sin (rad (357.529 + 0.98560028 * D')))) (0.020 * (sin (2 * rad (357.529 + 0.98560028 * D)) -
      sin (2 * rad (357.529 + 0.98560028 * D'))))
  have t2 := abs_add_le (0.98564736 * (D - D')) (1.915 * (sin (rad (357.529 + 0.98560028 * D)) -
    sin (rad (357.529 + 0.98560028 * D'))))
  nlinarith [abs_nonneg (D - D')]

/-- **M1.**  The Sun's direction moves at most `sunRate` radians per day. -/
theorem sun_lipschitz (D D' : ℝ) :
    norm3 (sub3 (sunDir D) (sunDir D')) ≤ sunRate * |D - D'| := by
  refine (dirOf_change _ _ _ _).trans ?_
  rw [abs_rad_sub, abs_rad_sub]
  have hl := sunLon_change D D'
  have he : |sunObl D - sunObl D'| = 0.00000036 * |D - D'| := by
    rw [show sunObl D - sunObl D' = -(0.00000036 * (D - D')) by unfold sunObl; ring, abs_neg,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 0.00000036)]
  rw [he]
  have hp : 0 < π / 180 := by positivity
  unfold sunRate
  nlinarith [mul_le_mul_of_nonneg_right hl hp.le]

theorem sunRate_nonneg : 0 ≤ sunRate := by unfold sunRate; positivity

/-- The Sun's direction at `t` minutes, for minute 0 at `d0` days from J2000.0. -/
noncomputable def sunAt (d0 t : ℝ) : V3 := sunDir (d0 + t / 1440)

theorem sunAt_unit (d0 t : ℝ) : norm3 (sunAt d0 t) = 1 := sun_unit _

theorem sunAt_lipschitz (d0 t t' : ℝ) :
    norm3 (sub3 (sunAt d0 t) (sunAt d0 t')) ≤ sunRate / 1440 * |t - t'| := by
  refine (sun_lipschitz _ _).trans (le_of_eq ?_)
  rw [show d0 + t / 1440 - (d0 + t' / 1440) = (t - t') / 1440 by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 1440)]
  ring

/-! ### M2: the shadow and the orbit's frame -/

/-- The spacecraft at `r` is in the shadow of the cone of half-angle `α` degrees about the axis
`-s` of an Earth of radius `R`: `x = -r · s ≥ 0` and `y cos α - x sin α ≤ R` with
`y = |r × s|`. -/
def InShadow (α R : ℝ) (r s : V3) : Prop :=
  0 ≤ -dot r s ∧ norm3 (cross r s) * cos (rad α) - (-dot r s) * sin (rad α) ≤ R

/-- **M2.**  For a unit `s`, `x² + y² = |r|²`, so `y` is the distance from the axis. -/
theorem axis_sq {s : V3} (hs : norm3 s = 1) (r : V3) :
    (-dot r s) ^ 2 + norm3 (cross r s) ^ 2 = norm3 r ^ 2 := by
  rw [norm3_sq (cross r s), lagrange, norm3_sq, ← norm3_sq s, hs]
  ring

/-- The angle between `v` and `s` is at most `β` degrees. -/
def Within (v s : V3) (β : ℝ) : Prop := norm3 v * norm3 s * cos (rad β) ≤ dot v s

/-- The direction of the position at `t`. -/
noncomputable def radial (mu : ℝ) (o : Orbit) (t : ℝ) : V3 := unit3 (o.position mu t)

/-- The orbit normal `p̂ × q̂`. -/
noncomputable def normal (o : Orbit) : V3 := cross o.toPerigee o.ahead

/-- The along-track direction `Ŵ × R̂`. -/
noncomputable def along (mu : ℝ) (o : Orbit) (t : ℝ) : V3 := cross (normal o) (radial mu o t)

/-- The vector with components `b` in the orbit's radial, along-track, and cross-track frame. -/
noncomputable def rsw (mu : ℝ) (o : Orbit) (b : V3) (t : ℝ) : V3 :=
  add3 (add3 (smul3 b.1 (radial mu o t)) (smul3 b.2.1 (along mu o t))) (smul3 b.2.2 (normal o))

theorem position_radius {o : Orbit} (hv : o.Valid) (mu t : ℝ) :
    o.a * (1 - o.e) ≤ norm3 (o.position mu t) ∧ norm3 (o.position mu t) ≤ o.a * (1 + o.e) := by
  have h := path_radius hv (o.anomaly mu t)
  have e : dist3 (o.path (o.anomaly mu t)) (0, 0, 0) = norm3 (o.position mu t) := by
    rw [dist3_eq]
    unfold norm3 sub3 Orbit.position
    simp only [sub_zero]
  rw [e] at h
  exact h

theorem perigee_pos {o : Orbit} (hv : o.Valid) : 0 < o.a * (1 - o.e) :=
  mul_pos hv.1 (by linarith [hv.2.2])

theorem normal_unit (o : Orbit) : dot (normal o) (normal o) = 1 := by
  have f := frame o
  unfold normal
  rw [lagrange]
  have hP : dot o.toPerigee o.toPerigee = 1 := by unfold dot; nlinarith [f.unitP]
  have hQ : dot o.ahead o.ahead = 1 := by unfold dot; nlinarith [f.unitQ]
  have hO : dot o.toPerigee o.ahead = 0 := f.orth
  rw [hP, hQ, hO]
  ring

theorem radial_normal (mu : ℝ) (o : Orbit) (t : ℝ) : dot (radial mu o t) (normal o) = 0 := by
  unfold radial unit3 normal Orbit.position Orbit.path dot cross
  simp only
  ring

/-- **M2.**  The frame `(R̂, Ŝ, Ŵ)` is orthonormal, so a vector fixed in it keeps the length of its
components. -/
theorem rsw_norm {o : Orbit} (hv : o.Valid) (mu : ℝ) (b : V3) (t : ℝ) :
    norm3 (rsw mu o b t) = norm3 b := by
  have hr0 : 0 < norm3 (o.position mu t) :=
    (perigee_pos hv).trans_le (position_radius hv mu t).1
  have hRR : dot (radial mu o t) (radial mu o t) = 1 := dot_unit hr0
  have hWW := normal_unit o
  have hRW := radial_normal mu o t
  unfold rsw along
  generalize radial mu o t = R at hRR hRW ⊢
  generalize normal o = W at hWW hRW ⊢
  have hSS : dot (cross W R) (cross W R) = 1 := by
    rw [lagrange, hRR, hWW, show dot W R = dot R W by unfold dot; ring, hRW]; ring
  have hSR : dot (cross W R) R = 0 := by unfold dot cross; ring
  have hSW : dot (cross W R) W = 0 := by unfold dot cross; ring
  unfold norm3
  apply congrArg Real.sqrt
  generalize cross W R = S at hSS hSR hSW
  unfold dot at hRR hWW hRW hSS hSR hSW
  unfold add3 smul3
  simp only
  linear_combination b.1 ^ 2 * hRR + b.2.1 ^ 2 * hSS + b.2.2 ^ 2 * hWW +
    2 * b.1 * b.2.1 * hSR + 2 * b.1 * b.2.2 * hRW + 2 * b.2.1 * b.2.2 * hSW

/-! ### M3: rates -/

/-- The shadow's functions: `r · s`, and `|r × s| cos α + (r · s) sin α - R`. -/
noncomputable def shadowG2 (ca sa R : ℝ) (r s : V3) : ℝ :=
  norm3 (cross r s) * ca + dot r s * sa - R

theorem inShadow_iff (α R : ℝ) (r s : V3) :
    InShadow α R r s ↔ dot r s ≤ 0 ∧ shadowG2 (cos (rad α)) (sin (rad α)) R r s ≤ 0 := by
  unfold InShadow shadowG2
  constructor
  · rintro ⟨a, b⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨a, b⟩; exact ⟨by linarith, by linarith⟩

/-- The rate bound of the shadow's first function, `V + r⁺ ω`, in km per minute. -/
noncomputable def shadowRate (mu : ℝ) (o : Orbit) : ℝ :=
  o.speed mu + o.a * (1 + o.e) * (sunRate / 1440)

section Rates

variable {mu : ℝ} {o : Orbit}

theorem position_change (hv : o.Valid) (t t' : ℝ) :
    norm3 (sub3 (o.position mu t) (o.position mu t')) ≤ o.speed mu * |t - t'| := by
  rw [← dist3_eq]
  exact position_lipschitz hv t t'

theorem shadowRate_nonneg (hv : o.Valid) : 0 ≤ shadowRate mu o := by
  unfold shadowRate
  have := speed_nonneg (mu := mu) hv
  have := hv.1
  have := hv.2.1
  have := sunRate_nonneg
  positivity

/-- The change of `r · s` and of `|r × s|` between two times. -/
theorem pair_change (hv : o.Valid) (d0 t t' : ℝ) :
    norm3 (sub3 (o.position mu t) (o.position mu t')) * norm3 (sunAt d0 t) +
        norm3 (o.position mu t') * norm3 (sub3 (sunAt d0 t) (sunAt d0 t')) ≤
      shadowRate mu o * |t - t'| := by
  rw [sunAt_unit, mul_one]
  have h1 := position_change (mu := mu) hv t t'
  have h2 := sunAt_lipschitz d0 t t'
  have h3 := (position_radius hv mu t').2
  have h4 : 0 ≤ norm3 (o.position mu t') := norm3_nonneg _
  have h5 : 0 ≤ norm3 (sub3 (sunAt d0 t) (sunAt d0 t')) := norm3_nonneg _
  have h6 : 0 ≤ sunRate / 1440 * |t - t'| := by have := sunRate_nonneg; positivity
  unfold shadowRate
  nlinarith [mul_le_mul h3 h2 h5 (by nlinarith [hv.1, hv.2.1] : 0 ≤ o.a * (1 + o.e))]

/-- **M3.**  `r · s` changes at most at the rate `V + r⁺ ω`. -/
theorem shadow1_lipschitz (hv : o.Valid) (d0 t t' : ℝ) :
    |dot (o.position mu t) (sunAt d0 t) - dot (o.position mu t') (sunAt d0 t')| ≤
      shadowRate mu o * |t - t'| :=
  (dot_change _ _ _ _).trans (pair_change hv d0 t t')

/-- **M3.**  The shadow's second function changes at most at the rate
`(|cos α| + |sin α|) (V + r⁺ ω)`. -/
theorem shadow2_lipschitz (hv : o.Valid) (d0 ca sa R t t' : ℝ) :
    |shadowG2 ca sa R (o.position mu t) (sunAt d0 t) -
        shadowG2 ca sa R (o.position mu t') (sunAt d0 t')| ≤
      (|ca| + |sa|) * shadowRate mu o * |t - t'| := by
  have hy := (cross_change (o.position mu t) (sunAt d0 t) (o.position mu t') (sunAt d0 t')).trans
    (pair_change hv d0 t t')
  have hx := shadow1_lipschitz (mu := mu) hv d0 t t'
  have e : shadowG2 ca sa R (o.position mu t) (sunAt d0 t) -
      shadowG2 ca sa R (o.position mu t') (sunAt d0 t') =
      ca * (norm3 (cross (o.position mu t) (sunAt d0 t)) -
        norm3 (cross (o.position mu t') (sunAt d0 t'))) +
      sa * (dot (o.position mu t) (sunAt d0 t) - dot (o.position mu t') (sunAt d0 t')) := by
    unfold shadowG2; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hy (abs_nonneg ca),
    mul_le_mul_of_nonneg_left hx (abs_nonneg sa)]

/-- A position `ρ` within `δ` of `r` changes `r · s` by at most `δ` and the shadow's second
function by at most `(|cos α| + |sin α|) δ`. -/
theorem shadow_near (ca sa R : ℝ) {r ρ s : V3} (hs : norm3 s = 1) {δ : ℝ}
    (h : norm3 (sub3 ρ r) ≤ δ) :
    |dot ρ s - dot r s| ≤ δ ∧ |shadowG2 ca sa R ρ s - shadowG2 ca sa R r s| ≤ (|ca| + |sa|) * δ := by
  have z : norm3 (sub3 s s) = 0 := by unfold norm3 sub3; simp
  have hx := dot_change ρ s r s
  have hy := cross_change ρ s r s
  rw [z, hs, mul_one, mul_zero, add_zero] at hx hy
  have hx' := hx.trans h
  have hy' := hy.trans h
  refine ⟨hx', ?_⟩
  have e : shadowG2 ca sa R ρ s - shadowG2 ca sa R r s =
      ca * (norm3 (cross ρ s) - norm3 (cross r s)) + sa * (dot ρ s - dot r s) := by
    unfold shadowG2; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [mul_le_mul_of_nonneg_left hy' (abs_nonneg ca),
    mul_le_mul_of_nonneg_left hx' (abs_nonneg sa)]

/-- The function of the exclusion events: `|b| cos β - v · s`. -/
noncomputable def vectorG (nb cb : ℝ) (v s : V3) : ℝ := nb * cb - dot v s

theorem within_iff {v s : V3} {nb : ℝ} (hv : norm3 v = nb) (hs : norm3 s = 1) (β : ℝ) :
    Within v s β ↔ vectorG nb (cos (rad β)) v s ≤ 0 := by
  unfold Within vectorG
  rw [hv, hs, mul_one]
  constructor <;> intro h <;> linarith

/-- **M3.**  For an inertial vector, `|b| cos β - b · s` changes at most at the rate `|b| ω`. -/
theorem inertial_lipschitz (b : V3) (cb d0 t t' : ℝ) :
    |vectorG (norm3 b) cb b (sunAt d0 t) - vectorG (norm3 b) cb b (sunAt d0 t')| ≤
      norm3 b * (sunRate / 1440) * |t - t'| := by
  have e : vectorG (norm3 b) cb b (sunAt d0 t) - vectorG (norm3 b) cb b (sunAt d0 t') =
      -(dot b (sunAt d0 t) - dot b (sunAt d0 t')) := by unfold vectorG; ring
  rw [e, abs_neg]
  have h := dot_change b (sunAt d0 t) b (sunAt d0 t')
  have z : sub3 b b = (0, 0, 0) := by unfold sub3; simp
  rw [z, show norm3 ((0, 0, 0) : V3) = 0 by unfold norm3; simp, zero_mul, zero_add] at h
  refine h.trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (sunAt_lipschitz d0 t t') (norm3_nonneg b)

/-- The rate of the radial direction in radians per minute, `V / (a (1 - e))`. -/
noncomputable def turnRate (mu : ℝ) (o : Orbit) : ℝ := o.speed mu / (o.a * (1 - o.e))

theorem radial_change (hv : o.Valid) (t t' : ℝ) :
    norm3 (sub3 (radial mu o t) (radial mu o t')) ≤ turnRate mu o * |t - t'| := by
  refine (unit_change (perigee_pos hv) (position_radius hv mu t).1
    (position_radius hv mu t').1).trans ?_
  rw [turnRate, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (position_change hv t t') (perigee_pos hv).le

/-- The rate bound of the exclusion event of a vector in the orbit's frame. -/
noncomputable def rswRate (mu : ℝ) (o : Orbit) (b : V3) : ℝ :=
  (|b.1| + |b.2.1|) * turnRate mu o + norm3 b * (sunRate / 1440)

theorem rsw_change (b : V3) (t t' : ℝ) :
    norm3 (sub3 (rsw mu o b t) (rsw mu o b t')) ≤
      (|b.1| + |b.2.1|) * norm3 (sub3 (radial mu o t) (radial mu o t')) := by
  have e : sub3 (rsw mu o b t) (rsw mu o b t') =
      add3 (smul3 b.1 (sub3 (radial mu o t) (radial mu o t')))
        (smul3 b.2.1 (cross (normal o) (sub3 (radial mu o t) (radial mu o t')))) := by
    unfold rsw along sub3 add3 smul3 cross
    ext <;> simp only <;> ring
  rw [e]
  refine (norm3_add_le _ _).trans ?_
  rw [norm3_smul, norm3_smul]
  have hc := norm3_cross_le (normal o) (sub3 (radial mu o t) (radial mu o t'))
  rw [norm3_eq_one (normal_unit o), one_mul] at hc
  nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg b.2.1)]

/-- **M3.**  For a vector in the orbit's frame, `|b| cos β - v · s` changes at most at the rate
`(|b₁| + |b₂|) V / (a (1 - e)) + |b| ω`. -/
theorem rsw_lipschitz (hv : o.Valid) (b : V3) (cb d0 t t' : ℝ) :
    |vectorG (norm3 b) cb (rsw mu o b t) (sunAt d0 t) -
        vectorG (norm3 b) cb (rsw mu o b t') (sunAt d0 t')| ≤ rswRate mu o b * |t - t'| := by
  have e : vectorG (norm3 b) cb (rsw mu o b t) (sunAt d0 t) -
      vectorG (norm3 b) cb (rsw mu o b t') (sunAt d0 t') =
      -(dot (rsw mu o b t) (sunAt d0 t) - dot (rsw mu o b t') (sunAt d0 t')) := by
    unfold vectorG; ring
  rw [e, abs_neg]
  refine (dot_change _ _ _ _).trans ?_
  rw [sunAt_unit, mul_one, rsw_norm hv]
  have h1 := (rsw_change (mu := mu) (o := o) b t t').trans (mul_le_mul_of_nonneg_left
    (radial_change hv t t') (by positivity))
  have h2 := mul_le_mul_of_nonneg_left (sunAt_lipschitz d0 t t') (norm3_nonneg b)
  unfold rswRate
  nlinarith

end Rates

end Demos.Events
