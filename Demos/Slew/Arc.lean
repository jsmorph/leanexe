import Demos.Slew.Spec
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! The arc lemmas of the edge check.  During a rotation by `φ` about the axis `n`, the cosine
between a body vector `v` and a cone axis `u` is `A cos φ + B sin φ + C` (`dot_rod`).  On `[0, θ]`
with `θ ≤ π`, if `f′(0) = B ≤ 0` or `f′(θ) = B cos θ - A sin θ ≥ 0`, the sinusoid's maximum lies
at an endpoint (`endpoint_max`), and in every case it is at most `√(A² + B²)` (`sinusoid_le`).
The proof of the endpoint case applies the mean value theorem twice and the identity
`sin (β - α) p(γ) = sin (β - γ) p(α) + sin (γ - α) p(β)` for a sinusoid `p` (`interpolate`), which
keeps the sign of `p` between two points of the same sign less than `π` apart.  The vector lemmas
give Cauchy–Schwarz, the tube bound, the displacement of a small rotation, and the scaling of the
formulas, which relates normalized inputs to the program's unnormalized ones. -/

namespace Demos.Slew.Arc

open Demos.Slew.Spec Vec Real

/-! ### Sinusoids -/

/-- The cosine of a rotated vector with an axis, in the form `A cos φ + B sin φ + C`. -/
theorem dot_rod (u n v : Vec) (φ : ℝ) :
    dot u (rod n φ v) = (dot u v - dot n u * dot n v) * cos φ + dot u (cross n v) * sin φ +
      dot n u * dot n v := by
  simp only [rod, dot, cross]
  ring

theorem sinusoid_sq_le (A B φ : ℝ) : (A * cos φ + B * sin φ) ^ 2 ≤ A ^ 2 + B ^ 2 := by
  nlinarith [sq_nonneg (A * sin φ - B * cos φ), sin_sq_add_cos_sq φ]

theorem sinusoid_le (A B φ : ℝ) : A * cos φ + B * sin φ ≤ √(A ^ 2 + B ^ 2) :=
  (le_abs_self _).trans (Real.abs_le_sqrt (sinusoid_sq_le A B φ))

theorem neg_sinusoid_le (A B φ : ℝ) : -√(A ^ 2 + B ^ 2) ≤ A * cos φ + B * sin φ := by
  have h := Real.abs_le_sqrt (sinusoid_sq_le A B φ)
  linarith [neg_abs_le (A * cos φ + B * sin φ)]

/-- Three values of a sinusoid at `α`, `β`, and `γ`. -/
theorem interpolate (P Q α β γ : ℝ) :
    sin (β - α) * (P * cos γ + Q * sin γ) =
      sin (β - γ) * (P * cos α + Q * sin α) + sin (γ - α) * (P * cos β + Q * sin β) := by
  simp only [sin_sub]
  ring

theorem hasDerivAt_sinusoid (A B t : ℝ) :
    HasDerivAt (fun t => A * cos t + B * sin t) (B * cos t - A * sin t) t := by
  have h := ((hasDerivAt_cos t).const_mul A).add ((hasDerivAt_sin t).const_mul B)
  have e : B * cos t - A * sin t = A * -sin t + B * cos t := by ring
  rw [e]
  exact h

theorem continuous_sinusoid (A B : ℝ) : Continuous fun t => A * cos t + B * sin t :=
  (continuous_const.mul continuous_cos).add (continuous_const.mul continuous_sin)

/-- On `[0, θ]` with `θ ≤ π`, a sinusoid whose derivative is not positive at `0` or not negative
at `θ` takes its maximum at an endpoint. -/
theorem endpoint_max (A B θ : ℝ) (hθ : θ ≤ π)
    (h : B ≤ 0 ∨ 0 ≤ B * cos θ - A * sin θ) (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ : φ ≤ θ) :
    A * cos φ + B * sin φ ≤ max A (A * cos θ + B * sin θ) := by
  set g : ℝ → ℝ := fun t => A * cos t + B * sin t with hg
  by_contra hcon
  push Not at hcon
  have hg0 : g 0 = A := by simp [hg]
  have h0 : g 0 < g φ := by rw [hg0]; exact lt_of_le_of_lt (le_max_left _ _) hcon
  have hθφ : g θ < g φ := lt_of_le_of_lt (le_max_right _ _) hcon
  have hφpos : 0 < φ := by
    rcases eq_or_lt_of_le hφ0 with e | e
    · subst e; exact absurd h0 (lt_irrefl _)
    · exact e
  have hφθ : φ < θ := by
    rcases eq_or_lt_of_le hφ with e | e
    · rw [e] at h0 hθφ; exact absurd hθφ (lt_irrefl _)
    · exact e
  have hc := (continuous_sinusoid A B).continuousOn (s := Set.Icc 0 φ)
  have hc' := (continuous_sinusoid A B).continuousOn (s := Set.Icc φ θ)
  obtain ⟨α, ⟨hα0, hαφ⟩, hαd⟩ := exists_hasDerivAt_eq_slope g (fun t => B * cos t - A * sin t)
    hφpos hc (fun t _ => hasDerivAt_sinusoid A B t)
  obtain ⟨β, ⟨hφβ, hβθ⟩, hβd⟩ := exists_hasDerivAt_eq_slope g (fun t => B * cos t - A * sin t)
    hφθ hc' (fun t _ => hasDerivAt_sinusoid A B t)
  have hpα : 0 < B * cos α - A * sin α := by
    rw [hαd]; exact div_pos (by linarith) (by linarith)
  have hpβ : B * cos β - A * sin β < 0 := by
    rw [hβd]; exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  rcases h with hB | hT
  · have key := interpolate B (-A) 0 β α
    have s1 : 0 < sin β := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have s2 : 0 ≤ sin (β - α) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have s3 : 0 < sin α := sin_pos_of_pos_of_lt_pi hα0 (by linarith)
    simp only [sub_zero, cos_zero, sin_zero, mul_one, mul_zero, add_zero] at key
    have l : 0 < sin β * (B * cos α + -A * sin α) := mul_pos s1 (by linarith)
    have r1 : sin (β - α) * B ≤ 0 := mul_nonpos_of_nonneg_of_nonpos s2 hB
    have r2 : sin α * (B * cos β + -A * sin β) < 0 := mul_neg_of_pos_of_neg s3 (by linarith)
    linarith
  · have key := interpolate B (-A) α θ β
    have s1 : 0 < sin (θ - α) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have s2 : 0 ≤ sin (θ - β) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have s3 : 0 ≤ sin (β - α) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have l : sin (θ - α) * (B * cos β + -A * sin β) < 0 := mul_neg_of_pos_of_neg s1 (by linarith)
    have r1 : 0 ≤ sin (θ - β) * (B * cos α + -A * sin α) := mul_nonneg s2 (by linarith)
    have r2 : 0 ≤ sin (β - α) * (B * cos θ + -A * sin θ) := mul_nonneg s3 (by linarith)
    linarith

/-- The minimum counterpart of `endpoint_max`. -/
theorem endpoint_min (A B θ : ℝ) (hθ : θ ≤ π)
    (h : 0 ≤ B ∨ B * cos θ - A * sin θ ≤ 0) (φ : ℝ) (hφ0 : 0 ≤ φ) (hφ : φ ≤ θ) :
    min A (A * cos θ + B * sin θ) ≤ A * cos φ + B * sin φ := by
  have h' : -B ≤ 0 ∨ 0 ≤ -B * cos θ - -A * sin θ := by
    rcases h with h | h
    · left; linarith
    · right; linarith
  have hm := endpoint_max (-A) (-B) θ hθ h' φ hφ0 hφ
  rcases le_max_iff.mp hm with e | e
  · exact min_le_of_left_le (by linarith)
  · exact min_le_of_right_le (by linarith)

/-! ### The rotation angle of a relative quaternion -/

theorem angle_nonneg (w s : ℝ) : 0 ≤ angle w s := arccos_nonneg _

theorem angle_le_pi (w s : ℝ) : angle w s ≤ π := arccos_le_pi _

theorem cos_angle (w s : ℝ) (hpos : 0 < w * w + s * s) :
    cos (angle w s) = (w * w - s * s) / (w * w + s * s) := by
  apply cos_arccos
  · rw [le_div_iff₀ hpos]; nlinarith [mul_self_nonneg w]
  · rw [div_le_one hpos]; nlinarith [mul_self_nonneg s]

theorem sin_angle (w s : ℝ) (hw : 0 ≤ w) (hs : 0 ≤ s) (hpos : 0 < w * w + s * s) :
    sin (angle w s) = 2 * w * s / (w * w + s * s) := by
  unfold angle
  rw [sin_arccos]
  have hne : (w * w + s * s) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hpos)
  have e : 1 - ((w * w - s * s) / (w * w + s * s)) ^ 2 = (2 * w * s / (w * w + s * s)) ^ 2 := by
    rw [div_pow, div_pow, one_sub_div hne]
    congr 1
    ring
  rw [e, Real.sqrt_sq (by positivity)]

/-! ### Vectors -/

theorem dot_comm (a b : Vec) : dot a b = dot b a := by simp only [dot]; ring

theorem dot_self_nonneg (a : Vec) : 0 ≤ dot a a := by
  simp only [dot]; nlinarith [mul_self_nonneg a.x, mul_self_nonneg a.y, mul_self_nonneg a.z]

theorem dot_sq_le (a b : Vec) : dot a b ^ 2 ≤ dot a a * dot b b := by
  simp only [dot]
  nlinarith [sq_nonneg (a.y * b.z - a.z * b.y), sq_nonneg (a.z * b.x - a.x * b.z),
    sq_nonneg (a.x * b.y - a.y * b.x)]

theorem norm_nonneg (a : Vec) : 0 ≤ norm a := Real.sqrt_nonneg _

theorem abs_dot_le (a b : Vec) : |dot a b| ≤ norm a * norm b := by
  rw [Vec.norm, Vec.norm, ← Real.sqrt_mul (dot_self_nonneg a)]
  exact Real.abs_le_sqrt (dot_sq_le a b)

theorem dot_sub (u a b : Vec) : dot u (sub a b) = dot u a - dot u b := by
  simp only [dot, sub]; ring

/-- A vector within `r` of `P` has a cosine with the unit axis `u` within `r` of `P`'s. -/
theorem near_bounds (u P v : Vec) (r : ℝ) (hu : norm u = 1) (h : norm (sub v P) ≤ r) :
    dot u v ≤ dot u P + r ∧ dot u P - r ≤ dot u v := by
  have e := abs_dot_le u (sub v P)
  rw [hu, one_mul, dot_sub] at e
  have := abs_le.mp (e.trans h)
  constructor <;> linarith [this.1, this.2]

/-- For a unit axis `n`, `A² + B²` is the product of the squared lengths of `u` and `v` across
`n`. -/
theorem sinusoid_sq_eq (u n v : Vec) (hn : dot n n = 1) :
    (dot u v - dot n u * dot n v) ^ 2 + dot u (cross n v) ^ 2 =
      (dot u u - dot n u ^ 2) * (dot v v - dot n v ^ 2) := by
  simp only [dot, cross] at hn ⊢
  linear_combination ((u.x * u.x + u.y * u.y + u.z * u.z) * (v.x * v.x + v.y * v.y + v.z * v.z) -
    (u.x * v.x + u.y * v.y + u.z * v.z) ^ 2) * hn

theorem sinusoid_sq_le_norms (u n v : Vec) (hn : dot n n = 1) :
    (dot u v - dot n u * dot n v) ^ 2 + dot u (cross n v) ^ 2 ≤ dot u u * dot v v := by
  rw [sinusoid_sq_eq u n v hn]
  have hu := dot_sq_le n u
  have hv := dot_sq_le n v
  rw [hn, one_mul] at hu hv
  have hu0 : 0 ≤ dot u u - dot n u ^ 2 := by linarith
  have hv0 : 0 ≤ dot v v - dot n v ^ 2 := by linarith
  nlinarith [sq_nonneg (dot n u), sq_nonneg (dot n v), dot_self_nonneg u, dot_self_nonneg v]

theorem sinusoid_amplitude_le (u n v : Vec) (hn : dot n n = 1) :
    √((dot u v - dot n u * dot n v) ^ 2 + dot u (cross n v) ^ 2) ≤ norm u * norm v := by
  rw [Vec.norm, Vec.norm, ← Real.sqrt_mul (dot_self_nonneg u)]
  exact Real.sqrt_le_sqrt (sinusoid_sq_le_norms u n v hn)

/-- A rotation by `φ` about a unit axis changes the cosine of `v` with `u` by at most
`‖u‖ ‖v‖ √(2 - 2 cos φ)`. -/
theorem dot_rod_sub_le (u n v : Vec) (hn : dot n n = 1) (φ : ℝ) :
    |dot u (rod n φ v) - dot u v| ≤ norm u * norm v * √(2 - 2 * cos φ) := by
  set A := dot u v - dot n u * dot n v
  set B := dot u (cross n v)
  have e : dot u (rod n φ v) - dot u v = A * (cos φ - 1) + B * sin φ := by
    rw [dot_rod]; simp only [A, B]; ring
  rw [e]
  have hcs : (A * (cos φ - 1) + B * sin φ) ^ 2 ≤ (A ^ 2 + B ^ 2) * (2 - 2 * cos φ) := by
    nlinarith [sq_nonneg (A * sin φ - B * (cos φ - 1)), sin_sq_add_cos_sq φ]
  have h2 : 0 ≤ 2 - 2 * cos φ := by linarith [cos_le_one φ]
  calc |A * (cos φ - 1) + B * sin φ| ≤ √((A ^ 2 + B ^ 2) * (2 - 2 * cos φ)) :=
        Real.abs_le_sqrt hcs
    _ = √(A ^ 2 + B ^ 2) * √(2 - 2 * cos φ) := Real.sqrt_mul (by positivity) _
    _ ≤ norm u * norm v * √(2 - 2 * cos φ) :=
        mul_le_mul_of_nonneg_right (sinusoid_amplitude_le u n v hn) (Real.sqrt_nonneg _)

/-- The cosine along a rotation about a unit axis is at most `2 ‖u‖ ‖v‖` in magnitude. -/
theorem abs_dot_rod_le (u n v : Vec) (hn : dot n n = 1) (φ : ℝ) :
    |dot u (rod n φ v)| ≤ 2 * (norm u * norm v) := by
  rw [dot_rod]
  have h1 := Real.abs_le_sqrt (sinusoid_sq_le (dot u v - dot n u * dot n v) (dot u (cross n v)) φ)
  have h2 := sinusoid_amplitude_le u n v hn
  have h3 : |dot n u * dot n v| ≤ norm u * norm v := by
    rw [abs_mul]
    have a := abs_dot_le n u
    have b := abs_dot_le n v
    have hn1 : norm n = 1 := by rw [Vec.norm, hn, Real.sqrt_one]
    rw [hn1, one_mul] at a b
    exact mul_le_mul a b (abs_nonneg _) (norm_nonneg u)
  calc |(dot u v - dot n u * dot n v) * cos φ + dot u (cross n v) * sin φ + dot n u * dot n v|
      ≤ |(dot u v - dot n u * dot n v) * cos φ + dot u (cross n v) * sin φ| +
          |dot n u * dot n v| := abs_add_le _ _
    _ ≤ norm u * norm v + norm u * norm v := add_le_add (h1.trans h2) h3
    _ = 2 * (norm u * norm v) := by ring

/-! ### Scaling -/

theorem dot_smul_left (k : ℝ) (a b : Vec) : dot (smul k a) b = k * dot a b := by
  simp only [dot, smul]; ring

theorem rod_smul (n : Vec) (φ k : ℝ) (v : Vec) : rod n φ (smul k v) = smul k (rod n φ v) := by
  ext <;> simp only [rod, smul, dot, cross] <;> ring

theorem rot_smul_right (q : Quat) (k : ℝ) (v : Vec) :
    Quat.rot q (smul k v) = smul k (Quat.rot q v) := by
  ext <;> simp only [Quat.rot, smul] <;> ring

theorem rot_sub (q : Quat) (a b : Vec) : Quat.rot q (sub a b) = sub (Quat.rot q a) (Quat.rot q b) := by
  ext <;> simp only [Quat.rot, sub] <;> ring

theorem rod_sub (n : Vec) (φ : ℝ) (a b : Vec) : rod n φ (sub a b) = sub (rod n φ a) (rod n φ b) := by
  ext <;> simp only [rod, sub, dot, cross] <;> ring

/-- Scaling the quaternion by `k` scales the displacement `rot q v - v` by `k²`. -/
theorem rot_smul_left (q : Quat) (k : ℝ) (v : Vec) :
    sub (Quat.rot (Quat.smul k q) v) v = smul (k * k) (sub (Quat.rot q v) v) := by
  ext <;> simp only [Quat.rot, Quat.smul, smul, sub] <;> ring

/-- The rotation formula keeps lengths for a unit quaternion. -/
theorem dot_rot_self (q : Quat) (v : Vec) (hq : Quat.norm2 q = 1) :
    dot (Quat.rot q v) (Quat.rot q v) = dot v v := by
  simp only [dot, Quat.rot, Quat.norm2] at hq ⊢
  linear_combination (4 * ((q.x * q.x + q.y * q.y + q.z * q.z) * (v.x * v.x + v.y * v.y + v.z * v.z) -
    (q.x * v.x + q.y * v.y + q.z * v.z) ^ 2)) * hq

/-- Rodrigues' formula keeps lengths for a unit axis. -/
theorem dot_rod_self (n : Vec) (φ : ℝ) (v : Vec) (hn : dot n n = 1) :
    dot (rod n φ v) (rod n φ v) = dot v v := by
  have hp := sin_sq_add_cos_sq φ
  simp only [dot, rod, cross] at hn ⊢
  linear_combination (sin φ ^ 2 * (v.x * v.x + v.y * v.y + v.z * v.z) +
      (n.x * v.x + n.y * v.y + n.z * v.z) ^ 2 * (1 - cos φ) ^ 2) * hn +
    ((v.x * v.x + v.y * v.y + v.z * v.z) - (n.x * v.x + n.y * v.y + n.z * v.z) ^ 2) * hp

theorem norm_smul (k : ℝ) (a : Vec) : norm (smul k a) = |k| * norm a := by
  rw [Vec.norm, Vec.norm, dot_smul_left]
  have : dot a (smul k a) = k * dot a a := by simp only [dot, smul]; ring
  rw [this, ← mul_assoc, Real.sqrt_mul (mul_self_nonneg k), Real.sqrt_mul_self_eq_abs]

theorem norm_unit (a : Vec) (h : 0 < norm a) : norm (unit a) = 1 := by
  rw [unit, norm_smul, abs_of_pos (by positivity)]
  field_simp

end Demos.Slew.Arc
