import Demos.Frames.Model
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
Geodetic coordinates over the real numbers.  The latitude of a point solves
`k(u) = p u − z − c u/√(1 + m u²) = 0` in `u = tan φ`, and for `z > 0` also
`ℓ(v) = z v + c v/√(v² + m) − p = 0` in `v = cot φ`, with `c = a e²` and `m = 1 − e²`.  `k` rises
with slope at least `p − c` and `ℓ` with slope at least `z`, so each has exactly one root when its
slope bound is positive, and every argument lies within the residual over the slope bound of the
root (`rootA_bound`, `rootB_bound`).  `exists_geodetic` builds geodetic coordinates from a root and
a longitude, and `geodetic_unique` shows that every point of the domain `D` has at most one
latitude and height, and one longitude modulo `2π`.
-/

open Real Filter

namespace Demos.Frames.Geodetic

open Model

/-! ### The two equations of the latitude -/

/-- The equation of the latitude in `u = tan φ`. -/
noncomputable def kA (c m p z u : ℝ) : ℝ := p * u - z - c * u / √(1 + m * u ^ 2)

/-- The equation of the latitude in `v = cot φ`. -/
noncomputable def lB (c m p z v : ℝ) : ℝ := z * v + c * v / √(v ^ 2 + m) - p

theorem one_le_sqrt {m : ℝ} (hm : 0 ≤ m) (s : ℝ) : 1 ≤ √(1 + m * s ^ 2) := by
  have h : (1 : ℝ) ≤ 1 + m * s ^ 2 := by nlinarith [mul_nonneg hm (sq_nonneg s)]
  calc (1 : ℝ) = √1 := Real.sqrt_one.symm
    _ ≤ √(1 + m * s ^ 2) := Real.sqrt_le_sqrt h

/-- `u − u/√(1 + m u²)` increases. -/
theorem lag_mono {m : ℝ} (hm : 0 ≤ m) {u₁ u₂ : ℝ} (h : u₁ ≤ u₂) :
    u₁ - u₁ / √(1 + m * u₁ ^ 2) ≤ u₂ - u₂ / √(1 + m * u₂ ^ 2) := by
  have h1 := one_le_sqrt hm u₁
  have h2 := one_le_sqrt hm u₂
  set A₁ := √(1 + m * u₁ ^ 2)
  set A₂ := √(1 + m * u₂ ^ 2)
  have e₁ : u₁ - u₁ / A₁ = u₁ * (1 - 1 / A₁) := by field_simp
  have e₂ : u₂ - u₂ / A₂ = u₂ * (1 - 1 / A₂) := by field_simp
  rw [e₁, e₂]
  have r₁ : 0 ≤ 1 - 1 / A₁ := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact h1
  have r₂ : 0 ≤ 1 - 1 / A₂ := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact h2
  rcases le_total 0 u₁ with hu₁ | hu₁
  · have hsq : u₁ ^ 2 ≤ u₂ ^ 2 := pow_le_pow_left₀ hu₁ h 2
    have hA : A₁ ≤ A₂ := Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hsq hm])
    have hr : 1 - 1 / A₁ ≤ 1 - 1 / A₂ := by
      have := one_div_le_one_div_of_le (by linarith) hA
      linarith
    nlinarith [mul_nonneg (sub_nonneg.2 h) r₁, mul_nonneg (hu₁.trans h) (sub_nonneg.2 hr)]
  · rcases le_total u₂ 0 with hu₂ | hu₂
    · have hsq : u₂ ^ 2 ≤ u₁ ^ 2 := by
        have := pow_le_pow_left₀ (neg_nonneg.2 hu₂) (neg_le_neg h) 2
        rwa [neg_sq, neg_sq] at this
      have hA : A₂ ≤ A₁ := Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hsq hm])
      have hr : 1 - 1 / A₂ ≤ 1 - 1 / A₁ := by
        have := one_div_le_one_div_of_le (by linarith) hA
        linarith
      nlinarith [mul_nonneg (sub_nonneg.2 h) r₂, mul_nonneg (neg_nonneg.2 (h.trans hu₂))
        (sub_nonneg.2 hr)]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hu₁ r₁, mul_nonneg hu₂ r₂]

/-- `v/√(v² + m)` increases for `m > 0`. -/
theorem ratio_mono {m : ℝ} (hm : 0 < m) {v₁ v₂ : ℝ} (h : v₁ ≤ v₂) :
    v₁ / √(v₁ ^ 2 + m) ≤ v₂ / √(v₂ ^ 2 + m) := by
  have b₁ : 0 < √(v₁ ^ 2 + m) := Real.sqrt_pos.2 (by positivity)
  have b₂ : 0 < √(v₂ ^ 2 + m) := Real.sqrt_pos.2 (by positivity)
  have q₁ := Real.sq_sqrt (show 0 ≤ v₁ ^ 2 + m by positivity)
  have q₂ := Real.sq_sqrt (show 0 ≤ v₂ ^ 2 + m by positivity)
  rw [div_le_div_iff₀ b₁ b₂]
  rcases le_total 0 v₁ with hv₁ | hv₁
  · have hv₂ := hv₁.trans h
    have hs : (v₁ * √(v₂ ^ 2 + m)) ^ 2 ≤ (v₂ * √(v₁ ^ 2 + m)) ^ 2 := by
      rw [mul_pow, mul_pow, q₁, q₂]; nlinarith [mul_le_mul h h hv₁ hv₂]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hs
  · rcases le_total v₂ 0 with hv₂ | hv₂
    · have hs : (v₂ * √(v₁ ^ 2 + m)) ^ 2 ≤ (v₁ * √(v₂ ^ 2 + m)) ^ 2 := by
        rw [mul_pow, mul_pow, q₁, q₂]
        nlinarith [mul_le_mul (neg_le_neg h) (neg_le_neg h) (neg_nonneg.2 hv₂)
          (neg_nonneg.2 hv₁)]
      have := (pow_le_pow_iff_left₀ (by nlinarith) (by nlinarith) two_ne_zero).1
        (show (-(v₂ * √(v₁ ^ 2 + m))) ^ 2 ≤ (-(v₁ * √(v₂ ^ 2 + m))) ^ 2 by
          rw [neg_sq, neg_sq]; exact hs)
      linarith
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hv₁ b₂.le, mul_nonneg hv₂ b₁.le]

/-- `k` rises by at least `(p − c)` times the distance. -/
theorem growthA {c m : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m) (p z : ℝ) {u₁ u₂ : ℝ} (h : u₁ ≤ u₂) :
    (p - c) * (u₂ - u₁) ≤ kA c m p z u₂ - kA c m p z u₁ := by
  have := lag_mono hm h
  unfold kA
  have e : ∀ u, c * u / √(1 + m * u ^ 2) = c * (u / √(1 + m * u ^ 2)) := fun u => by ring
  rw [e, e]
  nlinarith [mul_le_mul_of_nonneg_left this hc]

/-- `ℓ` rises by at least `z` times the distance. -/
theorem growthB {c m : ℝ} (hc : 0 ≤ c) (hm : 0 < m) (p z : ℝ) {v₁ v₂ : ℝ} (h : v₁ ≤ v₂) :
    z * (v₂ - v₁) ≤ lB c m p z v₂ - lB c m p z v₁ := by
  have := ratio_mono hm h
  unfold lB
  have e : ∀ v, c * v / √(v ^ 2 + m) = c * (v / √(v ^ 2 + m)) := fun v => by ring
  rw [e, e]
  nlinarith [mul_le_mul_of_nonneg_left this hc]

/-! ### Roots -/

theorem continuous_kA {c m : ℝ} (hm : 0 ≤ m) (p z : ℝ) : Continuous (kA c m p z) := by
  unfold kA
  refine (by fun_prop : Continuous fun u => p * u - z).sub
    ((by fun_prop : Continuous fun u => c * u).div (by fun_prop) fun u => ?_)
  exact (lt_of_lt_of_le one_pos (one_le_sqrt hm u)).ne'

theorem continuous_lB {c m : ℝ} (hm : 0 < m) (p z : ℝ) : Continuous (lB c m p z) := by
  unfold lB
  refine ((by fun_prop : Continuous fun v => z * v).add
    ((by fun_prop : Continuous fun v => c * v).div (by fun_prop) fun v => ?_)).sub
    continuous_const
  exact (Real.sqrt_pos.2 (by positivity)).ne'

/-- A continuous function that rises with a positive slope bound takes every value once. -/
theorem bijective_of_growth {g : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hg : Continuous g)
    (h : ∀ x₁ x₂, x₁ ≤ x₂ → s * (x₂ - x₁) ≤ g x₂ - g x₁) : Function.Bijective g := by
  refine ⟨fun x₁ x₂ he => ?_, hg.surjective ?_ ?_⟩
  · rcases le_total x₁ x₂ with hl | hl
    · have := h x₁ x₂ hl
      rw [he, sub_self] at this
      nlinarith
    · have := h x₂ x₁ hl
      rw [he, sub_self] at this
      nlinarith
  · refine tendsto_atTop_mono' atTop ?_
      ((tendsto_id.const_mul_atTop hs).atTop_add (tendsto_const_nhds (x := g 0 - s * 0)))
    filter_upwards [eventually_ge_atTop 0] with x hx
    have := h 0 x hx
    simp only [id]
    linarith
  · refine tendsto_atBot_mono' atBot ?_
      ((tendsto_id.const_mul_atBot hs).atBot_add (tendsto_const_nhds (x := g 0 - s * 0)))
    filter_upwards [eventually_le_atBot 0] with x hx
    have := h x 0 hx
    simp only [id]
    linarith

/-- The distance of `x` from the root `x₀` of `g` is at most `|g x|/s`. -/
theorem bound_of_growth {g : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (h : ∀ x₁ x₂, x₁ ≤ x₂ → s * (x₂ - x₁) ≤ g x₂ - g x₁) {x₀ : ℝ} (h₀ : g x₀ = 0) (x : ℝ) :
    |x - x₀| ≤ |g x| / s := by
  rw [le_div_iff₀ hs]
  rcases le_total x₀ x with hl | hl
  · have := h x₀ x hl
    rw [h₀, sub_zero] at this
    rw [abs_of_nonneg (sub_nonneg.2 hl)]
    nlinarith [le_abs_self (g x)]
  · have := h x x₀ hl
    rw [h₀, zero_sub] at this
    rw [abs_of_nonpos (sub_nonpos.2 hl)]
    nlinarith [neg_abs_le (g x)]

/-! ### The constants of WGS 84 -/

theorem a_pos : 0 < a := by unfold a; norm_num

theorem f_pos : 0 < f := by unfold f; norm_num

theorem f_lt_one : f < 1 := by unfold f; norm_num

theorem e2_pos : 0 < e2 := by unfold e2 f; norm_num

theorem e2_lt_one : e2 < 1 := by unfold e2 f; norm_num

theorem one_sub_e2 : 1 - e2 = (1 - f) ^ 2 := by unfold e2; ring

theorem c_nonneg : 0 ≤ a * e2 := (mul_pos a_pos e2_pos).le

theorem m_pos : 0 < 1 - e2 := by linarith [e2_lt_one]

/-- The radius of curvature is at most `a/(1 − f)`. -/
theorem radius_le (φ : ℝ) : radius φ ≤ a / (1 - f) := by
  unfold radius
  have hf : 0 < 1 - f := by linarith [f_lt_one]
  have hs : sin φ ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq φ, sq_nonneg (cos φ)]
  have hd : 1 - f ≤ √(1 - e2 * sin φ ^ 2) := by
    rw [show 1 - f = √((1 - f) ^ 2) from (Real.sqrt_sq hf.le).symm]
    exact Real.sqrt_le_sqrt (by rw [← one_sub_e2]; nlinarith [e2_pos])
  exact div_le_div_of_nonneg_left a_pos.le hf hd

theorem radius_pos (φ : ℝ) : 0 < radius φ := by
  unfold radius
  have hs : sin φ ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq φ, sq_nonneg (cos φ)]
  exact div_pos a_pos (Real.sqrt_pos.2 (by nlinarith [e2_lt_one, e2_pos]))

/-! ### Coordinates from a root -/

/-- A root `u` of `k` gives the latitude `arctan u` and the height of `requirements.md`, whose
position lies at the distance `p` from the polar axis and at the height `z`. -/
theorem position_of_rootA {p z u : ℝ} (hp : 0 < p) (hk : kA (a * e2) (1 - e2) p z u = 0)
    (lon : ℝ) :
    0 < radius (arctan u) + (p + z * u - a * √(1 + (1 - e2) * u ^ 2)) / √(1 + u ^ 2) ∧
      position (arctan u) lon ((p + z * u - a * √(1 + (1 - e2) * u ^ 2)) / √(1 + u ^ 2)) =
        (p * cos lon, p * sin lon, z) := by
  have hS : 0 < √(1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hQ : 0 < √(1 + (1 - e2) * u ^ 2) :=
    lt_of_lt_of_le one_pos (one_le_sqrt m_pos.le u)
  have sS := Real.sq_sqrt (show 0 ≤ 1 + u ^ 2 by positivity)
  have sQ := Real.sq_sqrt (show 0 ≤ 1 + (1 - e2) * u ^ 2 by nlinarith [m_pos, sq_nonneg u])
  set S := √(1 + u ^ 2)
  set Q := √(1 + (1 - e2) * u ^ 2)
  have hr : radius (arctan u) = a * S / Q := by
    unfold radius
    rw [sin_arctan]
    have e : 1 - e2 * (u / S) ^ 2 = (Q / S) ^ 2 := by
      field_simp; rw [sS, sQ]; ring
    rw [e, Real.sqrt_sq (div_nonneg hQ.le hS.le)]
    field_simp
  have hz : z = p * u - a * e2 * u / Q := by unfold kA at hk; linarith
  have hh : (p + z * u - a * Q) / S = S * (p - a / Q) := by
    rw [hz]
    field_simp
    linear_combination (a - p * Q) * sS - a * sQ
  rw [hh, hr]
  refine ⟨by
    have : a * S / Q + S * (p - a / Q) = S * p := by ring
    rw [this]; positivity, ?_⟩
  simp only [position, hr, cos_arctan, sin_arctan, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · rw [hz]; field_simp; ring

/-- A root `v` of `ℓ` for `z > 0` gives the latitude `π/2 − arctan v` and the height of
`requirements.md`. -/
theorem position_of_rootB {p z v : ℝ} (hz : 0 < z) (hl : lB (a * e2) (1 - e2) p z v = 0)
    (lon : ℝ) :
    0 < radius (π / 2 - arctan v) + (p * v + z - a * √(v ^ 2 + (1 - e2))) / √(1 + v ^ 2) ∧
      position (π / 2 - arctan v) lon ((p * v + z - a * √(v ^ 2 + (1 - e2))) / √(1 + v ^ 2)) =
        (p * cos lon, p * sin lon, z) := by
  have hS : 0 < √(1 + v ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hQ : 0 < √(v ^ 2 + (1 - e2)) := Real.sqrt_pos.2 (by nlinarith [m_pos, sq_nonneg v])
  have sS := Real.sq_sqrt (show 0 ≤ 1 + v ^ 2 by positivity)
  have sQ := Real.sq_sqrt (show 0 ≤ v ^ 2 + (1 - e2) by nlinarith [m_pos, sq_nonneg v])
  set S := √(1 + v ^ 2)
  set Q := √(v ^ 2 + (1 - e2))
  have hc : cos (π / 2 - arctan v) = v / S := by rw [cos_pi_div_two_sub, sin_arctan]
  have hs : sin (π / 2 - arctan v) = 1 / S := by rw [sin_pi_div_two_sub, cos_arctan]
  have hr : radius (π / 2 - arctan v) = a * S / Q := by
    unfold radius
    rw [hs]
    have e : 1 - e2 * (1 / S) ^ 2 = (Q / S) ^ 2 := by
      field_simp; rw [sS, sQ]; ring
    rw [e, Real.sqrt_sq (div_nonneg hQ.le hS.le)]
    field_simp
  have hp : p = z * v + a * e2 * v / Q := by unfold lB at hl; linarith
  have hh : (p * v + z - a * Q) / S = S * (z - a * (1 - e2) / Q) := by
    rw [hp]
    field_simp
    linear_combination (a * (1 - e2) - z * Q) * sS - a * sQ
  rw [hh, hr]
  refine ⟨by
    have : a * S / Q + S * (z - a * (1 - e2) / Q) = S * (z + a * e2 / Q) := by ring
    rw [this]
    have : 0 < a * e2 / Q := div_pos (mul_pos a_pos e2_pos) hQ
    positivity, ?_⟩
  simp only [position, hr, hc, hs, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp]; field_simp; ring
  · rw [hp]; field_simp; ring
  · field_simp; ring

/-- The root of `ℓ` lies above zero when `p > 0`. -/
theorem rootB_pos {p z v : ℝ} (hp : 0 < p) (hz : 0 < z) (hl : lB (a * e2) (1 - e2) p z v = 0) :
    0 < v := by
  have hQ : 0 < √(v ^ 2 + (1 - e2)) := Real.sqrt_pos.2 (by nlinarith [m_pos, sq_nonneg v])
  have hp' : p = v * (z + a * e2 / √(v ^ 2 + (1 - e2))) := by
    unfold lB at hl; linear_combination -hl
  have hw : 0 < z + a * e2 / √(v ^ 2 + (1 - e2)) := by
    have := div_pos (mul_pos a_pos e2_pos) hQ; linarith
  by_contra hv
  have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hv) hw.le
  linarith

/-! ### The longitude -/

/-- The half-angle form of the longitude for `p + x > 0`. -/
theorem lonA_spec {x y : ℝ} (hp : 0 < √(x ^ 2 + y ^ 2)) (hpx : 0 < √(x ^ 2 + y ^ 2) + x) :
    √(x ^ 2 + y ^ 2) * cos (2 * arctan (y / (√(x ^ 2 + y ^ 2) + x))) = x ∧
      √(x ^ 2 + y ^ 2) * sin (2 * arctan (y / (√(x ^ 2 + y ^ 2) + x))) = y := by
  have sP := Real.sq_sqrt (show 0 ≤ x ^ 2 + y ^ 2 by positivity)
  set P := √(x ^ 2 + y ^ 2)
  set w := y / (P + x)
  have hW : 0 < √(1 + w ^ 2) := Real.sqrt_pos.2 (by positivity)
  have sW := Real.sq_sqrt (show 0 ≤ 1 + w ^ 2 by positivity)
  have hw : 1 + w ^ 2 = 2 * P / (P + x) := by
    simp only [w]; field_simp; nlinarith [sP]
  rw [cos_two_mul, sin_two_mul, cos_arctan, sin_arctan]
  constructor
  · rw [div_pow, one_pow, sW, hw]; field_simp; ring
  · have e : 2 * (w / √(1 + w ^ 2)) * (1 / √(1 + w ^ 2)) = 2 * w / (1 + w ^ 2) := by
      calc 2 * (w / √(1 + w ^ 2)) * (1 / √(1 + w ^ 2)) = 2 * w / √(1 + w ^ 2) ^ 2 := by ring
        _ = 2 * w / (1 + w ^ 2) := by rw [sW]
    rw [e, hw]; simp only [w]; field_simp

/-- The form of the longitude for `p − x > 0`. -/
theorem lonB_spec {x y : ℝ} (hp : 0 < √(x ^ 2 + y ^ 2)) (hpx : 0 < √(x ^ 2 + y ^ 2) - x) :
    √(x ^ 2 + y ^ 2) * cos (π - 2 * arctan (y / (√(x ^ 2 + y ^ 2) - x))) = x ∧
      √(x ^ 2 + y ^ 2) * sin (π - 2 * arctan (y / (√(x ^ 2 + y ^ 2) - x))) = y := by
  have sP := Real.sq_sqrt (show 0 ≤ x ^ 2 + y ^ 2 by positivity)
  set P := √(x ^ 2 + y ^ 2)
  set w := y / (P - x)
  have hW : 0 < √(1 + w ^ 2) := Real.sqrt_pos.2 (by positivity)
  have sW := Real.sq_sqrt (show 0 ≤ 1 + w ^ 2 by positivity)
  have hw : 1 + w ^ 2 = 2 * P / (P - x) := by
    simp only [w]; field_simp; nlinarith [sP]
  rw [cos_pi_sub, sin_pi_sub, cos_two_mul, sin_two_mul, cos_arctan, sin_arctan]
  constructor
  · rw [div_pow, one_pow, sW, hw]; field_simp; ring
  · have e : 2 * (w / √(1 + w ^ 2)) * (1 / √(1 + w ^ 2)) = 2 * w / (1 + w ^ 2) := by
      calc 2 * (w / √(1 + w ^ 2)) * (1 / √(1 + w ^ 2)) = 2 * w / √(1 + w ^ 2) ^ 2 := by ring
        _ = 2 * w / (1 + w ^ 2) := by rw [sW]
    rw [e, hw]; simp only [w]; field_simp

/-! ### Uniqueness -/

/-- Geodetic coordinates put the point at the distance `(N + h) cos φ` from the polar axis. -/
theorem geodetic_p {x y z φ lon h : ℝ} (g : IsGeodetic x y z φ lon h) :
    √(x ^ 2 + y ^ 2) = (radius φ + h) * cos φ ∧ 0 < cos φ := by
  obtain ⟨hφ, hR, hpos⟩ := g
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le φ], by linarith [le_abs_self φ]⟩
  simp only [position, Prod.mk.injEq] at hpos
  obtain ⟨hx, hy, -⟩ := hpos
  refine ⟨?_, hc⟩
  rw [← hx, ← hy]
  have : ((radius φ + h) * cos φ * cos lon) ^ 2 + ((radius φ + h) * cos φ * sin lon) ^ 2 =
      ((radius φ + h) * cos φ) ^ 2 := by
    have := sin_sq_add_cos_sq lon; linear_combination ((radius φ + h) * cos φ) ^ 2 * this
  rw [this, Real.sqrt_sq (mul_pos hR hc).le]

theorem one_sub_pos (φ : ℝ) : 0 < 1 - e2 * sin φ ^ 2 := by
  have hs : sin φ ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq φ, sq_nonneg (cos φ)]
  nlinarith [e2_lt_one, e2_pos]

/-- `√(1 + m tan² φ)` is the square root of `1 − e² sin² φ` over the cosine. -/
theorem sqrt_tan {φ : ℝ} (hc : 0 < cos φ) :
    √(1 + (1 - e2) * tan φ ^ 2) = √(1 - e2 * sin φ ^ 2) / cos φ := by
  have hd := Real.sqrt_pos.2 (one_sub_pos φ)
  have sd := Real.sq_sqrt (one_sub_pos φ).le
  rw [← Real.sqrt_sq (div_nonneg hd.le hc.le)]
  congr 1
  rw [tan_eq_sin_div_cos, div_pow, div_pow, sd]
  field_simp
  nlinarith [sin_sq_add_cos_sq φ]

/-- `√(cot² φ + m)` is the square root of `1 − e² sin² φ` over the sine. -/
theorem sqrt_cot {φ : ℝ} (hs : 0 < sin φ) :
    √((cos φ / sin φ) ^ 2 + (1 - e2)) = √(1 - e2 * sin φ ^ 2) / sin φ := by
  have hd := Real.sqrt_pos.2 (one_sub_pos φ)
  have sd := Real.sq_sqrt (one_sub_pos φ).le
  rw [← Real.sqrt_sq (div_nonneg hd.le hs.le)]
  congr 1
  rw [div_pow, div_pow, sd]
  field_simp
  nlinarith [sin_sq_add_cos_sq φ]

/-- The latitude of geodetic coordinates solves `k(tan φ) = 0`. -/
theorem kA_tan {x y z φ lon h : ℝ} (g : IsGeodetic x y z φ lon h) :
    kA (a * e2) (1 - e2) (√(x ^ 2 + y ^ 2)) z (tan φ) = 0 := by
  obtain ⟨hp, hc⟩ := geodetic_p g
  have hz := g.2.2
  simp only [position, Prod.mk.injEq] at hz
  obtain ⟨-, -, hz⟩ := hz
  have hd := Real.sqrt_pos.2 (one_sub_pos φ)
  unfold kA
  rw [sqrt_tan hc, hp, ← hz, tan_eq_sin_div_cos]
  unfold radius
  field_simp
  ring

/-- The latitude of geodetic coordinates in `(0, π/2)` solves `ℓ(cot φ) = 0`. -/
theorem lB_cot {x y z φ lon h : ℝ} (g : IsGeodetic x y z φ lon h) (hφ : 0 < φ) :
    lB (a * e2) (1 - e2) (√(x ^ 2 + y ^ 2)) z (cos φ / sin φ) = 0 := by
  obtain ⟨hp, hc⟩ := geodetic_p g
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ (by linarith [le_abs_self φ, g.1, pi_pos])
  have hz := g.2.2
  simp only [position, Prod.mk.injEq] at hz
  obtain ⟨-, -, hz⟩ := hz
  have hd := Real.sqrt_pos.2 (one_sub_pos φ)
  unfold lB
  rw [sqrt_cot hs, hp, ← hz]
  unfold radius
  field_simp
  ring

/-- Geodetic coordinates of `(x, y, z)` with the latitude negated are those of `(x, y, −z)`. -/
theorem geodetic_neg {x y z φ lon h : ℝ} (g : IsGeodetic x y z φ lon h) :
    IsGeodetic x y (-z) (-φ) lon h := by
  obtain ⟨hφ, hR, hpos⟩ := g
  have hr : radius (-φ) = radius φ := by simp only [radius, sin_neg, neg_sq]
  refine ⟨by rwa [abs_neg], by rwa [hr], ?_⟩
  simp only [position, Prod.mk.injEq] at hpos ⊢
  obtain ⟨hx, hy, hz⟩ := hpos
  rw [hr, cos_neg, sin_neg]
  exact ⟨hx, hy, by rw [← hz]; ring⟩

/-- Above the cylinder about the center, the latitude is positive. -/
theorem lat_pos {x y z φ lon h : ℝ} (g : IsGeodetic x y z φ lon h) (hz : a * e2 / (1 - f) < z) :
    0 < φ := by
  by_contra hφ'
  have hφ : φ ≤ 0 := not_lt.1 hφ'
  obtain ⟨hφa, hR, hpos⟩ := g
  simp only [position, Prod.mk.injEq] at hpos
  obtain ⟨-, -, hz'⟩ := hpos
  have hs : sin φ ≤ 0 := by
    have := sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hφ)
      (by linarith [neg_abs_le φ, pi_pos])
    rw [sin_neg] at this; linarith
  have h1 : (radius φ + h) * sin φ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hR.le hs
  have h2 : -(e2 * radius φ * sin φ) ≤ e2 * radius φ := by
    have := neg_one_le_sin φ
    nlinarith [mul_pos e2_pos (radius_pos φ)]
  have h3 : e2 * radius φ ≤ a * e2 / (1 - f) := by
    have hf : 0 < 1 - f := by linarith [f_lt_one]
    rw [show a * e2 / (1 - f) = e2 * (a / (1 - f)) by ring]
    exact mul_le_mul_of_nonneg_left (radius_le φ) e2_pos.le
  have : z = (radius φ + h) * sin φ - e2 * radius φ * sin φ := by rw [← hz']; ring
  linarith

theorem tan_inj {φ₁ φ₂ : ℝ} (h₁ : |φ₁| < π / 2) (h₂ : |φ₂| < π / 2) (h : tan φ₁ = tan φ₂) :
    φ₁ = φ₂ := by
  calc φ₁ = arctan (tan φ₁) :=
        (arctan_tan (by linarith [neg_abs_le φ₁]) (by linarith [le_abs_self φ₁])).symm
    _ = arctan (tan φ₂) := by rw [h]
    _ = φ₂ := arctan_tan (by linarith [neg_abs_le φ₂]) (by linarith [le_abs_self φ₂])

/-- The latitude above the cylinder about the center is unique. -/
theorem latB_unique {x y z φ₁ l₁ h₁ φ₂ l₂ h₂ : ℝ} (hz : a * e2 / (1 - f) < z)
    (g₁ : IsGeodetic x y z φ₁ l₁ h₁) (g₂ : IsGeodetic x y z φ₂ l₂ h₂) : φ₁ = φ₂ := by
  have hz0 : 0 < z := lt_of_le_of_lt
    (div_nonneg c_nonneg (by linarith [f_lt_one])) hz
  have p₁ := lat_pos g₁ hz
  have p₂ := lat_pos g₂ hz
  have bij := bijective_of_growth hz0 (continuous_lB m_pos _ _)
    (fun _ _ h => growthB c_nonneg m_pos (√(x ^ 2 + y ^ 2)) z h)
  have hcot := bij.1 ((lB_cot g₁ p₁).trans (lB_cot g₂ p₂).symm)
  have s₁ : 0 < sin φ₁ := sin_pos_of_pos_of_lt_pi p₁ (by linarith [le_abs_self φ₁, g₁.1, pi_pos])
  have s₂ : 0 < sin φ₂ := sin_pos_of_pos_of_lt_pi p₂ (by linarith [le_abs_self φ₂, g₂.1, pi_pos])
  have c₁ := (geodetic_p g₁).2
  have c₂ := (geodetic_p g₂).2
  apply tan_inj g₁.1 g₂.1
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, ← inv_div, ← inv_div (cos φ₂), hcot]

/-- **Uniqueness.**  In the domain `D`, geodetic coordinates have one latitude and one height,
and their longitudes have one cosine and one sine. -/
theorem geodetic_unique {x y z φ₁ l₁ h₁ φ₂ l₂ h₂ : ℝ} (hD : InDomain x y z)
    (g₁ : IsGeodetic x y z φ₁ l₁ h₁) (g₂ : IsGeodetic x y z φ₂ l₂ h₂) :
    φ₁ = φ₂ ∧ h₁ = h₂ ∧ cos l₁ = cos l₂ ∧ sin l₁ = sin l₂ := by
  have hlat : φ₁ = φ₂ := by
    obtain ⟨-, hA | hB⟩ := hD
    · have bij := bijective_of_growth (sub_pos.2 hA) (continuous_kA m_pos.le _ _)
        (fun _ _ h => growthA c_nonneg m_pos.le (√(x ^ 2 + y ^ 2)) z h)
      exact tan_inj g₁.1 g₂.1 (bij.1 ((kA_tan g₁).trans (kA_tan g₂).symm))
    · rcases le_or_gt 0 z with hz | hz
      · rw [abs_of_nonneg hz] at hB
        exact latB_unique hB g₁ g₂
      · rw [abs_of_neg hz] at hB
        have := latB_unique hB (geodetic_neg g₁) (geodetic_neg g₂)
        linarith
  subst hlat
  obtain ⟨hp₁, hc⟩ := geodetic_p g₁
  obtain ⟨hp₂, -⟩ := geodetic_p g₂
  have hh : h₁ = h₂ := by
    have := mul_right_cancel₀ hc.ne' (hp₁.symm.trans hp₂)
    linarith
  subst hh
  have hx₁ := g₁.2.2
  have hx₂ := g₂.2.2
  simp only [position, Prod.mk.injEq] at hx₁ hx₂
  have hRc : (radius φ₁ + h₁) * cos φ₁ ≠ 0 := (mul_pos g₁.2.1 hc).ne'
  exact ⟨rfl, rfl, mul_left_cancel₀ hRc (hx₁.1.trans hx₂.1.symm),
    mul_left_cancel₀ hRc (hx₁.2.1.trans hx₂.2.1.symm)⟩

/-! ### Existence -/

/-- Every point off the polar axis has a longitude. -/
theorem exists_lon {x y : ℝ} (hp : 0 < √(x ^ 2 + y ^ 2)) :
    ∃ lon, √(x ^ 2 + y ^ 2) * cos lon = x ∧ √(x ^ 2 + y ^ 2) * sin lon = y := by
  rcases lt_or_ge 0 (√(x ^ 2 + y ^ 2) + x) with h | h
  · exact ⟨_, lonA_spec hp h⟩
  · exact ⟨_, lonB_spec hp (by linarith)⟩

/-- Above the cylinder about the center, a point off the polar axis has geodetic coordinates. -/
theorem exists_above {x y z : ℝ} (hp : 0 < √(x ^ 2 + y ^ 2)) (hz : a * e2 / (1 - f) < z) :
    ∃ φ lon h, IsGeodetic x y z φ lon h := by
  have hz0 : 0 < z := lt_of_le_of_lt (div_nonneg c_nonneg (by linarith [f_lt_one])) hz
  obtain ⟨v, hv⟩ := (bijective_of_growth hz0 (continuous_lB m_pos _ z)
    (fun _ _ h => growthB c_nonneg m_pos (√(x ^ 2 + y ^ 2)) z h)).2 0
  obtain ⟨lon, hc, hs⟩ := exists_lon hp
  have vpos := rootB_pos hp hz0 hv
  have h0 : 0 < arctan v := by have := arctan_strictMono vpos; rwa [arctan_zero] at this
  obtain ⟨hR, hpos⟩ := position_of_rootB hz0 hv lon
  refine ⟨_, lon, _, abs_lt.2 ⟨by linarith [arctan_lt_pi_div_two v, pi_pos],
    by linarith⟩, hR, ?_⟩
  rw [hpos, hc, hs]

/-- **Existence.**  Every point of the domain `D` has geodetic coordinates. -/
theorem geodetic_exists {x y z : ℝ} (hD : InDomain x y z) : ∃ φ lon h, IsGeodetic x y z φ lon h := by
  obtain ⟨hp, hA | hB⟩ := hD
  · obtain ⟨u, hu⟩ := (bijective_of_growth (sub_pos.2 hA) (continuous_kA m_pos.le _ z)
      (fun _ _ h => growthA c_nonneg m_pos.le (√(x ^ 2 + y ^ 2)) z h)).2 0
    obtain ⟨lon, hc, hs⟩ := exists_lon hp
    obtain ⟨hR, hpos⟩ := position_of_rootA hp hu lon
    refine ⟨arctan u, lon, _, abs_lt.2 ⟨neg_pi_div_two_lt_arctan u, arctan_lt_pi_div_two u⟩,
      hR, ?_⟩
    rw [hpos, hc, hs]
  · rcases le_or_gt 0 z with hz | hz
    · rw [abs_of_nonneg hz] at hB
      exact exists_above hp hB
    · rw [abs_of_neg hz] at hB
      obtain ⟨φ, lon, h, g⟩ := exists_above (x := x) (y := y) hp hB
      exact ⟨-φ, lon, h, by simpa using geodetic_neg g⟩

#print axioms geodetic_exists
#print axioms bijective_of_growth
#print axioms bound_of_growth
#print axioms position_of_rootA
#print axioms position_of_rootB
#print axioms rootB_pos
#print axioms lonA_spec
#print axioms lonB_spec
#print axioms geodetic_unique

end Demos.Frames.Geodetic
