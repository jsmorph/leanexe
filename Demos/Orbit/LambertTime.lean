import Demos.Orbit.LambertOrbit
import Demos.Orbit.LambertRoot
import Demos.Orbit.NewtonUnique

/-!
Lambert's theorem for every conic.  For every `x`, `izzo_target` states that the motion from
Izzo's state `(r1, v1(x))` reaches `r2` at the advance `χ` of the universal variable exactly when
`U2 = 2 c1²` and `U1 = 2 c0 c1`, with `c0 = x y + λ (1 - x²)` and `c1 = (y - λ x) s/(2γ)`, and that
`β = 2μ/|r1| - |v1|² = 4γ² (1 - x²)/s²`.  For `x > -1`, `izzo_arrival` gives the first such
advance and its time.  For an ellipse, `-1 < x < 1`, the advance is `χ = 2ψ/√β` with
`ψ = arccos c0`; for a hyperbola, `x > 1`, it is `χ = 2ψ/√(-β)` with `ψ = arcosh c0`; and for a
parabola, `x = 1`, it is `χ = 2 c1`.  In each case the time is `√(s³/(2μ)) T(x)`.  For `x ≤ -1`
the orbit is a parabola or a hyperbola with `c0 < 0`, on which `U1` increases from 0 with `χ`, and
`izzo_no_arrival` states that the motion never reaches `r2` at a positive advance.

With the converse of the geometry, `orbit_izzo`, and the uniqueness of the root,
`lambert_transfer` states that exactly one motion along a conic in the direction of `k` first
reaches `r2` after the time `t`: the motion from Izzo's state at the root `x*`.  `lambert_newton`
states the same for the solutions of Newton's equation, by `conic_newton` and `newton_unique`, and
gives the velocity `v2(x*)` at `r2`.

The positions follow from Lagrange's coefficients: in the basis `r1`, `r2` of `izzo_basis`,
`f r1 + g v1 = r2` is the pair of scalar identities `g κ = 1` and `f + g α1 = 0`.  The time
follows Lagrange's time equation: with `u = √|1 - x²|`, the advance `χ = ψ s/(γ u)` has
`√|β| χ = 2ψ`, and `|r1| U1 + (r1 · v1) U2 + μ (χ - U1)/β` reduces to `s²/(2γ) T(x)` by the
identity `key_time`.
-/

namespace Demos.Orbit

open Real

/-! ### Scalar identities in Izzo's variables -/

section Scalar

variable {s L ρ x y γ : ℝ}

/-- Izzo's equation `y² = 1 - λ² + λ² x²` written with `q = y + λ x`. -/
theorem xy_subst (hL : L ≠ 0) (hq : 0 < y + L * x) (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) :
    x = ((y + L * x) ^ 2 - (1 - L ^ 2)) / (2 * L * (y + L * x)) ∧
      y = ((y + L * x) ^ 2 + (1 - L ^ 2)) / (2 * (y + L * x)) :=
  xy_of_q hL rfl hq hy

/-- The time identity: `(1 - x²) d (b1 d + 2 N1 C) - d C - (λ y - x) = 0`, with
`N1 = (1 + ρ + λ² (1 - ρ))/2`, `C = x y + λ (1 - x²)`, `b1 = (λ y - x) - ρ (λ y + x)`, and
`d = y - λ x`. -/
theorem key_time (hL : L ≠ 0) (hq : 0 < y + L * x) (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) :
    (1 - x ^ 2) * (y - L * x) * (((L * y - x) - ρ * (L * y + x)) * (y - L * x) +
      2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (x * y + L * (1 - x ^ 2))) -
        (y - L * x) * (x * y + L * (1 - x ^ 2)) - (L * y - x) = 0 := by
  obtain ⟨hx, hy'⟩ := xy_subst hL hq hy
  generalize y + L * x = q at hx hy' hq
  subst hx hy'
  field_simp
  ring

/-- `g κ = 1` for the position `r2`. -/
theorem key_g (hs : 0 < s) (hL : L ≠ 0) (hLlt : L ^ 2 < 1) (hγ : 0 < γ) (hq : 0 < y + L * x)
    (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) :
    s ^ 2 * (y - L * x) * (2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (x * y + L * (1 - x ^ 2)) +
        ((L * y - x) - ρ * (L * y + x)) * (y - L * x)) / (2 * γ) *
      (γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s)) = 1 := by
  have hL1 : 1 - L ^ 2 ≠ 0 := by linarith
  obtain ⟨hx, hy'⟩ := xy_subst hL hq hy
  generalize y + L * x = q at hx hy' hq
  subst hx hy'
  field_simp
  ring

/-- `f + g α1 = 0` for the position `r2`. -/
theorem key_f (hs : 0 < s) (hL : L ≠ 0) (hLlt : L ^ 2 < 1) (hρ : ρ ^ 2 < 1) (hγ : 0 < γ)
    (hq : 0 < y + L * x) (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) :
    (1 - (y - L * x) ^ 2 / ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) +
      s ^ 2 * (y - L * x) * (2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (x * y + L * (1 - x ^ 2)) +
          ((L * y - x) - ρ * (L * y + x)) * (y - L * x)) / (2 * γ) *
        (γ * ((L * y - x) - ρ * (L * y + x)) / (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) ^ 2 -
          γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s) *
            (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
              (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) /
            (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) ^ 2) = 0 := by
  have hL1 : 1 - L ^ 2 ≠ 0 := by linarith
  have hN1 := (factors_pos (L := L) hρ).1
  obtain ⟨hx, hy'⟩ := xy_subst hL hq hy
  generalize y + L * x = q at hx hy' hq
  subst hx hy'
  field_simp
  ring

/-- The time of the advance `χ = ψ s/(γ u)` for an ellipse or a hyperbola:
`(|r1| U1 + (r1 · v1) U2 + μ (χ - U1)/β) T*/t` is Izzo's `T(x)` for `ψ/u` in place of its first
term. -/
theorem time_scalar {ψ u t μ : ℝ} (hs : 0 < s) (hγ : 0 < γ) (hu : 0 < u) (hx : 1 - x ^ 2 ≠ 0)
    (hL : L ≠ 0) (hq : 0 < y + L * x) (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2)
    (hμ : μ = 2 * γ ^ 2 / s) :
    (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) *
          (2 * (x * y + L * (1 - x ^ 2)) * ((y - L * x) * s / (2 * γ))) +
        γ * ((L * y - x) - ρ * (L * y + x)) * (2 * ((y - L * x) * s / (2 * γ)) ^ 2) +
        μ * ((ψ * s / (γ * u) - 2 * (x * y + L * (1 - x ^ 2)) * ((y - L * x) * s / (2 * γ))) /
          (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2))) * (2 * γ / s ^ 2 * t) =
      t * ((ψ / u - x + L * y) / (1 - x ^ 2)) := by
  have kt := key_time (ρ := ρ) hL hq hy
  subst hμ
  linear_combination (norm := skip) (t / (1 - x ^ 2)) * kt
  field_simp
  ring

/-- `x y + λ (1 - x²) < 0` for `x ≤ -1`. -/
theorem c0_neg (hx : x ≤ -1) (hy0 : 0 < y) (hd : 0 < y - L * x)
    (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) : x * y + L * (1 - x ^ 2) < 0 := by
  have h : (L * (1 + x)) ^ 2 < y ^ 2 := by
    rw [hy]; nlinarith [mul_nonneg (sq_nonneg L) (by linarith : (0 : ℝ) ≤ -(1 + x))]
  have hyL := (abs_lt_of_sq_lt_sq' h hy0.le).2
  nlinarith [mul_le_mul_of_nonneg_right hx hd.le]

/-- `1 < x y + λ (1 - x²)` for `x > 1`. -/
theorem c0_gt_one (hx : 1 < x) (hy0 : 0 < y) (hd : 0 < y - L * x)
    (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) : 1 < x * y + L * (1 - x ^ 2) := by
  have h : (L * (x - 1)) ^ 2 < y ^ 2 := by
    rw [hy]; nlinarith [mul_nonneg (sq_nonneg L) (sub_pos.mpr hx).le]
  have hyL := (abs_lt_of_sq_lt_sq' h hy0.le).2
  have hC0 : 0 < x * y + L * (1 - x ^ 2) := by nlinarith [mul_pos (sub_pos.mpr hx) hd]
  have hC2 : (x * y + L * (1 - x ^ 2)) ^ 2 = 1 + (x ^ 2 - 1) * (y - L * x) ^ 2 := by
    linear_combination hy
  nlinarith [mul_pos (by nlinarith : (0 : ℝ) < x ^ 2 - 1) (pow_pos hd 2)]

end Scalar

/-! ### Where Izzo's motion reaches `r2` -/

/-- Half the advance of the eccentric anomaly from `r1` to `r2` along an ellipse:
`ψ = arccos(x y + λ (1 - x²))`, the angle of Izzo's time of flight. -/
noncomputable def izzoPsi (L x : ℝ) : ℝ := arccos (x * Lambert.yOf L x + L * (1 - x ^ 2))

theorem lagrange_basis {r1 r2 : V3} {f g α κ : ℝ} (hgk : g * κ = 1) (hfa : f + g * α = 0) :
    f • r1 + g • (α • r1 + κ • r2) = r2 := by
  ext <;> simp only [V3.add_x, V3.add_y, V3.add_z, V3.smul_x, V3.smul_y, V3.smul_z]
  · linear_combination r1.x * hfa + r2.x * hgk
  · linear_combination r1.y * hfa + r2.y * hgk
  · linear_combination r1.z * hfa + r2.z * hgk

theorem izzoParams_time_eq {μ s γ : ℝ} (hs : 0 < s) (hγ : 0 < γ) (hγ2 : γ ^ 2 = μ * s / 2)
    (t : ℝ) : √(2 * μ / (s * s * s)) * t = 2 * γ / s ^ 2 * t := by
  have hμ : μ = 2 * γ ^ 2 / s := by rw [hγ2]; field_simp
  congr 1
  rw [← sqrt_sq (by positivity : 0 ≤ 2 * γ / s ^ 2), hμ]
  congr 1
  field_simp

/-- **Izzo's state and the position `r2`.**  For every `x`, Izzo's quantities for the state
`(r1, v1(x))`: `β = 4γ² (1 - x²)/s²`, and the advance `χ` reaches `r2` exactly when
`U2 = 2 c1²` and `U1 = 2 c0 c1`, with `c0 = x y + λ (1 - x²)` and `c1 = (y - λ x) s/(2γ)`. -/
theorem izzo_target {μ : ℝ} (hμ : 0 < μ) {r1 r2 k : V3} (hD : V3.dot (V3.cross r1 r2) k ≠ 0)
    (x : ℝ) :
    ∃ s L ρ y γ : ℝ, 0 < s ∧ L ≠ 0 ∧ L ^ 2 < 1 ∧ ρ ^ 2 < 1 ∧ 0 < y ∧ 0 < y + L * x ∧ 0 < γ ∧
      y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2 ∧ μ = 2 * γ ^ 2 / s ∧
      (∀ t, (izzoParams r1 r2 t μ k).1 = L ∧ (izzoParams r1 r2 t μ k).2 = 2 * γ / s ^ 2 * t) ∧
      Lambert.yOf L x = y ∧
      V3.norm r1 = s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) ∧
      V3.dot r1 (izzoV1 μ r1 r2 k x) = γ * ((L * y - x) - ρ * (L * y + x)) ∧
      conicBeta μ r1 (izzoV1 μ r1 r2 k x) = 4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2 ∧
      0 < V3.dot (V3.cross r1 (izzoV1 μ r1 r2 k x)) (V3.cross r1 (izzoV1 μ r1 r2 k x)) ∧
      ∀ χ, conicPos μ r1 (izzoV1 μ r1 r2 k x) χ = r2 ↔
        U2 (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) χ = 2 * ((y - L * x) * s / (2 * γ)) ^ 2 ∧
        U1 (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) χ =
          2 * (x * y + L * (1 - x ^ 2)) * ((y - L * x) * s / (2 * γ)) := by
  obtain ⟨s, L, ρ, y, γ, hs, hL, -, hy, -, hs0, hL0, hLlt, hρ2, hy0, hq, hγ0, hy2, hγ2, -, -,
    hc, hn1, hn2, hP, hv1, -⟩ := izzo_basis hμ hD x
  have hN1 := (factors_pos (L := L) hρ2).1
  have hn1p : 0 < V3.norm r1 := by rw [hn1]; positivity
  have hμγ : μ = 2 * γ ^ 2 / s := by rw [hγ2]; field_simp
  have hrv : V3.dot r1 (izzoV1 μ r1 r2 k x) = γ * ((L * y - x) - ρ * (L * y + x)) := by
    rw [hv1, dot_basis_left, ← V3.norm_sq r1]; field_simp; ring
  have hβ : conicBeta μ r1 (izzoV1 μ r1 r2 k x) = 4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2 := by
    have hE := izzo_energy hμ hD x
    rw [← hs] at hE
    have e : conicBeta μ r1 (izzoV1 μ r1 r2 k x) =
        μ * (2 / V3.norm r1 - V3.dot (izzoV1 μ r1 r2 k x) (izzoV1 μ r1 r2 k x) / μ) := by
      rw [conicBeta]; field_simp
    rw [e, hE, hμγ]; field_simp; ring
  have hh : 0 < V3.dot (V3.cross r1 (izzoV1 μ r1 r2 k x)) (V3.cross r1 (izzoV1 μ r1 r2 k x)) :=
    (izzo_orbit hμ hD x).2.1.1
  have hpos : (1 - μ * (2 * ((y - L * x) * s / (2 * γ)) ^ 2) / V3.norm r1) • r1 +
      (V3.norm r1 * (2 * (x * y + L * (1 - x ^ 2)) * ((y - L * x) * s / (2 * γ))) +
        V3.dot r1 (izzoV1 μ r1 r2 k x) * (2 * ((y - L * x) * s / (2 * γ)) ^ 2)) •
          izzoV1 μ r1 r2 k x = r2 := by
    have hfu : 1 - μ * (2 * ((y - L * x) * s / (2 * γ)) ^ 2) / V3.norm r1 =
        1 - (y - L * x) ^ 2 / ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) := by
      rw [hμγ, hn1]; field_simp
    have hgu : V3.norm r1 * (2 * (x * y + L * (1 - x ^ 2)) * ((y - L * x) * s / (2 * γ))) +
        V3.dot r1 (izzoV1 μ r1 r2 k x) * (2 * ((y - L * x) * s / (2 * γ)) ^ 2) =
        s ^ 2 * (y - L * x) * (2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (x * y + L * (1 - x ^ 2)) +
          ((L * y - x) - ρ * (L * y + x)) * (y - L * x)) / (2 * γ) := by
      rw [hn1, hrv]; field_simp
    rw [hfu, hgu, hv1, hP, hn1, hn2, hc]
    exact lagrange_basis (key_g hs0 hL0 hLlt hγ0 hq hy2) (key_f hs0 hL0 hLlt hρ2 hγ0 hq hy2)
  refine ⟨s, L, ρ, y, γ, hs0, hL0, hLlt, hρ2, hy0, hq, hγ0, hy2, hμγ, fun t => ⟨?_, ?_⟩, ?_, hn1,
    hrv, hβ, hh, fun χ => ?_⟩
  · rw [izzoParams_lam, hL, hs]
  · rw [izzoParams_time, ← hs]; exact izzoParams_time_eq hs0 hγ0 hγ2 t
  · rw [hy]; rfl
  · rw [← hβ]
    constructor
    · intro hp
      obtain ⟨hf, hg⟩ := coeff_unique hh (hp.trans hpos.symm)
      have h2 : U2 (conicBeta μ r1 (izzoV1 μ r1 r2 k x)) χ =
          2 * ((y - L * x) * s / (2 * γ)) ^ 2 := by
        have : μ * U2 (conicBeta μ r1 (izzoV1 μ r1 r2 k x)) χ / V3.norm r1 =
            μ * (2 * ((y - L * x) * s / (2 * γ)) ^ 2) / V3.norm r1 := by linarith
        exact mul_left_cancel₀ hμ.ne' ((div_left_inj' hn1p.ne').mp this)
      refine ⟨h2, ?_⟩
      rw [h2] at hg
      exact mul_left_cancel₀ hn1p.ne' (by linarith)
    · rintro ⟨h2, h1⟩
      rw [conicPos, h2, h1]
      exact hpos

/-- **Izzo's motion reaches `r2` first after the time `√(s³/(2μ)) T(x)`.**  For `x > -1`, the
motion from `(r1, v1(x))` reaches `r2` at some advance `χ > 0` and at no smaller positive advance,
and the time of `χ`, multiplied by `T* = √(2μ/s³) t`, is `t T(x)`. -/
theorem izzo_arrival {μ : ℝ} (hμ : 0 < μ) {r1 r2 k : V3} (hD : V3.dot (V3.cross r1 r2) k ≠ 0)
    {x : ℝ} (hx : -1 < x) (t : ℝ) :
    ∃ χ, 0 < χ ∧ conicPos μ r1 (izzoV1 μ r1 r2 k x) χ = r2 ∧
      (∀ χ', 0 < χ' → χ' < χ → conicPos μ r1 (izzoV1 μ r1 r2 k x) χ' ≠ r2) ∧
      conicTime μ r1 (izzoV1 μ r1 r2 k x) χ * (izzoParams r1 r2 t μ k).2 =
        t * Lambert.tof (izzoParams r1 r2 t μ k).1 x := by
  obtain ⟨s, L, ρ, y, γ, hs0, hL0, hLlt, hρ2, hy0, hq, hγ0, hy2, hμγ, hpar, hyOf, hn1, hrv, hβ,
    hh, hreach⟩ := izzo_target hμ hD x
  obtain ⟨hLp, hTp⟩ := hpar t
  rw [hLp, hTp]
  have hd : 0 < y - L * x := by
    have h : (y - L * x) * (y + L * x) = 1 - L ^ 2 := by linear_combination hy2
    have : 0 < (y - L * x) * (y + L * x) := by rw [h]; linarith
    exact (pos_iff_pos_of_mul_pos this).mpr hq
  have hc1 : 0 < (y - L * x) * s / (2 * γ) := by positivity
  have first : ∀ χ, 0 < χ → conicPos μ r1 (izzoV1 μ r1 r2 k x) χ = r2 →
      (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2 ≤ 0 ∨ √(4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) * χ < 2 * π) →
      ∀ χ', 0 < χ' → χ' < χ → conicPos μ r1 (izzoV1 μ r1 r2 k x) χ' ≠ r2 := by
    intro χ hχ hpos hb χ' h0 h1 heq
    have := conicPos_inj hμ hh (χ1 := χ') (χ2 := χ) ?_ (heq.trans hpos.symm)
    · linarith
    · rw [hβ]
      refine hb.imp id fun hb => ?_
      rw [abs_of_neg (by linarith)]
      nlinarith [mul_nonneg (sqrt_nonneg (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2)) h0.le]
  rcases lt_trichotomy x 1 with hx1 | hx1 | hx1
  · -- an ellipse
    have hu1 : 0 < 1 - x ^ 2 := by nlinarith
    set u := √(1 - x ^ 2) with hu
    have hu2 : u ^ 2 = 1 - x ^ 2 := sq_sqrt hu1.le
    have hu0 : 0 < u := sqrt_pos.mpr hu1
    have hb : 0 < 4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2 := by positivity
    have hw : √(4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) = 2 * γ * u / s := by
      rw [← hu2, show 4 * γ ^ 2 * u ^ 2 / s ^ 2 = (2 * γ * u / s) ^ 2 by ring]
      exact sqrt_sq (by positivity)
    have hCS : (x * y + L * (1 - x ^ 2)) ^ 2 + (u * (y - L * x)) ^ 2 = 1 := by
      rw [mul_pow u, hu2]; linear_combination hy2
    have hC1 : (x * y + L * (1 - x ^ 2)) ^ 2 ≤ 1 ^ 2 := by
      have := sq_nonneg (u * (y - L * x)); linarith
    have hCb := abs_le_of_sq_le_sq' hC1 zero_le_one
    have hcos : cos (izzoPsi L x) = x * y + L * (1 - x ^ 2) := by
      rw [izzoPsi, hyOf, cos_arccos hCb.1 hCb.2]
    have hsin : sin (izzoPsi L x) = u * (y - L * x) := by
      rw [izzoPsi, hyOf, sin_arccos, show 1 - (x * y + L * (1 - x ^ 2)) ^ 2 =
        (u * (y - L * x)) ^ 2 by linarith, sqrt_sq (by positivity)]
    have hsin0 : 0 < sin (izzoPsi L x) := by rw [hsin]; positivity
    have hψ0 : 0 < izzoPsi L x := by
      rcases (arccos_nonneg _).lt_or_eq with h | h
      · exact h
      · rw [izzoPsi, ← h, sin_zero] at hsin0; exact absurd hsin0 (lt_irrefl 0)
    have hψπ : izzoPsi L x < π := by
      rcases (arccos_le_pi (x * Lambert.yOf L x + L * (1 - x ^ 2))).lt_or_eq with h | h
      · exact h
      · rw [izzoPsi, h, sin_pi] at hsin0; exact absurd hsin0 (lt_irrefl 0)
    have harg : √(4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) * (izzoPsi L x * s / (γ * u)) =
        2 * izzoPsi L x := by
      rw [hw]; field_simp
    have hU1 : U1 (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) (izzoPsi L x * s / (γ * u)) =
        2 * (x * y + L * (1 - x ^ 2)) * ((y - L * x) * s / (2 * γ)) := by
      rw [U1_pos hb, harg, hw, sin_two_mul, hsin, hcos]; field_simp
    have hU2 : U2 (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) (izzoPsi L x * s / (γ * u)) =
        2 * ((y - L * x) * s / (2 * γ)) ^ 2 := by
      rw [U2, ite_eq_right hb.ne', U0_pos hb, harg, cos_two_mul, cos_sq', hsin, ← hu2]
      field_simp; ring
    have hp := (hreach _).mpr ⟨hU2, hU1⟩
    refine ⟨izzoPsi L x * s / (γ * u), by positivity, hp,
      first _ (by positivity) hp (Or.inr (by rw [harg]; linarith)), ?_⟩
    have htof : Lambert.tof L x = (izzoPsi L x / u - x + L * y) / (1 - x ^ 2) := by
      simp only [Lambert.tof, hx1, ↓reduceIte, izzoPsi, hyOf, hu]
    rw [conicTime, hβ, hU1, hU2, U3, ite_eq_right hb.ne', hU1, hn1, hrv, htof]
    exact time_scalar hs0 hγ0 hu0 hu1.ne' hL0 hq hy2 hμγ
  · -- a parabola
    subst hx1
    have hy1 : y = 1 := by
      have h1 : y ^ 2 = 1 := by rw [hy2]; ring
      nlinarith
    subst hy1
    have hb0 : (4 * γ ^ 2 * (1 - 1 ^ 2) / s ^ 2 : ℝ) = 0 := by ring
    have hU1 : U1 (4 * γ ^ 2 * (1 - 1 ^ 2) / s ^ 2) (2 * ((1 - L * 1) * s / (2 * γ))) =
        2 * (1 * 1 + L * (1 - 1 ^ 2)) * ((1 - L * 1) * s / (2 * γ)) := by
      rw [hb0, U1_zero]; ring
    have hU2 : U2 (4 * γ ^ 2 * (1 - 1 ^ 2) / s ^ 2) (2 * ((1 - L * 1) * s / (2 * γ))) =
        2 * ((1 - L * 1) * s / (2 * γ)) ^ 2 := by
      rw [hb0, U2, ite_eq_left rfl]; ring
    have hp := (hreach _).mpr ⟨hU2, hU1⟩
    refine ⟨2 * ((1 - L * 1) * s / (2 * γ)), by positivity, hp,
      first _ (by positivity) hp (Or.inl hb0.le), ?_⟩
    have htof : Lambert.tof L 1 = 2 / 3 * (1 - L ^ 3) := by simp [Lambert.tof]
    rw [conicTime, hβ, hU1, hU2, hb0, U3, ite_eq_left rfl, hn1, hrv, hμγ, htof]
    field_simp
    ring
  · -- a hyperbola
    have hx2 : 0 < x ^ 2 - 1 := by nlinarith
    set u := √(x ^ 2 - 1) with hu
    have hu2 : u ^ 2 = x ^ 2 - 1 := sq_sqrt hx2.le
    have hu0 : 0 < u := sqrt_pos.mpr hx2
    have hb : 4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2 < 0 := by
      have : 0 < 4 * γ ^ 2 * (x ^ 2 - 1) / s ^ 2 := by positivity
      have e : 4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2 = -(4 * γ ^ 2 * (x ^ 2 - 1) / s ^ 2) := by ring
      linarith
    have hw : √(-(4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2)) = 2 * γ * u / s := by
      rw [show -(4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) = (2 * γ * u / s) ^ 2 by
        rw [div_pow, mul_pow, mul_pow, hu2]; ring]
      exact sqrt_sq (by positivity)
    have hC1 := c0_gt_one hx1 hy0 hd hy2
    have hCS : (x * y + L * (1 - x ^ 2)) ^ 2 - 1 = (u * (y - L * x)) ^ 2 := by
      rw [mul_pow u, hu2]; linear_combination hy2
    have hcosh : cosh (arcosh (x * y + L * (1 - x ^ 2))) = x * y + L * (1 - x ^ 2) :=
      cosh_arcosh hC1.le
    have hsinh : sinh (arcosh (x * y + L * (1 - x ^ 2))) = u * (y - L * x) := by
      rw [sinh_arcosh hC1.le, hCS, sqrt_sq (by positivity)]
    have hψ0 : 0 < arcosh (x * y + L * (1 - x ^ 2)) := arcosh_pos hC1
    have harg : √(-(4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2)) *
        (arcosh (x * y + L * (1 - x ^ 2)) * s / (γ * u)) =
        2 * arcosh (x * y + L * (1 - x ^ 2)) := by
      rw [hw]; field_simp
    have hU1 : U1 (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2)
        (arcosh (x * y + L * (1 - x ^ 2)) * s / (γ * u)) =
        2 * (x * y + L * (1 - x ^ 2)) * ((y - L * x) * s / (2 * γ)) := by
      rw [U1_neg hb, harg, hw, sinh_two_mul, hsinh, hcosh]; field_simp
    have hU2 : U2 (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2)
        (arcosh (x * y + L * (1 - x ^ 2)) * s / (γ * u)) =
        2 * ((y - L * x) * s / (2 * γ)) ^ 2 := by
      rw [U2, ite_eq_right hb.ne, U0_neg hb, harg, cosh_two_mul, cosh_sq, hsinh,
        show (1 : ℝ) - x ^ 2 = -u ^ 2 by linarith]
      field_simp; ring
    have hp := (hreach _).mpr ⟨hU2, hU1⟩
    refine ⟨arcosh (x * y + L * (1 - x ^ 2)) * s / (γ * u), by positivity, hp,
      first _ (by positivity) hp (Or.inl hb.le), ?_⟩
    have htof : Lambert.tof L x =
        (arcosh (x * y + L * (1 - x ^ 2)) / u - x + L * y) / (1 - x ^ 2) := by
      have harc : x * y - L * (x ^ 2 - 1) = x * y + L * (1 - x ^ 2) := by ring
      simp only [Lambert.tof, not_lt.mpr hx1.le, hx1.ne', ↓reduceIte, hyOf, hu, harc]
    rw [conicTime, hβ, hU1, hU2, U3, ite_eq_right hb.ne, hU1, hn1, hrv, htof]
    exact time_scalar hs0 hγ0 hu0 (by linarith) hL0 hq hy2 hμγ

/-- **No arrival for `x ≤ -1`.**  For `x ≤ -1`, the motion from `(r1, v1(x))` reaches `r2` at no
positive advance: its conic is a parabola or a hyperbola, so `U1 > 0` for `χ > 0`, while reaching
`r2` needs `U1 = 2 c0 c1 < 0`. -/
theorem izzo_no_arrival {μ : ℝ} (hμ : 0 < μ) {r1 r2 k : V3} (hD : V3.dot (V3.cross r1 r2) k ≠ 0)
    {x : ℝ} (hx : x ≤ -1) {χ : ℝ} (hχ : 0 < χ) : conicPos μ r1 (izzoV1 μ r1 r2 k x) χ ≠ r2 := by
  obtain ⟨s, L, -, y, γ, hs0, -, hLlt, -, hy0, hq, hγ0, hy2, -, -, -, -, -, -, -, hreach⟩ :=
    izzo_target hμ hD x
  intro hpos
  obtain ⟨-, h1⟩ := (hreach χ).mp hpos
  have hb : 4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (by nlinarith)) (by positivity)
  have hU : 0 < U1 (4 * γ ^ 2 * (1 - x ^ 2) / s ^ 2) χ := by
    have := U1_strictMono hb hχ
    rwa [(U_zero _).2.1] at this
  have hd : 0 < y - L * x := by
    have h : (y - L * x) * (y + L * x) = 1 - L ^ 2 := by linear_combination hy2
    have : 0 < (y - L * x) * (y + L * x) := by rw [h]; linarith
    exact (pos_iff_pos_of_mul_pos this).mpr hq
  have hC := c0_neg hx hy0 hd hy2
  have hc1 : 0 < (y - L * x) * s / (2 * γ) := by positivity
  have := mul_neg_of_neg_of_pos hC hc1
  linarith

/-! ### Lambert's theorem -/

/-- The root `x*` of Izzo's equation for the positions, the time of flight, `μ`, and `k`. -/
noncomputable def izzoRoot (r1 r2 : V3) (t μ : ℝ) (k : V3) : ℝ :=
  Lambert.root (izzoParams r1 r2 t μ k).1 (izzoParams r1 r2 t μ k).2

/-- Izzo's `λ` lies strictly between -1 and 1, and `T* > 0` for `t > 0`. -/
theorem izzoParams_bounds {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) {r1 r2 k : V3}
    (hD : V3.dot (V3.cross r1 r2) k ≠ 0) :
    -1 < (izzoParams r1 r2 t μ k).1 ∧ (izzoParams r1 r2 t μ k).1 < 1 ∧
      0 < (izzoParams r1 r2 t μ k).2 := by
  obtain ⟨s, L, -, -, γ, hs0, -, hLlt, -, -, -, hγ0, -, -, hpar, -⟩ := izzo_target hμ hD 0
  obtain ⟨hLp, hTp⟩ := hpar t
  have hb := abs_lt_of_sq_lt_sq' (show L ^ 2 < 1 ^ 2 by rw [one_pow]; exact hLlt) zero_le_one
  rw [hLp, hTp]
  exact ⟨hb.1, hb.2, by positivity⟩

/-- **Lambert's theorem for every conic.**  For `μ > 0`, `t > 0`, and `(r1 × r2) · k ≠ 0`, a
velocity `v` at `r1` starts a motion along a conic in the direction of `k` that first reaches
`r2` after the time `t` exactly when `v` is Izzo's velocity at the root `x*` of Izzo's equation.
By `izzo_target` and `orbitOf_ecc`, the conic is an ellipse, a parabola, or a hyperbola as `x*`
lies below, at, or above 1. -/
theorem lambert_transfer {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) {r1 r2 k : V3}
    (hD : V3.dot (V3.cross r1 r2) k ≠ 0) (v : V3) :
    (ConicTransfer μ r1 v r2 t ∧ 0 < V3.dot (V3.cross r1 v) k) ↔
      v = izzoV1 μ r1 r2 k (izzoRoot r1 r2 t μ k) := by
  unfold izzoRoot
  obtain ⟨hL0, hL1, hT⟩ := izzoParams_bounds hμ ht hD
  obtain ⟨hr0, hrT⟩ := Lambert.root_spec hL0 hL1 hT
  constructor
  · rintro ⟨⟨hh, χ, hχ0, hpos, htime, hfirst⟩, hk⟩
    have s1 := orbitOf_spec hμ (norm_pos_of_cross hh) hh
    have hp2 : OnPath μ (orbitOf μ r1 v) r2 := hpos ▸ conicPos_onPath hμ hh χ
    obtain ⟨x, hx, -⟩ := orbit_izzo hμ hD s1.1 hp2 hk
    have hvx : v = izzoV1 μ r1 r2 k x := s1.2.symm.trans hx
    subst hvx
    have hx1 : -1 < x := by
      by_contra hle
      exact izzo_no_arrival hμ hD (not_lt.mp hle) hχ0 hpos
    obtain ⟨χ', hχ'0, hpos', hfirst', htime'⟩ := izzo_arrival hμ hD hx1 t
    have heq : χ = χ' := by
      rcases lt_trichotomy χ χ' with h | h | h
      · exact absurd hpos (hfirst' χ hχ0 h)
      · exact h
      · exact absurd hpos' (hfirst χ' hχ'0 h)
    rw [← heq, htime] at htime'
    have hTx := (mul_left_cancel₀ ht.ne' htime').symm
    rw [(Lambert.tof_strictAntiOn hL0 hL1).injOn hx1 hr0 (hTx.trans hrT.symm)]
  · rintro rfl
    obtain ⟨χ, hχ0, hpos, hfirst, htime⟩ := izzo_arrival hμ hD hr0 t
    obtain ⟨-, hp1, -, -, -, hk⟩ := izzo_orbit hμ hD
      (Lambert.root (izzoParams r1 r2 t μ k).1 (izzoParams r1 r2 t μ k).2)
    refine ⟨⟨hp1.1, χ, hχ0, hpos, ?_, hfirst⟩, hk⟩
    rw [hrT] at htime
    exact mul_right_cancel₀ hT.ne' htime

/-- A two-body transfer from `(r1, v1)` to `(r2, v2)` in the time `t`: a solution of Newton's
equation on an open interval of times that contains `[0, t]`, which starts at `(r1, v1)`, is at
`(r2, v2)` at the time `t`, and is not at `r2` at any earlier positive time.  The interval admits
a transfer that begins with a manoeuvre at `r1`, before which the motion follows another
orbit. -/
def NewtonTransfer (μ : ℝ) (r1 v1 r2 v2 : V3) (t : ℝ) : Prop :=
  ∃ a b : ℝ, a < 0 ∧ t < b ∧ ∃ R V : ℝ → V3, NewtonOn μ (Set.Ioo a b) R V ∧ R 0 = r1 ∧
    V 0 = v1 ∧ R t = r2 ∧ V t = v2 ∧ ∀ τ, 0 < τ → τ < t → R τ ≠ r2

/-- **Lambert's theorem for Newton's equation.**  For `μ > 0`, `t > 0`, and `(r1 × r2) · k ≠ 0`,
a solution of Newton's equation that starts at `r1` with the velocity `v`, with
`(r1 × v) · k > 0`, first reaches `r2` at the time `t` with the velocity `v'` exactly when
`v = v1(x*)` and `v' = v2(x*)`.  On its interval such a solution is the motion of `conic_newton`
(`newton_unique`), so `lambert_transfer` applies to it. -/
theorem lambert_newton {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) {r1 r2 k : V3}
    (hD : V3.dot (V3.cross r1 r2) k ≠ 0) (v v' : V3) :
    (NewtonTransfer μ r1 v r2 v' t ∧ 0 < V3.dot (V3.cross r1 v) k) ↔
      v = izzoV1 μ r1 r2 k (izzoRoot r1 r2 t μ k) ∧
        v' = izzoV2 μ r1 r2 k (izzoRoot r1 r2 t μ k) := by
  have vend : ∀ R V : ℝ → V3, Newton μ R V → R 0 = r1 →
      V 0 = izzoV1 μ r1 r2 k (izzoRoot r1 r2 t μ k) → R t = r2 →
      V t = izzoV2 μ r1 r2 k (izzoRoot r1 r2 t μ k) := by
    intro R V hN hR0 hV0 hRt
    obtain ⟨-, hp1, hp2, -, hva2, -⟩ := izzo_orbit hμ hD (izzoRoot r1 r2 t μ k)
    have hc := newton_conserves hμ hN t 0
    rw [hR0, hV0, hRt] at hc
    have hht : 0 < V3.dot (V3.cross r2 (V t)) (V3.cross r2 (V t)) := by
      have := hN.h_const t 0
      rw [hR0, hV0, hRt] at this
      rw [this]; exact hp1.1
    have hs := (orbitOf_spec hμ hp2.2.1 hht).2
    rw [hc, hva2] at hs
    exact hs.symm
  constructor
  · rintro ⟨⟨a, b, ha, hb, R, V, hN, hR0, hV0, hRt, hVt, hfirst⟩, hk⟩
    have hh : 0 < V3.dot (V3.cross r1 v) (V3.cross r1 v) := by
      rcases (V3.dot_self_nonneg (V3.cross r1 v)).lt_or_eq with h | h
      · exact h
      · rw [V3.eq_zero_of_dot_self h.symm] at hk; simp [V3.dot] at hk
    obtain ⟨hK, hK0, hKv0⟩ := conic_newton hμ hh
    have hu := newton_unique isOpen_Ioo isPreconnected_Ioo hN (hK.on (Set.Ioo a b))
      ⟨ha, by linarith⟩ (hR0.trans hK0.symm) (hV0.trans hKv0.symm)
    have hR : ∀ τ, 0 ≤ τ → τ ≤ t → R τ = conicPos μ r1 v (conicAdvance μ r1 v τ) :=
      fun τ h0 h1 => (hu τ ⟨by linarith, by linarith⟩).1
    have hKt : conicPos μ r1 v (conicAdvance μ r1 v t) = r2 := (hR t ht.le le_rfl).symm.trans hRt
    have htr : ConicTransfer μ r1 v r2 t := by
      refine ⟨hh, conicAdvance μ r1 v t, ?_, hKt, conicTime_advance hμ hh t, fun χ' h0 h1 heq => ?_⟩
      · have := conicAdvance_strictMono hμ hh ht
        rwa [conicAdvance_zero hμ hh] at this
      · have hτ0 : 0 < conicTime μ r1 v χ' := by
          have := conicTime_strictMono hμ hh h0
          rwa [conic_zero.2.1] at this
        have hτ1 : conicTime μ r1 v χ' < t := by
          have := conicTime_strictMono hμ hh h1
          rwa [conicTime_advance hμ hh] at this
        exact hfirst _ hτ0 hτ1
          (by rw [hR _ hτ0.le hτ1.le, conicAdvance_time hμ hh]; exact heq)
    have hv := (lambert_transfer hμ ht hD v).mp ⟨htr, hk⟩
    subst hv
    have hVt' : V t = conicVel μ r1 _ (conicAdvance μ r1 _ t) :=
      (hu t ⟨by linarith, hb⟩).2
    exact ⟨rfl, hVt.symm.trans (hVt'.trans (vend _ _ hK hK0 hKv0 hKt))⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨⟨hh, χ, hχ0, hpos, htime, hfirst⟩, hk⟩ :=
      (lambert_transfer hμ ht hD (izzoV1 μ r1 r2 k (izzoRoot r1 r2 t μ k))).mpr rfl
    obtain ⟨hN, hR0, hV0⟩ := conic_newton hμ hh
    have hadv := conicAdvance_time hμ hh χ
    rw [htime] at hadv
    have hRt : conicPos μ r1 (izzoV1 μ r1 r2 k (izzoRoot r1 r2 t μ k))
        (conicAdvance μ r1 (izzoV1 μ r1 r2 k (izzoRoot r1 r2 t μ k)) t) = r2 := by
      rw [hadv, hpos]
    refine ⟨⟨-1, t + 1, by norm_num, by linarith, _, _, hN.on _, hR0, hV0, hRt,
      vend _ _ hN hR0 hV0 hRt, fun τ hτ0 hτt heq => ?_⟩, hk⟩
    have a0 := conicAdvance_strictMono hμ hh hτ0
    have a1 := conicAdvance_strictMono hμ hh hτt
    rw [conicAdvance_zero hμ hh] at a0
    rw [hadv] at a1
    exact hfirst _ a0 a1 heq

end Demos.Orbit
