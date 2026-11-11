import Demos.Orbit.LambertOrbit
import Demos.Orbit.LambertRoot

/-!
Lambert's theorem for elliptic transfers.  For `-1 < x < 1`, `izzo_kepler` states that the motion
from Izzo's state `(r1, v1(x))` along its ellipse reaches `r2` when the eccentric anomaly has
advanced by `2ψ` with `0 < ψ < π`, in the time `√(s³/(2μ)) T(x)` of Kepler's equation, where
`ψ = arccos(x y + λ (1 - x²))` and `T` is Izzo's time of flight.  `lambert_time` turns this into
an equivalence: the motion is an elliptic transfer to `r2` in the time `t` exactly when
`T(x) = T*`.  With the converse of the geometry, `orbit_izzo`, and the uniqueness of the root,
`lambert_elliptic` states that the elliptic transfers from `r1` to `r2` in the time `t` in the
direction of `k` are exactly one, Izzo's at the root `x*`, when `x* < 1`, and none otherwise.

The proof follows Lagrange's form of the time.  With `u = √(1 - x²)`, `sin(α/2) = u`,
`cos(α/2) = x`, `sin(β/2) = λ u`, and `cos(β/2) = y`, the orbit's semimajor axis is
`a = s/(2 u²)` (`izzo_energy`), the eccentric anomaly advances by `α - β = 2ψ`, and
`n t = (α - sin α) - (β - sin β)`.  The positions follow from Lagrange's coefficients `f` and
`g` at `2ψ`: in the basis `r1`, `r2` of `izzo_basis`, `f r1 + g v1 = r2` is the pair of scalar
identities `g κ = 1` and `f + g α1 = 0`.
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

/-- `2 N1 C + b1 d = 2 λ`, with `N1 = (1 + ρ + λ² (1 - ρ))/2`, `C = x y + λ (1 - x²)`,
`b1 = (λ y - x) - ρ (λ y + x)`, and `d = y - λ x`. -/
theorem key_one (hL : L ≠ 0) (hq : 0 < y + L * x) (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) :
    2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (x * y + L * (1 - x ^ 2)) +
      ((L * y - x) - ρ * (L * y + x)) * (y - L * x) = 2 * L := by
  obtain ⟨hx, hy'⟩ := xy_subst hL hq hy
  generalize y + L * x = q at hx hy' hq
  subst hx hy'
  field_simp
  ring

/-- The time identity: `(1 - x²) d (b1 d + 2 N1 C) - d C - (λ y - x) = 0`. -/
theorem key_time (hL : L ≠ 0) (hq : 0 < y + L * x) (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) :
    (1 - x ^ 2) * (y - L * x) * (((L * y - x) - ρ * (L * y + x)) * (y - L * x) +
      2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (x * y + L * (1 - x ^ 2))) -
        (y - L * x) * (x * y + L * (1 - x ^ 2)) - (L * y - x) = 0 := by
  obtain ⟨hx, hy'⟩ := xy_subst hL hq hy
  generalize y + L * x = q at hx hy' hq
  subst hx hy'
  field_simp
  ring

/-- `g κ = 1` at the advance `2ψ`. -/
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

/-- `f + g α1 = 0` at the advance `2ψ`. -/
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

end Scalar

/-! ### The time along Izzo's orbit -/

/-- Half the advance of the eccentric anomaly from `r1` to `r2`:
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

/-- **The time along Izzo's elliptic orbit.**  For `-1 < x < 1`, the motion from `(r1, v1(x))`
reaches `r2` when its eccentric anomaly has advanced by `2ψ`, with `0 < ψ < π`, and the time of
Kepler's equation for that advance, multiplied by `T* = √(2μ/s³) t`, is `t T(x)`: the time is
`√(s³/(2μ)) T(x)`. -/
theorem izzo_kepler {μ : ℝ} (hμ : 0 < μ) {r1 r2 k : V3} (hD : V3.dot (V3.cross r1 r2) k ≠ 0)
    {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) (t : ℝ) :
    0 < izzoPsi (izzoParams r1 r2 t μ k).1 x ∧ izzoPsi (izzoParams r1 r2 t μ k).1 x < π ∧
      keplerPos μ r1 (izzoV1 μ r1 r2 k x) (2 * izzoPsi (izzoParams r1 r2 t μ k).1 x) = r2 ∧
      keplerTime μ r1 (izzoV1 μ r1 r2 k x) (2 * izzoPsi (izzoParams r1 r2 t μ k).1 x) *
          (izzoParams r1 r2 t μ k).2 = t * Lambert.tof (izzoParams r1 r2 t μ k).1 x := by
  obtain ⟨s, L, ρ, y, γ, hs, hL, -, hy, -, hs0, hL0, hLlt, hρ2, hy0, hq, hγ0, hy2, hγ2, -, -,
    hc, hn1, hn2, hP, hv1, -⟩ := izzo_basis hμ hD x
  have hLp : (izzoParams r1 r2 t μ k).1 = L := by rw [izzoParams_lam, hL, hs]
  have hTp : (izzoParams r1 r2 t μ k).2 = 2 * γ / s ^ 2 * t := by
    rw [izzoParams_time, ← hs]; exact izzoParams_time_eq hs0 hγ0 hγ2 t
  rw [hLp, hTp]
  have hyOf : Lambert.yOf L x = y := by rw [hy]; rfl
  have hN1 := (factors_pos (L := L) hρ2).1
  have hu1 : 0 < 1 - x ^ 2 := by nlinarith
  set u := √(1 - x ^ 2) with hu
  have hu2 : u ^ 2 = 1 - x ^ 2 := sq_sqrt hu1.le
  have hu0 : 0 < u := sqrt_pos.mpr hu1
  have hd : 0 < y - L * x := by
    have h : (y - L * x) * (y + L * x) = 1 - L ^ 2 := by linear_combination hy2
    have : 0 < (y - L * x) * (y + L * x) := by rw [h]; linarith
    exact (pos_iff_pos_of_mul_pos this).mpr hq
  have hCS : (x * y + L * (1 - x ^ 2)) ^ 2 + (u * (y - L * x)) ^ 2 = 1 := by
    rw [mul_pow u, hu2]; linear_combination hy2
  have hC1 : (x * y + L * (1 - x ^ 2)) ^ 2 ≤ 1 ^ 2 := by
    have := sq_nonneg (u * (y - L * x)); linarith
  have hCb := abs_le_of_sq_le_sq' hC1 zero_le_one
  have hcos : cos (izzoPsi L x) = x * y + L * (1 - x ^ 2) := by
    rw [izzoPsi, hyOf, cos_arccos hCb.1 hCb.2]
  have hsin : sin (izzoPsi L x) = u * (y - L * x) := by
    rw [izzoPsi, hyOf, sin_arccos, show 1 - (x * y + L * (1 - x ^ 2)) ^ 2 = (u * (y - L * x)) ^ 2
      by linarith, sqrt_sq (by positivity)]
  have hsin0 : 0 < sin (izzoPsi L x) := by rw [hsin]; positivity
  have hψ0 : 0 < izzoPsi L x := by
    rcases (arccos_nonneg _).lt_or_eq with h | h
    · exact h
    · rw [izzoPsi, ← h, sin_zero] at hsin0; exact absurd hsin0 (lt_irrefl 0)
  have hψπ : izzoPsi L x < π := by
    rcases (arccos_le_pi (x * Lambert.yOf L x + L * (1 - x ^ 2))).lt_or_eq with h | h
    · exact h
    · rw [izzoPsi, h, sin_pi] at hsin0; exact absurd hsin0 (lt_irrefl 0)
  have hcos2 : cos (2 * izzoPsi L x) = 1 - 2 * (u * (y - L * x)) ^ 2 := by
    rw [cos_two_mul, cos_sq', hsin]; ring
  have hsin2 : sin (2 * izzoPsi L x) = 2 * (u * (y - L * x)) * (x * y + L * (1 - x ^ 2)) := by
    rw [sin_two_mul, hsin, hcos]
  -- the orbit's constants
  have hn1p : 0 < V3.norm r1 := by rw [hn1]; positivity
  have hE := izzo_energy hμ hD x
  rw [← hs] at hE
  have hμγ : μ = 2 * γ ^ 2 / s := by rw [hγ2]; field_simp
  have ha : semimajor μ r1 (izzoV1 μ r1 r2 k x) = s / (2 * u ^ 2) := by
    rw [semimajor, hE, hu2]; field_simp
  have hrv : V3.dot r1 (izzoV1 μ r1 r2 k x) = γ * ((L * y - x) - ρ * (L * y + x)) := by
    rw [hv1, dot_basis_left, ← V3.norm_sq r1]; field_simp; ring
  have hroot : √(μ * semimajor μ r1 (izzoV1 μ r1 r2 k x)) = γ / u := by
    rw [ha, ← sqrt_sq (by positivity : 0 ≤ γ / u), hμγ]
    congr 1
    field_simp
  have hB : eSin μ r1 (izzoV1 μ r1 r2 k x) = u * ((L * y - x) - ρ * (L * y + x)) := by
    rw [eSin, hrv, hroot]; field_simp
  have hA : eCos μ r1 (izzoV1 μ r1 r2 k x) = 1 - 2 * u ^ 2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) := by
    rw [eCos, ha, hn1]; field_simp
  have hnm : meanMotion μ r1 (izzoV1 μ r1 r2 k x) = 4 * γ * u ^ 3 / s ^ 2 := by
    rw [meanMotion, ha, ← sqrt_sq (by positivity : 0 ≤ 4 * γ * u ^ 3 / s ^ 2), hμγ]
    congr 1
    field_simp
    ring
  -- Lagrange's coefficients at `2ψ`
  have hf : 1 - semimajor μ r1 (izzoV1 μ r1 r2 k x) / V3.norm r1 * (1 - cos (2 * izzoPsi L x)) =
      1 - (y - L * x) ^ 2 / ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) := by
    rw [ha, hn1, hcos2]; field_simp; ring
  have hg : (V3.norm r1 / semimajor μ r1 (izzoV1 μ r1 r2 k x) * sin (2 * izzoPsi L x) +
        eSin μ r1 (izzoV1 μ r1 r2 k x) * (1 - cos (2 * izzoPsi L x))) /
        meanMotion μ r1 (izzoV1 μ r1 r2 k x) =
      s ^ 2 * (y - L * x) * (2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (x * y + L * (1 - x ^ 2)) +
        ((L * y - x) - ρ * (L * y + x)) * (y - L * x)) / (2 * γ) := by
    rw [ha, hn1, hcos2, hsin2, hB, hnm]; field_simp; ring
  refine ⟨hψ0, hψπ, ?_, ?_⟩
  · rw [keplerPos, hf, hg, hv1, hP, hn1, hn2, hc]
    exact lagrange_basis (key_g hs0 hL0 hLlt hγ0 hq hy2) (key_f hs0 hL0 hLlt hρ2 hγ0 hq hy2)
  · have kt := key_time (ρ := ρ) hL0 hq hy2
    have hlhs : Sgp4.Kepler.lhs (eCos μ r1 (izzoV1 μ r1 r2 k x)) (-eSin μ r1 (izzoV1 μ r1 r2 k x))
          (2 * izzoPsi L x) + eSin μ r1 (izzoV1 μ r1 r2 k x) =
        2 * (izzoPsi L x + u * (L * y - x)) := by
      rw [Sgp4.Kepler.lhs, hA, hB, hcos2, hsin2]
      linear_combination (2 * u) * kt + (2 * u * (y - L * x) * (((L * y - x) - ρ * (L * y + x)) *
        (y - L * x) + 2 * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (x * y + L * (1 - x ^ 2)))) * hu2
    have htof : Lambert.tof L x = (izzoPsi L x / u - x + L * y) / (1 - x ^ 2) := by
      simp only [Lambert.tof, hx1, ↓reduceIte, izzoPsi, hyOf, hu]
    rw [keplerTime, hlhs, hnm, htof]
    generalize izzoPsi L x = ψ
    rw [← hu2]
    field_simp
    ring

/-! ### Lambert's theorem for ellipses -/

/-- Izzo's `λ` lies strictly between -1 and 1, and `T* > 0` for `t > 0`. -/
theorem izzoParams_bounds {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) {r1 r2 k : V3}
    (hD : V3.dot (V3.cross r1 r2) k ≠ 0) :
    -1 < (izzoParams r1 r2 t μ k).1 ∧ (izzoParams r1 r2 t μ k).1 < 1 ∧
      0 < (izzoParams r1 r2 t μ k).2 := by
  obtain ⟨s, L, -, -, γ, hs, hL, -, -, -, hs0, -, hLlt, -, -, -, hγ0, -, hγ2, -⟩ :=
    izzo_basis hμ hD 0
  have hLp : (izzoParams r1 r2 t μ k).1 = L := by rw [izzoParams_lam, hL, hs]
  have hTp : (izzoParams r1 r2 t μ k).2 = 2 * γ / s ^ 2 * t := by
    rw [izzoParams_time, ← hs]; exact izzoParams_time_eq hs0 hγ0 hγ2 t
  have hb := abs_lt_of_sq_lt_sq' (show L ^ 2 < 1 ^ 2 by rw [one_pow]; exact hLlt) zero_le_one
  rw [hLp, hTp]
  exact ⟨hb.1, hb.2, by positivity⟩

/-- **The time law for Izzo's elliptic orbits.**  For `t > 0` and `-1 < x < 1`, the motion from
`(r1, v1(x))` along its ellipse first reaches `r2` after the time `t` exactly when `x` solves
Izzo's equation `T(x) = T*`. -/
theorem lambert_time {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) {r1 r2 k : V3}
    (hD : V3.dot (V3.cross r1 r2) k ≠ 0) {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    EllipticTransfer μ r1 (izzoV1 μ r1 r2 k x) r2 t ↔
      Lambert.tof (izzoParams r1 r2 t μ k).1 x = (izzoParams r1 r2 t μ k).2 := by
  obtain ⟨hψ0, hψπ, hpos, htime⟩ := izzo_kepler hμ hD hx0 hx1 t
  obtain ⟨-, -, hT⟩ := izzoParams_bounds hμ ht hD
  obtain ⟨-, hp1, -, -, -, -⟩ := izzo_orbit hμ hD x
  obtain ⟨s, -, -, -, -, hs, -, -, -, -, hs0, -⟩ := izzo_basis hμ hD x
  have he : 0 < 2 / V3.norm r1 -
      V3.dot (izzoV1 μ r1 r2 k x) (izzoV1 μ r1 r2 k x) / μ := by
    rw [izzo_energy hμ hD x, ← hs]
    have : 0 < 1 - x ^ 2 := by nlinarith
    positivity
  constructor
  · rintro ⟨-, φ, hφ0, hφ2, hφpos, hφt⟩
    have hφ : φ = 2 * izzoPsi (izzoParams r1 r2 t μ k).1 x := by
      refine keplerPos_inj hμ hp1.2.1 he hp1.1 ?_ (hφpos.trans hpos.symm)
      rw [abs_lt]; constructor <;> linarith
    rw [← hφ, hφt] at htime
    exact (mul_left_cancel₀ ht.ne' htime).symm
  · intro h
    refine ⟨he, 2 * izzoPsi (izzoParams r1 r2 t μ k).1 x, by positivity, by linarith, hpos, ?_⟩
    rw [h] at htime
    exact mul_right_cancel₀ hT.ne' htime

/-- **Lambert's theorem for elliptic transfers.**  For `μ > 0`, `t > 0`, and
`(r1 × r2) · k ≠ 0`, a velocity `v` at `r1` starts a two-body motion in the direction of `k`
that first reaches `r2` along an ellipse after the time `t` exactly when the root `x*` of Izzo's
equation lies below 1 and `v` is Izzo's velocity at `x*`.  So such a transfer exists exactly
when `x* < 1`, and it is unique. -/
theorem lambert_elliptic {μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) {r1 r2 k : V3}
    (hD : V3.dot (V3.cross r1 r2) k ≠ 0) (v : V3) :
    (EllipticTransfer μ r1 v r2 t ∧ 0 < V3.dot (V3.cross r1 v) k) ↔
      Lambert.root (izzoParams r1 r2 t μ k).1 (izzoParams r1 r2 t μ k).2 < 1 ∧
        v = izzoV1 μ r1 r2 k
          (Lambert.root (izzoParams r1 r2 t μ k).1 (izzoParams r1 r2 t μ k).2) := by
  obtain ⟨hL0, hL1, hT⟩ := izzoParams_bounds hμ ht hD
  obtain ⟨hr0, hrT⟩ := Lambert.root_spec hL0 hL1 hT
  constructor
  · rintro ⟨⟨he, φ, hφ0, hφ2, hφpos, hφt⟩, hk⟩
    obtain ⟨s, L, ρ, -, -, hs, -, -, -, -, hs0, -, -, hρ2, -, -, -, -, -, -, -, -, hn1, -⟩ :=
      izzo_basis hμ hD 0
    have hn1p : 0 < V3.norm r1 := by
      rw [hn1]; have := (factors_pos (L := L) hρ2).1; positivity
    have hh : 0 < V3.dot (V3.cross r1 v) (V3.cross r1 v) := by
      rcases (V3.dot_self_nonneg (V3.cross r1 v)).lt_or_eq with h | h
      · exact h
      · rw [V3.eq_zero_of_dot_self h.symm] at hk; simp [V3.dot] at hk
    have s1 := orbitOf_spec hμ hn1p hh
    have hp2 : OnPath μ (orbitOf μ r1 v) r2 := hφpos ▸ keplerPos_onPath hμ hn1p he hh φ
    obtain ⟨x, hx, -⟩ := orbit_izzo hμ hD s1.1 hp2 hk
    have hvx : v = izzoV1 μ r1 r2 k x := s1.2.symm.trans hx
    have hE := izzo_energy hμ hD x
    rw [← hvx, ← hs] at hE
    rw [hE] at he
    have hx2 : 0 < 1 - x ^ 2 := by
      have := mul_pos he (show 0 < s / 2 by positivity)
      rw [show 2 * (1 - x ^ 2) / s * (s / 2) = 1 - x ^ 2 by field_simp] at this
      exact this
    have hxb := abs_lt_of_sq_lt_sq' (show x ^ 2 < 1 ^ 2 by linarith) zero_le_one
    have htr : EllipticTransfer μ r1 (izzoV1 μ r1 r2 k x) r2 t := by
      rw [← hvx]
      have : 0 < 2 / V3.norm r1 - V3.dot v v / μ := by rw [hE]; exact he
      exact ⟨this, φ, hφ0, hφ2, hφpos, hφt⟩
    have hTx := (lambert_time hμ ht hD hxb.1 hxb.2).mp htr
    have hxr : x = Lambert.root (izzoParams r1 r2 t μ k).1 (izzoParams r1 r2 t μ k).2 :=
      (Lambert.tof_strictAntiOn hL0 hL1).injOn hxb.1 hr0 (hTx.trans hrT.symm)
    exact ⟨hxr ▸ hxb.2, hxr ▸ hvx⟩
  · rintro ⟨hr1, rfl⟩
    refine ⟨(lambert_time hμ ht hD hr0 hr1).mpr hrT, ?_⟩
    exact (izzo_orbit hμ hD _).2.2.2.2.2

end Demos.Orbit
