import Demos.Orbit.LambertBox
import Demos.Orbit.Universal

/-!
Izzo's velocities and the two-body model.  For positions `r1` and `r2` that do not lie on one
line through the origin, an axis `k` with `(r1 × r2) · k ≠ 0`, and every `x`, `izzo_orbit` states
that Izzo's velocities `izzoV1` at `r1` and `izzoV2` at `r2` are the velocities of one orbit
whose angular momentum `h` has `h · k > 0`, and `izzo_energy` that this orbit has
`2/|r1| - |v1|²/μ = 2 (1 - x²)/s`, so that `1 - x² = s/(2a)` for its semimajor axis `a`.
`orbit_izzo` states the converse: every orbit through `r1` and `r2` with `h · k > 0` has the
velocities of Izzo's formulas for some `x`.

The proofs write the velocities in the basis `r1`, `r2` (`izzo_basis`): with `w = r1 × r2` and
`P = r1 · r2`, `v1 = α1 r1 + κ r2` and `v2 = -κ r1 + α2 r2`, so that both states have the angular
momentum `κ w`.  The geometry gives `sg |w| = λ σ c s` (`area_eq`), hence
`κ = γ (y + λ x)/(λ c s)`, and the eccentricity vectors agree when
`v2 - v1 = β ((w × r2)/|r2| - (w × r1)/|r1|)` with `β = μ/(κ |w|²)`, which is the pair of scalar
identities `core_one` and `core_two` in Izzo's normalized variables `c = s (1 - λ²)`,
`|r1| = s (1 + ρ + λ² (1 - ρ))/2`, and `|r2| = s (1 - ρ + λ² (1 + ρ))/2`.
-/

namespace Demos.Orbit

open V3 Real

/-! ### Izzo's quantities -/

/-- The sign of the direction of motion: 1 when `(r1 × r2) · k > 0` and -1 otherwise. -/
noncomputable def motionSign (r1 r2 k : V3) : ℝ := if 0 < dot (cross r1 r2) k then 1 else -1

/-- Izzo's `λ` and `T` for the positions, the time of flight, `μ`, and the axis `k`. -/
noncomputable def izzoParams (r1 r2 : V3) (t μ : ℝ) (k : V3) : ℝ × ℝ :=
  geometry r1.x r1.y r1.z r2.x r2.y r2.z t μ (motionSign r1 r2 k)

/-- Izzo's velocity at `r1` for the parameter `x`. -/
noncomputable def izzoV1 (μ : ℝ) (r1 r2 k : V3) (x : ℝ) : V3 :=
  let v := velocities r1.x r1.y r1.z r2.x r2.y r2.z μ (motionSign r1 r2 k) x
  ⟨v.1, v.2.1, v.2.2.1⟩

/-- Izzo's velocity at `r2` for the parameter `x`. -/
noncomputable def izzoV2 (μ : ℝ) (r1 r2 k : V3) (x : ℝ) : V3 :=
  let v := velocities r1.x r1.y r1.z r2.x r2.y r2.z μ (motionSign r1 r2 k) x
  ⟨v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩

theorem sqrt_max_zero (u : ℝ) : √(max u 0) = √u := by
  rcases le_total 0 u with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, sqrt_zero, sqrt_eq_zero_of_nonpos h]

theorem izzoParams_lam (r1 r2 : V3) (t μ : ℝ) (k : V3) :
    (izzoParams r1 r2 t μ k).1 = motionSign r1 r2 k *
      √(max (1 - norm (r2 - r1) / ((norm r1 + norm r2 + norm (r2 - r1)) / 2)) 0) := rfl

theorem izzoParams_time (r1 r2 : V3) (t μ : ℝ) (k : V3) :
    (izzoParams r1 r2 t μ k).2 = √(2 * μ / (((norm r1 + norm r2 + norm (r2 - r1)) / 2) *
      ((norm r1 + norm r2 + norm (r2 - r1)) / 2) * ((norm r1 + norm r2 + norm (r2 - r1)) / 2))) *
        t := rfl

theorem components_eq {n1 n2 c s μ sg x L y γ ρ σ : ℝ} (hL : L = sg * √(max (1 - c / s) 0))
    (hy : y = √(max (1 - L * L * (1 - x * x)) 0)) (hγ : γ = √(μ * s / 2))
    (hρ : ρ = (n1 - n2) / c) (hσ : σ = √(max (1 - ρ * ρ) 0)) :
    components n1 n2 c s μ sg x = (γ * ((L * y - x) - ρ * (L * y + x)) / n1,
      -(γ * ((L * y - x) + ρ * (L * y + x))) / n2, γ * σ * (y + L * x)) := by
  subst hL hy hγ hρ hσ; rfl

theorem izzoV1_form (μ : ℝ) (r1 r2 k : V3) (x : ℝ) :
    izzoV1 μ r1 r2 k x =
      ((components (norm r1) (norm r2) (norm (r2 - r1))
          ((norm r1 + norm r2 + norm (r2 - r1)) / 2) μ (motionSign r1 r2 k) x).1 / norm r1) • r1 +
        (motionSign r1 r2 k * (components (norm r1) (norm r2) (norm (r2 - r1))
          ((norm r1 + norm r2 + norm (r2 - r1)) / 2) μ (motionSign r1 r2 k) x).2.2 /
          (norm r1 * norm r1 * norm (cross r1 r2))) • cross (cross r1 r2) r1 := by
  ext <;> rfl

theorem izzoV2_form (μ : ℝ) (r1 r2 k : V3) (x : ℝ) :
    izzoV2 μ r1 r2 k x =
      ((components (norm r1) (norm r2) (norm (r2 - r1))
          ((norm r1 + norm r2 + norm (r2 - r1)) / 2) μ (motionSign r1 r2 k) x).2.1 / norm r2) • r2 +
        (motionSign r1 r2 k * (components (norm r1) (norm r2) (norm (r2 - r1))
          ((norm r1 + norm r2 + norm (r2 - r1)) / 2) μ (motionSign r1 r2 k) x).2.2 /
          (norm r2 * norm r2 * norm (cross r1 r2))) • cross (cross r1 r2) r2 := by
  ext <;> rfl

/-! ### Vector identities -/

/-- Lagrange's identity. -/
theorem dot_cross_cross (a b : V3) :
    dot (cross a b) (cross a b) = dot a a * dot b b - dot a b ^ 2 := by
  simp only [dot, cross_x, cross_y, cross_z]; ring

theorem dot_sub_self (a b : V3) : dot (b - a) (b - a) = dot a a + dot b b - 2 * dot a b := by
  simp only [dot, sub_x, sub_y, sub_z]; ring

theorem combine {r1 r2 : V3} {c1 c2 d1 d2 α κ : ℝ} (ha : c1 - c2 * d2 = α) (hk : c2 * d1 = κ) :
    c1 • r1 + c2 • (d1 • r2 - d2 • r1) = α • r1 + κ • r2 := by
  ext <;> simp only [add_x, add_y, add_z, sub_x, sub_y, sub_z, smul_x, smul_y, smul_z]
  · linear_combination r1.x * ha + r2.x * hk
  · linear_combination r1.y * ha + r2.y * hk
  · linear_combination r1.z * ha + r2.z * hk

/-- The triangle of two positions that do not lie on one line through the origin. -/
theorem triangle {r1 r2 : V3} (hw : 0 < dot (cross r1 r2) (cross r1 r2)) :
    0 < norm r1 ∧ 0 < norm r2 ∧ 0 < norm (r2 - r1) ∧
      norm (r2 - r1) ^ 2 = norm r1 ^ 2 + norm r2 ^ 2 - 2 * dot r1 r2 ∧
      dot r1 r2 < norm r1 * norm r2 ∧ -(norm r1 * norm r2) < dot r1 r2 := by
  have l := dot_cross_cross r1 r2
  have h1 := norm_sq r1
  have h2 := norm_sq r2
  have h3 := norm_sq (r2 - r1)
  have e3 := dot_sub_self r1 r2
  have n1 := norm_nonneg r1
  have n2 := norm_nonneg r2
  have n3 := norm_nonneg (r2 - r1)
  have hp : dot r1 r2 ^ 2 < (norm r1 * norm r2) ^ 2 := by
    rw [mul_pow, h1, h2]; nlinarith
  have hn12 : 0 < norm r1 * norm r2 := by
    rcases (mul_nonneg n1 n2).lt_or_eq with h | h
    · exact h
    · rw [← h] at hp; nlinarith [sq_nonneg (dot r1 r2)]
  have hP := abs_lt_of_sq_lt_sq' hp hn12.le
  have p1 : 0 < norm r1 := by
    rcases n1.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hn12; exact absurd hn12 (lt_irrefl 0)
  have p2 : 0 < norm r2 := by
    rcases n2.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hn12; exact absurd hn12 (lt_irrefl 0)
  have hc2 : norm (r2 - r1) ^ 2 = norm r1 ^ 2 + norm r2 ^ 2 - 2 * dot r1 r2 := by
    rw [h3, e3, h1, h2]
  refine ⟨p1, p2, ?_, hc2, hP.2, hP.1⟩
  rcases n3.lt_or_eq with h | h
  · exact h
  · rw [← h] at hc2; nlinarith [sq_nonneg (norm r1 - norm r2)]

/-- `sg |r1 × r2| = λ σ c s`. -/
theorem area_eq {n1 n2 c P s L σ sg wn : ℝ} (hn1 : 0 < n1) (hn2 : 0 < n2) (hc : 0 < c)
    (hc2 : c ^ 2 = n1 ^ 2 + n2 ^ 2 - 2 * P) (hs : s = (n1 + n2 + c) / 2)
    (hL2 : L ^ 2 = 1 - c / s) (hσ2 : σ ^ 2 = 1 - ((n1 - n2) / c) ^ 2) (hσ : 0 ≤ σ)
    (hsg : sg = 1 ∨ sg = -1) (hLs : 0 ≤ sg * L) (hwn : wn ^ 2 = n1 ^ 2 * n2 ^ 2 - P ^ 2)
    (hwn0 : 0 ≤ wn) : sg * wn = L * σ * c * s := by
  have hs0 : 0 < s := by rw [hs]; linarith
  have key : wn ^ 2 = (L * σ * c * s) ^ 2 := by
    rw [hwn, mul_pow, mul_pow, mul_pow, hL2, hσ2, hs]
    field_simp
    linear_combination (c ^ 2 - n1 ^ 2 - n2 ^ 2 - 2 * P) * hc2
  have hsg2 : sg ^ 2 = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num
  have hpos : 0 ≤ sg * (L * σ * c * s) := by
    have : sg * (L * σ * c * s) = (sg * L) * σ * c * s := by ring
    rw [this]; positivity
  have e : wn = sg * (L * σ * c * s) := by
    have h2 : wn ^ 2 = (sg * (L * σ * c * s)) ^ 2 := by rw [mul_pow, hsg2, one_mul, key]
    exact (pow_left_inj₀ hwn0 hpos two_ne_zero).mp h2
  rw [e, ← mul_assoc, ← sq, hsg2, one_mul]

namespace LambertOrbit

theorem core_one {s L ρ x y γ c n1 n2 P κ β a1 : ℝ} (hs : s ≠ 0) (hL : L ≠ 0)
    (hL1 : 1 - L ^ 2 ≠ 0) (hρ1 : 1 - ρ ^ 2 ≠ 0) (hN1 : 1 + ρ + L ^ 2 * (1 - ρ) ≠ 0)
    (hq : y + L * x ≠ 0)
    (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2)
    (hc : c = s * (1 - L ^ 2)) (hn1 : n1 = s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2))
    (hn2 : n2 = s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) (hP : P = n1 * n2 - (1 - ρ ^ 2) * c ^ 2 / 2)
    (hκ : κ = γ * (y + L * x) / (L * c * s))
    (hβ : β = 2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * c))
    (ha : a1 = γ * ((L * y - x) - ρ * (L * y + x)) / n1 ^ 2) :
    -κ - (a1 - κ * P / n1 ^ 2) = β * (P / n1 - n2) := by
  subst hκ hβ ha hP hc hn1 hn2
  have key : -(γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s)) -
      (γ * ((L * y - x) - ρ * (L * y + x)) / (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) ^ 2 -
        γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s) *
          (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
            (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) / (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) ^ 2) -
      2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * (s * (1 - L ^ 2))) *
        ((s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
            (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) / (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) -
          s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) =
      -γ * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (y ^ 2 - (1 - L ^ 2 + L ^ 2 * x ^ 2)) /
        (L * (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) ^ 2 * (y + L * x)) := by
    field_simp
    ring
  rw [hy, sub_self, mul_zero, zero_div] at key
  linarith

theorem core_two {s L ρ x y γ c n1 n2 P κ β a2 : ℝ} (hs : s ≠ 0) (hL : L ≠ 0)
    (hL1 : 1 - L ^ 2 ≠ 0) (hρ1 : 1 - ρ ^ 2 ≠ 0) (hN2 : 1 - ρ + L ^ 2 * (1 + ρ) ≠ 0)
    (hq : y + L * x ≠ 0) (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2)
    (hc : c = s * (1 - L ^ 2)) (hn1 : n1 = s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2))
    (hn2 : n2 = s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) (hP : P = n1 * n2 - (1 - ρ ^ 2) * c ^ 2 / 2)
    (hκ : κ = γ * (y + L * x) / (L * c * s))
    (hβ : β = 2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * c))
    (ha : a2 = -(γ * ((L * y - x) + ρ * (L * y + x))) / n2 ^ 2) :
    (a2 + κ * P / n2 ^ 2) - κ = β * (P / n2 - n1) := by
  subst hκ hβ ha hP hc hn1 hn2
  have key : (-(γ * ((L * y - x) + ρ * (L * y + x))) / (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) ^ 2 +
        γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s) *
          (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
            (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) / (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) ^ 2) -
      γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s) -
      2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * (s * (1 - L ^ 2))) *
        ((s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
            (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) / (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
          s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) =
      -γ * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2) * (y ^ 2 - (1 - L ^ 2 + L ^ 2 * x ^ 2)) /
        (L * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) ^ 2 * (y + L * x)) := by
    field_simp
    ring
  rw [hy, sub_self, mul_zero, zero_div] at key
  linarith

end LambertOrbit

/-! ### Izzo's velocities in the basis `r1`, `r2` -/

/-- Izzo's quantities for two positions with `(r1 × r2) · k ≠ 0`, their relations, and the
velocities in the basis `r1`, `r2`: `s` the semiperimeter, `L` Izzo's `λ`, `ρ = (|r1| - |r2|)/c`,
`y`, and `γ = √(μ s/2)`. -/
theorem izzo_basis {μ : ℝ} (hμ : 0 < μ) {r1 r2 k : V3} (hD : dot (cross r1 r2) k ≠ 0) (x : ℝ) :
    ∃ s L ρ y γ : ℝ,
      s = (norm r1 + norm r2 + norm (r2 - r1)) / 2 ∧
      L = motionSign r1 r2 k * √(max (1 - norm (r2 - r1) / s) 0) ∧
      ρ = (norm r1 - norm r2) / norm (r2 - r1) ∧
      y = √(1 - L ^ 2 * (1 - x ^ 2)) ∧ γ = √(μ * s / 2) ∧
      0 < s ∧ L ≠ 0 ∧ L ^ 2 < 1 ∧ ρ ^ 2 < 1 ∧ 0 < y ∧ 0 < y + L * x ∧ 0 < γ ∧
      y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2 ∧ γ ^ 2 = μ * s / 2 ∧ 0 < L * dot (cross r1 r2) k ∧
      0 < dot (cross r1 r2) (cross r1 r2) ∧
      norm (r2 - r1) = s * (1 - L ^ 2) ∧
      norm r1 = s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) ∧
      norm r2 = s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2) ∧
      dot r1 r2 = norm r1 * norm r2 - (1 - ρ ^ 2) * norm (r2 - r1) ^ 2 / 2 ∧
      izzoV1 μ r1 r2 k x = (γ * ((L * y - x) - ρ * (L * y + x)) / norm r1 ^ 2 -
          γ * (y + L * x) / (L * norm (r2 - r1) * s) * dot r1 r2 / norm r1 ^ 2) • r1 +
        (γ * (y + L * x) / (L * norm (r2 - r1) * s)) • r2 ∧
      izzoV2 μ r1 r2 k x = (-(γ * (y + L * x) / (L * norm (r2 - r1) * s))) • r1 +
        (-(γ * ((L * y - x) + ρ * (L * y + x))) / norm r2 ^ 2 +
          γ * (y + L * x) / (L * norm (r2 - r1) * s) * dot r1 r2 / norm r2 ^ 2) • r2 := by
  have hw : 0 < dot (cross r1 r2) (cross r1 r2) := by
    rcases (dot_self_nonneg (cross r1 r2)).lt_or_eq with h | h
    · exact h
    · exact absurd (by rw [eq_zero_of_dot_self h.symm]; simp [dot]) hD
  obtain ⟨hn1, hn2, hc, hc2, hPlt, hPgt⟩ := triangle hw
  have v1f := izzoV1_form μ r1 r2 k x
  have v2f := izzoV2_form μ r1 r2 k x
  rw [cross_cross_left, dot_comm r2 r1] at v1f
  rw [cross_cross_left] at v2f
  have hsq1 := norm_sq r1
  have hsq2 := norm_sq r2
  have hwn2 : norm (cross r1 r2) ^ 2 = norm r1 ^ 2 * norm r2 ^ 2 - dot r1 r2 ^ 2 := by
    rw [norm_sq, dot_cross_cross, hsq1, hsq2]
  have hwn0 := norm_nonneg (cross r1 r2)
  generalize norm (cross r1 r2) = wn at v1f v2f hwn2 hwn0
  rw [← hsq1] at v1f
  rw [← hsq2] at v2f
  generalize norm r1 = n1 at v1f v2f hwn2 hn1 hc2 hPlt hPgt hsq1 ⊢
  generalize norm r2 = n2 at v1f v2f hwn2 hn2 hc2 hPlt hPgt hsq2 ⊢
  generalize norm (r2 - r1) = c at v1f v2f hc hc2 ⊢
  generalize dot r1 r2 = P at v1f v2f hwn2 hc2 hPlt hPgt ⊢
  have hsg : motionSign r1 r2 k = 1 ∨ motionSign r1 r2 k = -1 := by
    unfold motionSign; split_ifs <;> simp
  have hsgk : 0 < motionSign r1 r2 k * dot (cross r1 r2) k := by
    unfold motionSign; split_ifs with h
    · simpa using h
    · have : dot (cross r1 r2) k < 0 := lt_of_le_of_ne (not_lt.mp h) hD
      linarith
  generalize motionSign r1 r2 k = sg at v1f v2f hsg hsgk ⊢
  have hsg2 : sg ^ 2 = 1 := by rcases hsg with h | h <;> rw [h] <;> norm_num
  have hsg0 : sg ≠ 0 := by rcases hsg with h | h <;> rw [h] <;> norm_num
  set s := (n1 + n2 + c) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hcs : c < n1 + n2 := by
    have h : c ^ 2 < (n1 + n2) ^ 2 := by rw [hc2]; linarith
    exact (abs_lt_of_sq_lt_sq' h (by linarith)).2
  have hm0 : 0 < 1 - c / s := by
    rw [sub_pos, div_lt_one hs0, hs]; linarith
  have hm1 : 1 - c / s < 1 := by
    have : 0 < c / s := div_pos hc hs0
    linarith
  set L := sg * √(max (1 - c / s) 0) with hL
  have hL2 : L ^ 2 = 1 - c / s := by
    rw [hL, mul_pow, hsg2, one_mul, sq_sqrt (le_max_right _ _), max_eq_left hm0.le]
  have hL0 : L ≠ 0 := by
    intro h; rw [h] at hL2; linarith
  have hLs : 0 ≤ sg * L := by
    rw [hL, ← mul_assoc, ← sq, hsg2, one_mul]; exact sqrt_nonneg _
  have hLlt : L ^ 2 < 1 := by rw [hL2]; exact hm1
  set ρ := (n1 - n2) / c with hρ
  have hρ2 : ρ ^ 2 < 1 := by
    rw [hρ, div_pow, div_lt_one (by positivity), hc2]; linarith
  set σ := √(max (1 - ρ * ρ) 0) with hσ
  have hρρ : 0 < 1 - ρ * ρ := by rw [← sq]; linarith
  have hσ2 : σ ^ 2 = 1 - ρ ^ 2 := by
    rw [hσ, sq_sqrt (le_max_right _ _), max_eq_left hρρ.le]; ring
  have hσ0 : 0 < σ := by
    rw [hσ]; apply sqrt_pos.mpr; rw [max_eq_left hρρ.le]; exact hρρ
  set y := √(1 - L ^ 2 * (1 - x ^ 2)) with hy
  have hY : 0 < 1 - L ^ 2 * (1 - x ^ 2) := by
    have := sq_nonneg (L * x)
    rw [show 1 - L ^ 2 * (1 - x ^ 2) = (1 - L ^ 2) + (L * x) ^ 2 by ring]; linarith
  have hy2 : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2 := by
    rw [hy, sq_sqrt hY.le]; ring
  have hy0 : 0 < y := sqrt_pos.mpr hY
  have hq : 0 < y + L * x := by
    by_contra h
    push Not at h
    have h1 : y ≤ -(L * x) := by linarith
    have h2 : y ^ 2 ≤ (-(L * x)) ^ 2 := pow_le_pow_left₀ hy0.le h1 2
    rw [neg_sq, hy2] at h2
    rw [mul_pow] at h2
    linarith
  set γ := √(μ * s / 2) with hγ
  have hγ2 : γ ^ 2 = μ * s / 2 := by rw [hγ, sq_sqrt (by positivity)]
  have hγ0 : 0 < γ := sqrt_pos.mpr (by positivity)
  have hcomp := components_eq (n1 := n1) (n2 := n2) (c := c) (s := s) (μ := μ) (sg := sg) (x := x)
    (L := L) (y := y) (γ := γ) (ρ := ρ) (σ := σ) hL
    (by rw [hy, sqrt_max_zero]; congr 1; ring) hγ hρ hσ
  rw [hcomp] at v1f v2f
  have hwn : sg * wn = L * σ * c * s :=
    area_eq hn1 hn2 hc hc2 hs hL2 (by rw [hσ2, hρ]) hσ0.le hsg hLs hwn2 hwn0
  have hwn' : wn = sg * (L * σ * c * s) := by
    rw [← hwn, ← mul_assoc, ← sq, hsg2, one_mul]
  have hf : ∀ n : ℝ, n ≠ 0 → sg * (γ * σ * (y + L * x)) / (n * n * wn) =
      γ * (y + L * x) / (L * c * s) / n ^ 2 := by
    intro n hn
    rw [hwn', show n * n * (sg * (L * σ * c * s)) = sg * (n * n * (L * σ * c * s)) by ring,
      mul_div_mul_left _ _ hsg0]
    field_simp
  refine ⟨s, L, ρ, y, γ, rfl, rfl, rfl, rfl, rfl, hs0, hL0, hLlt, hρ2, hy0, hq, hγ0, hy2, hγ2,
    ?_, hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e : L * dot (cross r1 r2) k = (sg * L) * (sg * dot (cross r1 r2) k) := by
      linear_combination (-(L * dot (cross r1 r2) k)) * hsg2
    rw [e]
    have : 0 < sg * L := lt_of_le_of_ne hLs (mul_ne_zero hsg0 hL0).symm
    positivity
  · rw [hL2]; field_simp; ring
  · rw [hL2, hρ, hs]; field_simp; ring
  · rw [hL2, hρ, hs]; field_simp; ring
  · rw [hρ]; field_simp; linear_combination hc2
  · rw [v1f, hf n1 hn1.ne']
    apply combine
    · field_simp
    · field_simp
  · rw [v2f, hf n2 hn2.ne']
    ext <;> simp only [add_x, add_y, add_z, sub_x, sub_y, sub_z, smul_x, smul_y, smul_z]
      <;> field_simp <;> ring

/-! ### One orbit -/

theorem e_coord {μ κ β A1 A2 P n1 n2 a b : ℝ} (hμ : μ ≠ 0) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0)
    (hβ : κ * β * (n1 ^ 2 * n2 ^ 2 - P ^ 2) = μ)
    (e : A2 - A1 = β * (P / n1 - n2) * (P * a - n1 ^ 2 * b) +
      β * (P / n2 - n1) * (n2 ^ 2 * a - P * b)) :
    μ⁻¹ * (κ * A2) - n2⁻¹ * b = μ⁻¹ * (κ * A1) - n1⁻¹ * a := by
  have e' : A2 - A1 = β * (n1 ^ 2 * n2 ^ 2 - P ^ 2) * (b / n2 - a / n1) := by
    rw [e]; field_simp; ring
  have h3 : κ * (A2 - A1) = μ * (b / n2 - a / n1) := by rw [e', ← hβ]; ring
  have h4 : μ⁻¹ * (κ * A2) - μ⁻¹ * (κ * A1) = n2⁻¹ * b - n1⁻¹ * a := by
    rw [← mul_sub, ← mul_sub, h3]; field_simp
  linarith

/-- Two states in the basis `r1`, `r2` that satisfy the identities of `core_one` and `core_two`
have one orbit. -/
theorem orbitOf_basis {μ κ β α1 α2 : ℝ} {r1 r2 : V3} (hμ : μ ≠ 0) (hn1 : 0 < norm r1)
    (hn2 : 0 < norm r2)
    (hβ : κ * β * (norm r1 ^ 2 * norm r2 ^ 2 - dot r1 r2 ^ 2) = μ)
    (J1 : -κ - α1 = β * (dot r1 r2 / norm r1 - norm r2))
    (J2 : α2 - κ = β * (dot r1 r2 / norm r2 - norm r1)) :
    orbitOf μ r2 ((-κ) • r1 + α2 • r2) = orbitOf μ r1 (α1 • r1 + κ • r2) := by
  have h1 : cross r1 (α1 • r1 + κ • r2) = κ • cross r1 r2 := by
    ext <;> simp only [cross_x, cross_y, cross_z, add_x, add_y, add_z, smul_x, smul_y, smul_z]
      <;> ring
  have h2 : cross r2 ((-κ) • r1 + α2 • r2) = κ • cross r1 r2 := by
    ext <;> simp only [cross_x, cross_y, cross_z, add_x, add_y, add_z, smul_x, smul_y, smul_z]
      <;> ring
  have hd : cross ((-κ) • r1 + α2 • r2) (cross r1 r2) - cross (α1 • r1 + κ • r2) (cross r1 r2) =
      (β * (dot r1 r2 / norm r1 - norm r2)) • cross r1 (cross r1 r2) +
        (β * (dot r1 r2 / norm r2 - norm r1)) • cross r2 (cross r1 r2) := by
    rw [← J1, ← J2]
    ext <;> simp only [cross_x, cross_y, cross_z, add_x, add_y, add_z, sub_x, sub_y, sub_z,
      smul_x, smul_y, smul_z] <;> ring
  rw [cross_cross_right r1 r1 r2, cross_cross_right r2 r1 r2, ← norm_sq r1, ← norm_sq r2,
    dot_comm r2 r1] at hd
  simp only [orbitOf, h1, h2, cross_smul]
  congr 1
  ext
  · have e := congrArg V3.x hd
    simp only [sub_x, add_x, smul_x] at e
    simp only [sub_x, smul_x]
    exact e_coord hμ hn1.ne' hn2.ne' hβ e
  · have e := congrArg V3.y hd
    simp only [sub_y, add_y, smul_y] at e
    simp only [sub_y, smul_y]
    exact e_coord hμ hn1.ne' hn2.ne' hβ e
  · have e := congrArg V3.z hd
    simp only [sub_z, add_z, smul_z] at e
    simp only [sub_z, smul_z]
    exact e_coord hμ hn1.ne' hn2.ne' hβ e

theorem cross_basis' (a b : ℝ) (r1 r2 : V3) :
    cross r2 ((-a) • r1 + b • r2) = a • cross r1 r2 := by
  ext <;> simp only [cross_x, cross_y, cross_z, add_x, add_y, add_z, smul_x, smul_y, smul_z]
    <;> ring

/-- The positive factors `1 + ρ + λ² (1 - ρ)` and `1 - ρ + λ² (1 + ρ)`. -/
theorem factors_pos {L ρ : ℝ} (hρ : ρ ^ 2 < 1) :
    0 < 1 + ρ + L ^ 2 * (1 - ρ) ∧ 0 < 1 - ρ + L ^ 2 * (1 + ρ) := by
  have h := abs_lt_of_sq_lt_sq' (show ρ ^ 2 < 1 ^ 2 by rw [one_pow]; exact hρ) one_pos.le
  have h1 : 0 ≤ L ^ 2 * (1 - ρ) := mul_nonneg (sq_nonneg L) (by linarith)
  have h2 : 0 ≤ L ^ 2 * (1 + ρ) := mul_nonneg (sq_nonneg L) (by linarith)
  constructor <;> linarith

/-- **Geometry of Izzo's solution.**  For every `x`, the states `(r1, v1(x))` and
`(r2, v2(x))` have one orbit: both positions lie on its path, its velocities there are Izzo's,
and its angular momentum `h` has `h · k > 0`. -/
theorem izzo_orbit {μ : ℝ} (hμ : 0 < μ) {r1 r2 k : V3} (hD : dot (cross r1 r2) k ≠ 0) (x : ℝ) :
    orbitOf μ r2 (izzoV2 μ r1 r2 k x) = orbitOf μ r1 (izzoV1 μ r1 r2 k x) ∧
      OnPath μ (orbitOf μ r1 (izzoV1 μ r1 r2 k x)) r1 ∧
      OnPath μ (orbitOf μ r1 (izzoV1 μ r1 r2 k x)) r2 ∧
      velocityAt μ (orbitOf μ r1 (izzoV1 μ r1 r2 k x)) r1 = izzoV1 μ r1 r2 k x ∧
      velocityAt μ (orbitOf μ r1 (izzoV1 μ r1 r2 k x)) r2 = izzoV2 μ r1 r2 k x ∧
      0 < dot (orbitOf μ r1 (izzoV1 μ r1 r2 k x)).h k := by
  obtain ⟨s, L, ρ, y, γ, -, -, -, -, -, hs0, hL0, hLlt, hρ2, -, hq, hγ0, hy2, hγ2, hLk, hw, hc,
    hn1, hn2, hP, hv1, hv2⟩ := izzo_basis hμ hD x
  obtain ⟨hN1, hN2⟩ := factors_pos (L := L) hρ2
  have hL1 : 1 - L ^ 2 ≠ 0 := by linarith
  have hρ1 : 1 - ρ ^ 2 ≠ 0 := by linarith
  have J1 := LambertOrbit.core_one (κ := γ * (y + L * x) / (L * norm (r2 - r1) * s))
    (β := 2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * norm (r2 - r1))) hs0.ne' hL0 hL1
    hρ1 hN1.ne' hq.ne' hy2 hc hn1 hn2 hP rfl rfl rfl
  have J2 := LambertOrbit.core_two (κ := γ * (y + L * x) / (L * norm (r2 - r1) * s))
    (β := 2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * norm (r2 - r1))) hs0.ne' hL0 hL1
    hρ1 hN2.ne' hq.ne' hy2 hc hn1 hn2 hP rfl rfl rfl
  have hn1p : 0 < norm r1 := by rw [hn1]; positivity
  have hn2p : 0 < norm r2 := by rw [hn2]; positivity
  have hμγ : μ = 2 * γ ^ 2 / s := by rw [hγ2]; field_simp
  have hβ : γ * (y + L * x) / (L * norm (r2 - r1) * s) *
      (2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * norm (r2 - r1))) *
        (norm r1 ^ 2 * norm r2 ^ 2 - dot r1 r2 ^ 2) = μ := by
    rw [hP, hn1, hn2, hc, hμγ]
    field_simp
    ring
  have heq := orbitOf_basis hμ.ne' hn1p hn2p hβ J1 J2
  rw [← hv1, ← hv2] at heq
  set κ := γ * (y + L * x) / (L * norm (r2 - r1) * s)
  have hκ : 0 < κ * L := by
    have : κ * L = γ * (y + L * x) / (norm (r2 - r1) * s) := by
      simp only [κ]; field_simp
    rw [this, hc]
    have : 0 < 1 - L ^ 2 := by linarith
    positivity
  have hκ0 : κ ≠ 0 := by intro h; rw [h, zero_mul] at hκ; exact lt_irrefl 0 hκ
  have hκw : 0 < dot (κ • cross r1 r2) (κ • cross r1 r2) := by
    rw [dot_smul, dot_comm, dot_smul]
    have := mul_pos (mul_self_pos.mpr hκ0) hw
    linarith [this, show κ * (κ * dot (cross r1 r2) (cross r1 r2)) =
      κ * κ * dot (cross r1 r2) (cross r1 r2) by ring]
  have hc1 : cross r1 (izzoV1 μ r1 r2 k x) = κ • cross r1 r2 := by rw [hv1, cross_basis]
  have hc2 : cross r2 (izzoV2 μ r1 r2 k x) = κ • cross r1 r2 := by rw [hv2, cross_basis']
  have s1 := orbitOf_spec (v := izzoV1 μ r1 r2 k x) hμ hn1p (by rw [hc1]; exact hκw)
  have s2 := orbitOf_spec (v := izzoV2 μ r1 r2 k x) hμ hn2p (by rw [hc2]; exact hκw)
  rw [heq] at s2
  refine ⟨heq, s1.1, s2.1, s1.2, s2.2, ?_⟩
  show 0 < dot (cross r1 _) k
  rw [hc1, dot_comm, dot_smul, dot_comm]
  have e : κ * dot (cross r1 r2) k = (κ * L) * (L * dot (cross r1 r2) k) / L ^ 2 := by
    field_simp
  rw [e]
  positivity

/-- For `q = y + λ x > 0` and `λ ≠ 0`, `x` and `y` are rational functions of `q`. -/
theorem xy_of_q {L x y q : ℝ} (hL : L ≠ 0) (hq : y + L * x = q) (hq0 : 0 < q)
    (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2) :
    x = (q ^ 2 - (1 - L ^ 2)) / (2 * L * q) ∧ y = (q ^ 2 + (1 - L ^ 2)) / (2 * q) := by
  have hy' : y = q - L * x := by linarith
  have hx : x = (q ^ 2 - (1 - L ^ 2)) / (2 * L * q) := by
    rw [eq_div_iff (by positivity)]
    rw [hy'] at hy
    linear_combination -hy
  refine ⟨hx, ?_⟩
  rw [hy', hx]
  field_simp
  ring

/-- **The energy of Izzo's orbit.**  `2/|r1| - |v1|²/μ = 2 (1 - x²)/s`.  By `orbitOf_ecc` the
orbit is an ellipse for `|x| < 1`, with the semimajor axis `a = s/(2 (1 - x²))`, a parabola for
`|x| = 1`, and a hyperbola for `|x| > 1`. -/
theorem izzo_energy {μ : ℝ} (hμ : 0 < μ) {r1 r2 k : V3} (hD : dot (cross r1 r2) k ≠ 0)
    (x : ℝ) :
    2 / norm r1 - dot (izzoV1 μ r1 r2 k x) (izzoV1 μ r1 r2 k x) / μ =
      2 * (1 - x ^ 2) / ((norm r1 + norm r2 + norm (r2 - r1)) / 2) := by
  obtain ⟨s, L, ρ, y, γ, hs, -, -, -, -, hs0, hL0, hLlt, hρ2, -, hq, hγ0, hy2, hγ2, -, -, hc,
    hn1, hn2, hP, hv1, -⟩ := izzo_basis hμ hD x
  obtain ⟨hN1, hN2⟩ := factors_pos (L := L) hρ2
  rw [← hs, hv1, dot_basis, ← norm_sq r1, ← norm_sq r2, hP, hn1, hn2, hc]
  have hμγ : μ = 2 * γ ^ 2 / s := by rw [hγ2]; field_simp
  rw [hμγ]
  generalize hqd : y + L * x = q at hq
  obtain ⟨hx, hy⟩ := xy_of_q hL0 hqd hq hy2
  subst hx hy
  have hL1 : 0 < 1 - L ^ 2 := by linarith
  field_simp
  ring

/-- The velocity of an orbit depends on `h` and on the component of `e` normal to `h`. -/
theorem velocityAt_congr {μ : ℝ} {o o' : Conic} (r : V3) (hh : o.h = o'.h)
    (he : cross o.h (o.e - o'.e) = 0) : velocityAt μ o r = velocityAt μ o' r := by
  simp only [velocityAt, ← hh]
  have ex := congrArg V3.x he
  have ey := congrArg V3.y he
  have ez := congrArg V3.z he
  simp only [cross_x, cross_y, cross_z, sub_x, sub_y, sub_z, zero_x, zero_y, zero_z] at ex ey ez
  ext <;> simp only [smul_x, smul_y, smul_z, cross_x, cross_y, cross_z, add_x, add_y, add_z]
  · linear_combination (μ / dot o.h o.h) * ex
  · linear_combination (μ / dot o.h o.h) * ey
  · linear_combination (μ / dot o.h o.h) * ez

theorem dot_sub_left (a b c : V3) : dot (a - b) c = dot a c - dot b c := by
  simp only [dot, sub_x, sub_y, sub_z]; ring

/-- **Every orbit through the two positions is Izzo's.**  An orbit whose path holds `r1` and
`r2` and whose angular momentum `h` has `h · k > 0` has at `r1` and `r2` the velocities of
Izzo's formulas for some `x`. -/
theorem orbit_izzo {μ : ℝ} (hμ : 0 < μ) {r1 r2 k : V3} (hD : dot (cross r1 r2) k ≠ 0)
    {o : Conic} (h1 : OnPath μ o r1) (h2 : OnPath μ o r2) (hk : 0 < dot o.h k) :
    ∃ x, velocityAt μ o r1 = izzoV1 μ r1 r2 k x ∧ velocityAt μ o r2 = izzoV2 μ r1 r2 k x := by
  obtain ⟨s, L, ρ, -, γ, hs, hL, -, -, hγ, hs0, hL0, hLlt, -, -, -, hγ0, -, -, hLk, hw, hc,
    -, -, -, -, -⟩ := izzo_basis hμ hD 0
  have hcw : cross o.h (cross r1 r2) = 0 := by
    rw [cross_cross_right, dot_comm o.h r2, h2.2.2.1, dot_comm o.h r1, h1.2.2.1]
    ext <;> simp
  have hhw := eq_smul_of_cross hw hcw
  set κ' := dot o.h (cross r1 r2) / dot (cross r1 r2) (cross r1 r2) with hκ'
  have hk' : 0 < κ' * dot (cross r1 r2) k := by
    rw [hhw, dot_comm, dot_smul, dot_comm] at hk; exact hk
  have hκL : 0 < κ' * L := by
    have h := mul_pos hk' hLk
    rw [show κ' * dot (cross r1 r2) k * (L * dot (cross r1 r2) k) =
      (κ' * L) * dot (cross r1 r2) k ^ 2 by ring] at h
    by_contra hn
    push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg (dot (cross r1 r2) k))
    linarith
  have hL1 : 0 < 1 - L ^ 2 := by linarith
  have hcpos : 0 < norm (r2 - r1) := by rw [hc]; positivity
  set q := (κ' * L) * norm (r2 - r1) * s / γ with hqd
  have hq0 : 0 < q := div_pos (mul_pos (mul_pos hκL hcpos) hs0) hγ0
  refine ⟨(q ^ 2 - (1 - L ^ 2)) / (2 * L * q), ?_⟩
  obtain ⟨s', L', ρ', y, γ', hs', hL', -, -, hγ', -, -, -, -, hy0, -, -, hy2, -, -, -, -, -, -, -,
    hv1, hv2⟩ := izzo_basis hμ hD ((q ^ 2 - (1 - L ^ 2)) / (2 * L * q))
  have es : s' = s := by rw [hs, hs']
  have eL : L' = L := by rw [hL, hL', es]
  have eγ : γ' = γ := by rw [hγ, hγ', es]
  rw [es, eL, eγ] at hv1 hv2
  rw [eL] at hy2
  have hY : y = (q ^ 2 + (1 - L ^ 2)) / (2 * q) := by
    have hpos : 0 < (q ^ 2 + (1 - L ^ 2)) / (2 * q) := by positivity
    have hsq : y ^ 2 = ((q ^ 2 + (1 - L ^ 2)) / (2 * q)) ^ 2 := by
      rw [hy2]; field_simp; ring
    exact (pow_left_inj₀ hy0.le hpos.le two_ne_zero).mp hsq
  have hyq : y + L * ((q ^ 2 - (1 - L ^ 2)) / (2 * L * q)) = q := by
    rw [hY]; field_simp; ring
  have hκ : γ * q / (L * norm (r2 - r1) * s) = κ' := by
    rw [hqd]; field_simp
  rw [hyq, hκ] at hv1 hv2
  obtain ⟨heq, hp1, hp2, hva1, hva2, -⟩ := izzo_orbit hμ hD ((q ^ 2 - (1 - L ^ 2)) / (2 * L * q))
  set o' := orbitOf μ r1 (izzoV1 μ r1 r2 k ((q ^ 2 - (1 - L ^ 2)) / (2 * L * q)))
  have hh : o.h = o'.h := by
    show o.h = cross r1 _
    rw [hv1, cross_basis, ← hhw]
  have hd1 : dot (o.e - o'.e) r1 = 0 := by
    have e1 := h1.2.2.2
    rw [hh] at e1
    rw [dot_sub_left]; linarith [hp1.2.2.2]
  have hd2 : dot (o.e - o'.e) r2 = 0 := by
    have e2 := h2.2.2.2
    rw [hh] at e2
    rw [dot_sub_left]; linarith [hp2.2.2.2]
  have he : cross o.h (o.e - o'.e) = 0 := by
    rw [hhw, smul_cross, cross_cross_left, dot_comm r1, hd1, dot_comm r2, hd2]
    ext <;> simp
  exact ⟨(velocityAt_congr r1 hh he).trans hva1, (velocityAt_congr r2 hh he).trans hva2⟩

end Demos.Orbit
