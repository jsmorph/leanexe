import Demos.Orbit.Vector

/-!
The two-body model of the demo.  For a gravitational parameter `μ > 0`, an orbit is a pair of
vectors `(h, e)`, the angular momentum per unit mass and the eccentricity vector.  Its path is the
set of positions `r` with `r · h = 0` and `|r| + e · r = |h|²/μ`, the polar equation of a conic
with a focus at the origin, and its velocity at a position `r` of the path is
`(μ/|h|²) h × (e + r/|r|)`.  `orbitOf_spec` states that a state `(r, v)` with `r × v ≠ 0` lies on
the path of its orbit `(r × v, v × (r × v)/μ - r/|r|)` with the velocity `v`.
-/

namespace Demos.Orbit

open V3

/-- An orbit's conic: the angular momentum per unit mass `h` and the eccentricity vector `e`. -/
structure Conic where
  h : V3
  e : V3

/-- `r` lies on the path of the orbit `o` for the gravitational parameter `μ`: the angular
momentum is not zero, `r` is not zero, `r` is normal to `h`, and `|r| + e · r = |h|²/μ`. -/
def OnPath (μ : ℝ) (o : Conic) (r : V3) : Prop :=
  0 < dot o.h o.h ∧ 0 < norm r ∧ dot r o.h = 0 ∧ norm r + dot o.e r = dot o.h o.h / μ

/-- The velocity of the orbit `o` at the position `r` of its path. -/
noncomputable def velocityAt (μ : ℝ) (o : Conic) (r : V3) : V3 :=
  (μ / dot o.h o.h) • cross o.h (o.e + (norm r)⁻¹ • r)

/-- The orbit of the state `(r, v)`. -/
noncomputable def orbitOf (μ : ℝ) (r v : V3) : Conic :=
  ⟨cross r v, μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r⟩

/-- A state with `r × v ≠ 0` lies on the path of its orbit, with the velocity `v`. -/
theorem orbitOf_spec {μ : ℝ} (hμ : 0 < μ) {r v : V3} (hr : 0 < norm r)
    (hh : 0 < dot (cross r v) (cross r v)) :
    OnPath μ (orbitOf μ r v) r ∧ velocityAt μ (orbitOf μ r v) r = v := by
  have hn2 := norm_sq r
  refine ⟨⟨hh, hr, dot_cross_self r v, ?_⟩, ?_⟩
  · simp only [orbitOf]
    have e1 : dot (μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r) r =
        μ⁻¹ * dot (cross r v) (cross r v) - (norm r)⁻¹ * dot r r := by
      simp only [dot, sub_x, sub_y, sub_z, smul_x, smul_y, smul_z, cross_x, cross_y, cross_z]
      ring
    rw [e1, ← hn2]
    field_simp
    ring
  · simp only [velocityAt, orbitOf]
    have hv : dot (cross r v) v = 0 := by rw [dot_comm]; exact dot_cross_self' r v
    have e2 : cross (cross r v) (μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r + (norm r)⁻¹ • r)
        = μ⁻¹ • (dot (cross r v) (cross r v) • v) := by
      have : μ⁻¹ • cross v (cross r v) - (norm r)⁻¹ • r + (norm r)⁻¹ • r =
          μ⁻¹ • cross v (cross r v) := by ext <;> simp
      rw [this, cross_smul, cross_cross_right, hv]
      congr 1
      ext <;> simp
    rw [e2]
    ext <;> simp <;> field_simp

end Demos.Orbit
