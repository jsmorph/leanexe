import Demos.Orbit.TwoBody

/-!
Gibbs' method over the real numbers.  For three positions `r1`, `r2`, `r3` with lengths `n1`,
`n2`, `n3`, `gibbs` forms `D = r1 × r2 + r2 × r3 + r3 × r1`,
`N = n1 (r2 × r3) + n2 (r3 × r1) + n3 (r1 × r2)`, and
`S = (n2 - n3) r1 + (n3 - n1) r2 + (n1 - n2) r3`, and returns `√(μ/(N · D)) (D × r2/n2 + S)`.
`gibbs_velocity` states that for three positions on the path of one orbit in the order of motion,
`D · h > 0`, the result is the orbit's velocity at `r2`.
-/

namespace Demos.Orbit

open V3

/-- `D`, the normal of the triangle of the three positions. -/
def gibbsD (r1 r2 r3 : V3) : V3 := cross r1 r2 + cross r2 r3 + cross r3 r1

/-- `N`. -/
noncomputable def gibbsN (r1 r2 r3 : V3) : V3 :=
  norm r1 • cross r2 r3 + norm r2 • cross r3 r1 + norm r3 • cross r1 r2

/-- `S`. -/
noncomputable def gibbsS (r1 r2 r3 : V3) : V3 :=
  (norm r2 - norm r3) • r1 + (norm r3 - norm r1) • r2 + (norm r1 - norm r2) • r3

/-- Gibbs' formula for the velocity at `r2`. -/
noncomputable def gibbs (μ : ℝ) (r1 r2 r3 : V3) : V3 :=
  √(μ / dot (gibbsN r1 r2 r3) (gibbsD r1 r2 r3)) •
    ((norm r2)⁻¹ • cross (gibbsD r1 r2 r3) r2 + gibbsS r1 r2 r3)

/-- `(e · r1)(r2 × r3) + (e · r2)(r3 × r1) + (e · r3)(r1 × r2) = (r1 · (r2 × r3)) e`. -/
theorem triple_expansion (e r1 r2 r3 : V3) :
    dot e r1 • cross r2 r3 + dot e r2 • cross r3 r1 + dot e r3 • cross r1 r2 =
      dot r1 (cross r2 r3) • e := by
  ext <;> simp [dot] <;> ring

/-- `S = D × e` when each length is `p - e · r`. -/
theorem gibbsS_eq {e r1 r2 r3 : V3} {p : ℝ} (h1 : norm r1 = p - dot e r1)
    (h2 : norm r2 = p - dot e r2) (h3 : norm r3 = p - dot e r3) :
    gibbsS r1 r2 r3 = cross (gibbsD r1 r2 r3) e := by
  simp only [gibbsS, gibbsD, h1, h2, h3]
  ext <;> simp [dot] <;> ring

/-- `N = p D` for three coplanar positions whose lengths are `p - e · r`. -/
theorem gibbsN_eq {e r1 r2 r3 : V3} {p : ℝ} (h1 : norm r1 = p - dot e r1)
    (h2 : norm r2 = p - dot e r2) (h3 : norm r3 = p - dot e r3)
    (hc : dot r1 (cross r2 r3) = 0) :
    gibbsN r1 r2 r3 = p • gibbsD r1 r2 r3 := by
  have t := triple_expansion e r1 r2 r3
  rw [hc] at t
  simp only [gibbsN, gibbsD, h1, h2, h3]
  ext
  · have := congrArg V3.x t
    simp at this ⊢
    linarith
  · have := congrArg V3.y t
    simp at this ⊢
    linarith
  · have := congrArg V3.z t
    simp at this ⊢
    linarith

/-- **G1.**  For three positions on the path of an orbit with `D · h > 0`, `N · D > 0`, and
Gibbs' formula gives the orbit's velocity at the middle position. -/
theorem gibbs_velocity {μ : ℝ} (hμ : 0 < μ) {o : Conic} {r1 r2 r3 : V3}
    (h1 : OnPath μ o r1) (h2 : OnPath μ o r2) (h3 : OnPath μ o r3)
    (hD : 0 < dot (gibbsD r1 r2 r3) o.h) :
    0 < dot (gibbsN r1 r2 r3) (gibbsD r1 r2 r3) ∧ gibbs μ r1 r2 r3 = velocityAt μ o r2 := by
  rcases o with ⟨H, E⟩
  obtain ⟨hh, hn1, d1, p1⟩ := h1
  obtain ⟨-, hn2, d2, p2⟩ := h2
  obtain ⟨-, -, d3, p3⟩ := h3
  dsimp only at hh hn1 d1 p1 hn2 d2 p2 d3 p3 hD ⊢
  set p := dot H H / μ with hp
  have q1 : norm r1 = p - dot E r1 := by linarith
  have q2 : norm r2 = p - dot E r2 := by linarith
  have q3 : norm r3 = p - dot E r3 := by linarith
  -- `D` is a positive multiple `κ` of `h`.
  have hDh : cross (gibbsD r1 r2 r3) H = 0 := by
    simp only [gibbsD]
    have c12 := cross_eq_smul hh d1 d2
    have c23 := cross_eq_smul hh d2 d3
    have c31 := cross_eq_smul hh d3 d1
    rw [c12, c23, c31]
    ext <;> simp <;> ring
  set κ := dot (gibbsD r1 r2 r3) H / dot H H with hκ
  have hDk : gibbsD r1 r2 r3 = κ • H := eq_smul_of_cross hh hDh
  have hκ0 : 0 < κ := div_pos hD hh
  -- The positions are coplanar.
  have hc : dot r1 (cross r2 r3) = 0 := by
    rw [cross_eq_smul hh d2 d3, dot_smul, d1, mul_zero]
  have hN := gibbsN_eq q1 q2 q3 hc
  have hS := gibbsS_eq q1 q2 q3
  have hp0 : 0 < p := div_pos hh hμ
  have hND : dot (gibbsN r1 r2 r3) (gibbsD r1 r2 r3) = p * κ ^ 2 * dot H H := by
    rw [hN, hDk]
    simp only [dot, smul_x, smul_y, smul_z]
    ring
  refine ⟨by rw [hND]; positivity, ?_⟩
  have hroot : √(μ / dot (gibbsN r1 r2 r3) (gibbsD r1 r2 r3)) = μ / (κ * dot H H) := by
    rw [hND, hp]
    have : μ / (dot H H / μ * κ ^ 2 * dot H H) = (μ / (κ * dot H H)) ^ 2 := by
      field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  simp only [gibbs, velocityAt]
  rw [hroot, hS, hDk]
  have hne : dot H H ≠ 0 := hh.ne'
  have hκne : κ ≠ 0 := hκ0.ne'
  ext <;> simp <;> field_simp <;> ring

end Demos.Orbit
