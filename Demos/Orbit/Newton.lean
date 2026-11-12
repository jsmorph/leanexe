import Demos.Orbit.Gibbs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-!
Newton's two-body equation `r'' = -μ r/|r|³` conserves the angular momentum `r × r'` and the
eccentricity vector `r' × (r × r')/μ - r/|r|` (`newton_conserves`), so the positions of a solution
lie on the path of one orbit and its velocity at each of them is that orbit's velocity.
`gibbs_newton` states Gibbs' theorem for three positions of a solution.  `Newton` states the
equation at every time, and `NewtonOn` at the times of a given set.
-/

namespace Demos.Orbit

open V3

/-- `r` and `v` solve Newton's two-body equation on the whole line: `r' = v`,
`v' = -μ r/|r|³`, and `r` stays away from the origin. -/
structure Newton (μ : ℝ) (r v : ℝ → V3) : Prop where
  pos : ∀ t, 0 < norm (r t)
  dx : ∀ t, HasDerivAt (fun s => (r s).x) (v t).x t
  dy : ∀ t, HasDerivAt (fun s => (r s).y) (v t).y t
  dz : ∀ t, HasDerivAt (fun s => (r s).z) (v t).z t
  ax : ∀ t, HasDerivAt (fun s => (v s).x) (-μ * (r t).x / norm (r t) ^ 3) t
  ay : ∀ t, HasDerivAt (fun s => (v s).y) (-μ * (r t).y / norm (r t) ^ 3) t
  az : ∀ t, HasDerivAt (fun s => (v s).z) (-μ * (r t).z / norm (r t) ^ 3) t

/-- `r` and `v` solve Newton's two-body equation at the times of the set `I`: at each of them
`r' = v`, `v' = -μ r/|r|³`, and `r` is away from the origin. -/
structure NewtonOn (μ : ℝ) (I : Set ℝ) (r v : ℝ → V3) : Prop where
  pos : ∀ t ∈ I, 0 < norm (r t)
  dx : ∀ t ∈ I, HasDerivAt (fun s => (r s).x) (v t).x t
  dy : ∀ t ∈ I, HasDerivAt (fun s => (r s).y) (v t).y t
  dz : ∀ t ∈ I, HasDerivAt (fun s => (r s).z) (v t).z t
  ax : ∀ t ∈ I, HasDerivAt (fun s => (v s).x) (-μ * (r t).x / norm (r t) ^ 3) t
  ay : ∀ t ∈ I, HasDerivAt (fun s => (v s).y) (-μ * (r t).y / norm (r t) ^ 3) t
  az : ∀ t ∈ I, HasDerivAt (fun s => (v s).z) (-μ * (r t).z / norm (r t) ^ 3) t

/-- A solution on the whole line solves Newton's equation on every set of times. -/
theorem Newton.on {μ : ℝ} {r v : ℝ → V3} (hN : Newton μ r v) (I : Set ℝ) : NewtonOn μ I r v :=
  ⟨fun t _ => hN.pos t, fun t _ => hN.dx t, fun t _ => hN.dy t, fun t _ => hN.dz t,
    fun t _ => hN.ax t, fun t _ => hN.ay t, fun t _ => hN.az t⟩

theorem const_of_hasDerivAt_zero {f : ℝ → ℝ} (h : ∀ t, HasDerivAt f 0 t) (t s : ℝ) :
    f t = f s :=
  is_const_of_deriv_eq_zero (fun t => (h t).differentiableAt) (fun t => (h t).deriv) t s

variable {μ : ℝ} {r v : ℝ → V3}

/-- The derivative of the length of a solution's position. -/
theorem Newton.norm_deriv (hN : Newton μ r v) (t : ℝ) :
    HasDerivAt (fun s => V3.norm (r s)) (dot (r t) (v t) / V3.norm (r t)) t := by
  have hd : HasDerivAt (fun s => (r s).x * (r s).x + (r s).y * (r s).y + (r s).z * (r s).z)
      (2 * dot (r t) (v t)) t :=
    ((((hN.dx t).fun_mul (hN.dx t)).fun_add ((hN.dy t).fun_mul (hN.dy t))).fun_add
      ((hN.dz t).fun_mul (hN.dz t))).congr_deriv (by simp only [dot]; ring)
  have hn := hN.pos t
  have hpos : (r t).x * (r t).x + (r t).y * (r t).y + (r t).z * (r t).z ≠ 0 := by
    have := norm_sq (r t)
    simp only [dot] at this
    rw [← this]; positivity
  exact (hd.sqrt hpos).congr_deriv (by
    show 2 * dot (r t) (v t) / (2 * V3.norm (r t)) = _
    field_simp)

theorem Newton.h_deriv (hN : Newton μ r v) (t : ℝ) :
    HasDerivAt (fun s => (cross (r s) (v s)).x) 0 t ∧
      HasDerivAt (fun s => (cross (r s) (v s)).y) 0 t ∧
      HasDerivAt (fun s => (cross (r s) (v s)).z) 0 t :=
  ⟨(((hN.dy t).fun_mul (hN.az t)).fun_sub ((hN.dz t).fun_mul (hN.ay t))).congr_deriv (by ring),
    (((hN.dz t).fun_mul (hN.ax t)).fun_sub ((hN.dx t).fun_mul (hN.az t))).congr_deriv (by ring),
    (((hN.dx t).fun_mul (hN.ay t)).fun_sub ((hN.dy t).fun_mul (hN.ax t))).congr_deriv (by ring)⟩

/-- The angular momentum of a solution is constant. -/
theorem Newton.h_const (hN : Newton μ r v) (t s : ℝ) :
    cross (r t) (v t) = cross (r s) (v s) := by
  ext
  · exact const_of_hasDerivAt_zero (fun t => (hN.h_deriv t).1) t s
  · exact const_of_hasDerivAt_zero (fun t => (hN.h_deriv t).2.1) t s
  · exact const_of_hasDerivAt_zero (fun t => (hN.h_deriv t).2.2) t s

/-- The eccentricity vector with a fixed angular momentum `h0` has derivative zero along a
solution whose angular momentum is `h0`. -/
theorem Newton.e_deriv (hμ : 0 < μ) (hN : Newton μ r v) (h0 : V3)
    (hh : ∀ t, cross (r t) (v t) = h0) (t : ℝ) :
    HasDerivAt (fun s => (μ⁻¹ • cross (v s) h0 - (V3.norm (r s))⁻¹ • r s).x) 0 t ∧
      HasDerivAt (fun s => (μ⁻¹ • cross (v s) h0 - (V3.norm (r s))⁻¹ • r s).y) 0 t ∧
      HasDerivAt (fun s => (μ⁻¹ • cross (v s) h0 - (V3.norm (r s))⁻¹ • r s).z) 0 t := by
  have hn := (hN.pos t).ne'
  have hμ' := hμ.ne'
  have hsq := norm_sq (r t)
  have hinv := (hN.norm_deriv t).fun_inv hn
  have e0 := hh t
  have ex : h0.x = (r t).y * (v t).z - (r t).z * (v t).y := by rw [← e0]; rfl
  have ey : h0.y = (r t).z * (v t).x - (r t).x * (v t).z := by rw [← e0]; rfl
  have ez : h0.z = (r t).x * (v t).y - (r t).y * (v t).x := by rw [← e0]; rfl
  simp only [dot] at hsq
  refine ⟨?_, ?_, ?_⟩
  · refine (((((hN.ay t).mul_const h0.z).fun_sub ((hN.az t).mul_const h0.y)).const_mul
      μ⁻¹).fun_sub (hinv.fun_mul (hN.dx t))).congr_deriv ?_
    simp only [ex, ey, ez, dot]
    field_simp
    linear_combination (-(v t).x) * hsq
  · refine (((((hN.az t).mul_const h0.x).fun_sub ((hN.ax t).mul_const h0.z)).const_mul
      μ⁻¹).fun_sub (hinv.fun_mul (hN.dy t))).congr_deriv ?_
    simp only [ex, ey, ez, dot]
    field_simp
    linear_combination (-(v t).y) * hsq
  · refine (((((hN.ax t).mul_const h0.y).fun_sub ((hN.ay t).mul_const h0.x)).const_mul
      μ⁻¹).fun_sub (hinv.fun_mul (hN.dz t))).congr_deriv ?_
    simp only [ex, ey, ez, dot]
    field_simp
    linear_combination (-(v t).z) * hsq

/-- **Conservation.**  The orbit of a solution's state is the same at every time. -/
theorem newton_conserves (hμ : 0 < μ) (hN : Newton μ r v) (t s : ℝ) :
    orbitOf μ (r t) (v t) = orbitOf μ (r s) (v s) := by
  have hh : ∀ u, cross (r u) (v u) = cross (r s) (v s) := fun u => hN.h_const u s
  have he := hN.e_deriv hμ (cross (r s) (v s)) hh
  simp only [orbitOf, hh t, hh s]
  congr 1
  ext
  · exact const_of_hasDerivAt_zero (fun u => (he u).1) t s
  · exact const_of_hasDerivAt_zero (fun u => (he u).2.1) t s
  · exact const_of_hasDerivAt_zero (fun u => (he u).2.2) t s

/-- **G1 for Newton's equation.**  For three positions of a solution with `D · h > 0`, where `h`
is the solution's angular momentum, Gibbs' formula gives the solution's velocity at the middle
time. -/
theorem gibbs_newton (hμ : 0 < μ) (hN : Newton μ r v) {t1 t2 t3 : ℝ}
    (hD : 0 < dot (gibbsD (r t1) (r t2) (r t3)) (cross (r t2) (v t2))) :
    gibbs μ (r t1) (r t2) (r t3) = v t2 := by
  have hh : 0 < dot (cross (r t2) (v t2)) (cross (r t2) (v t2)) := by
    rcases (dot_self_nonneg (cross (r t2) (v t2))).lt_or_eq with h | h
    · exact h
    · have := eq_zero_of_dot_self h.symm
      rw [this] at hD
      simp [dot] at hD
  have on : ∀ t, OnPath μ (orbitOf μ (r t2) (v t2)) (r t) := by
    intro t
    have hht : 0 < dot (cross (r t) (v t)) (cross (r t) (v t)) := by
      rw [hN.h_const t t2]; exact hh
    rw [← newton_conserves hμ hN t t2]
    exact (orbitOf_spec hμ (hN.pos t) hht).1
  have g := gibbs_velocity hμ (on t1) (on t2) (on t3) hD
  rw [g.2]
  exact (orbitOf_spec hμ (hN.pos t2) hh).2

end Demos.Orbit
