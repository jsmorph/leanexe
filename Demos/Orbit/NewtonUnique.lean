import Demos.Orbit.Newton
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
A solution of Newton's equation is determined by its state at one time (`newton_unique`).  The
proof writes a solution as a curve in `E × E`, with `E` the Euclidean space of three coordinates.
Newton's field `(r, v) ↦ (v, -μ r/|r|³)` is continuously differentiable where `r ≠ 0`, so it is
Lipschitz near each state of a solution, and Mathlib's local uniqueness theorem for such fields,
`ODE_solution_unique_of_eventually`, makes the set of times at which two solutions agree open.
Continuity makes the set closed, and the real line is connected.
-/

namespace Demos.Orbit

open V3

/-- A vector as a point of the Euclidean space of three coordinates. -/
noncomputable def toE (a : V3) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![a.x, a.y, a.z]

theorem norm_toE (a : V3) : ‖toE a‖ = V3.norm a := by
  rw [EuclideanSpace.norm_eq, V3.norm, dot]
  congr 1
  simp [toE, Fin.sum_univ_three, sq_abs]
  ring

theorem toE_injective {a b : V3} (h : toE a = toE b) : a = b := by
  have h0 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) => e 0) h
  have h1 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) => e 1) h
  have h2 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) => e 2) h
  simp [toE] at h0 h1 h2
  ext <;> assumption

/-- Newton's field `(r, v) ↦ (v, -μ r/|r|³)` on positions and velocities. -/
noncomputable def newtonField (μ : ℝ) (p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) :=
  (p.2, (-μ * (‖p.1‖ ^ 3)⁻¹) • p.1)

theorem newtonField_contDiffAt (μ : ℝ) {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)}
    (hp : p.1 ≠ 0) : ContDiffAt ℝ 1 (newtonField μ) p := by
  have hn : ContDiffAt ℝ 1 (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ‖q.1‖) p :=
    (contDiffAt_norm ℝ hp).comp p contDiffAt_fst
  have hn3 : ‖p.1‖ ^ 3 ≠ 0 := pow_ne_zero 3 (norm_ne_zero_iff.mpr hp)
  exact contDiffAt_snd.prodMk ((contDiffAt_const.mul ((hn.pow 3).inv hn3)).smul contDiffAt_fst)

theorem hasDerivAt_toE {r v : ℝ → V3} {t : ℝ} (hx : HasDerivAt (fun s => (r s).x) (v t).x t)
    (hy : HasDerivAt (fun s => (r s).y) (v t).y t) (hz : HasDerivAt (fun s => (r s).z) (v t).z t) :
    HasDerivAt (fun s => toE (r s)) (toE (v t)) t := by
  have h : HasDerivAt (fun s => ![(r s).x, (r s).y, (r s).z]) ![(v t).x, (v t).y, (v t).z] t := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hx
    · exact hy
    · exact hz
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt.comp_hasDerivAt t h

/-- A solution of Newton's equation is a solution of `newtonField` in `E × E`. -/
theorem Newton.hasDerivAt_curve {μ : ℝ} {r v : ℝ → V3} (hN : Newton μ r v) (t : ℝ) :
    HasDerivAt (fun s => (toE (r s), toE (v s))) (newtonField μ (toE (r t), toE (v t))) t := by
  have ha : HasDerivAt (fun s => toE (v s)) (toE ((-μ / V3.norm (r t) ^ 3) • r t)) t := by
    refine hasDerivAt_toE (v := fun _ => (-μ / V3.norm (r t) ^ 3) • r t) ?_ ?_ ?_
    · exact (hN.ax t).congr_deriv (by simp only [smul_x]; ring)
    · exact (hN.ay t).congr_deriv (by simp only [smul_y]; ring)
    · exact (hN.az t).congr_deriv (by simp only [smul_z]; ring)
  refine ((hasDerivAt_toE (hN.dx t) (hN.dy t) (hN.dz t)).prodMk ha).congr_deriv ?_
  simp only [newtonField, norm_toE]
  congr 1
  simp only [toE, smul_x, smul_y, smul_z]
  ext i
  fin_cases i <;> simp <;> ring

/-- **Uniqueness for Newton's equation.**  Two solutions with the same position and velocity at
one time are equal. -/
theorem newton_unique {μ : ℝ} {r1 v1 r2 v2 : ℝ → V3} (h1 : Newton μ r1 v1) (h2 : Newton μ r2 v2)
    {t0 : ℝ} (hr : r1 t0 = r2 t0) (hv : v1 t0 = v2 t0) : r1 = r2 ∧ v1 = v2 := by
  set f := fun s => (toE (r1 s), toE (v1 s)) with hf
  set g := fun s => (toE (r2 s), toE (v2 s)) with hg
  have df := h1.hasDerivAt_curve
  have dg := h2.hasDerivAt_curve
  have cf : Continuous f := continuous_iff_continuousAt.mpr fun t => (df t).continuousAt
  have cg : Continuous g := continuous_iff_continuousAt.mpr fun t => (dg t).continuousAt
  have hS : IsClopen {t | f t = g t} := by
    refine ⟨isClosed_eq cf cg, isOpen_iff_mem_nhds.mpr fun t ht => ?_⟩
    have hne : (f t).1 ≠ 0 := by
      intro h0
      have := norm_toE (r1 t)
      rw [show toE (r1 t) = (f t).1 from rfl, h0, norm_zero] at this
      linarith [h1.pos t]
    obtain ⟨K, U, hU, hK⟩ := (newtonField_contDiffAt μ hne).exists_lipschitzOnWith
    have hgU : U ∈ nhds (g t) := (show f t = g t from ht) ▸ hU
    exact ODE_solution_unique_of_eventually (v := fun _ => newtonField μ) (s := fun _ => U)
      (K := K) (Filter.Eventually.of_forall fun _ => hK)
      ((cf.continuousAt.eventually_mem hU).mono fun s hs => ⟨df s, hs⟩)
      ((cg.continuousAt.eventually_mem hgU).mono fun s hs => ⟨dg s, hs⟩) ht
  have huniv := hS.eq_univ ⟨t0, show f t0 = g t0 by simp only [hf, hg, hr, hv]⟩
  have heq : ∀ t, f t = g t := fun t => (Set.eq_univ_iff_forall.mp huniv t)
  refine ⟨funext fun t => toE_injective (congrArg Prod.fst (heq t)),
    funext fun t => toE_injective (congrArg Prod.snd (heq t))⟩

end Demos.Orbit
