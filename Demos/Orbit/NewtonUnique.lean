import Demos.Orbit.Newton
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
A solution of Newton's equation on an open interval of times is determined by its state at one
time of the interval (`newton_unique`).  The proof writes a solution as a curve in `E × E`, with
`E` the Euclidean space of three coordinates.  Newton's field `(r, v) ↦ (v, -μ r/|r|³)` is
continuously differentiable where `r ≠ 0`, so it is Lipschitz near each state of a solution, and
Mathlib's local uniqueness theorem for such fields, `ODE_solution_unique_of_eventually`, makes the
set of times at which two solutions agree open in the interval.  Continuity makes the set closed
in the interval, and the interval is connected.
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

/-- A solution of Newton's equation on `I` is a solution of `newtonField` in `E × E` at the times
of `I`. -/
theorem NewtonOn.hasDerivAt_curve {μ : ℝ} {I : Set ℝ} {r v : ℝ → V3} (hN : NewtonOn μ I r v)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s => (toE (r s), toE (v s))) (newtonField μ (toE (r t), toE (v t))) t := by
  have ha : HasDerivAt (fun s => toE (v s)) (toE ((-μ / V3.norm (r t) ^ 3) • r t)) t := by
    refine hasDerivAt_toE (v := fun _ => (-μ / V3.norm (r t) ^ 3) • r t) ?_ ?_ ?_
    · exact (hN.ax t ht).congr_deriv (by simp only [smul_x]; ring)
    · exact (hN.ay t ht).congr_deriv (by simp only [smul_y]; ring)
    · exact (hN.az t ht).congr_deriv (by simp only [smul_z]; ring)
  refine ((hasDerivAt_toE (hN.dx t ht) (hN.dy t ht) (hN.dz t ht)).prodMk ha).congr_deriv ?_
  simp only [newtonField, norm_toE]
  congr 1
  simp only [toE, smul_x, smul_y, smul_z]
  ext i
  fin_cases i <;> simp <;> ring

/-- **Uniqueness for Newton's equation.**  On an open interval, or any open preconnected set of
times, two solutions with the same position and velocity at one of its times are equal at every
time of it. -/
theorem newton_unique {μ : ℝ} {I : Set ℝ} (hIo : IsOpen I) (hIc : IsPreconnected I)
    {r1 v1 r2 v2 : ℝ → V3} (h1 : NewtonOn μ I r1 v1) (h2 : NewtonOn μ I r2 v2) {t0 : ℝ}
    (ht0 : t0 ∈ I) (hr : r1 t0 = r2 t0) (hv : v1 t0 = v2 t0) :
    ∀ t ∈ I, r1 t = r2 t ∧ v1 t = v2 t := by
  set f := fun s => (toE (r1 s), toE (v1 s)) with hf
  set g := fun s => (toE (r2 s), toE (v2 s)) with hg
  have df : ∀ t ∈ I, HasDerivAt f (newtonField μ (f t)) t := fun t ht => h1.hasDerivAt_curve ht
  have dg : ∀ t ∈ I, HasDerivAt g (newtonField μ (g t)) t := fun t ht => h2.hasDerivAt_curve ht
  have : PreconnectedSpace I := Subtype.preconnectedSpace hIc
  have cf : Continuous fun s : I => f s := continuous_iff_continuousAt.mpr fun s =>
    (df s s.2).continuousAt.comp continuous_subtype_val.continuousAt
  have cg : Continuous fun s : I => g s := continuous_iff_continuousAt.mpr fun s =>
    (dg s s.2).continuousAt.comp continuous_subtype_val.continuousAt
  have hS : IsClopen {s : I | f s = g s} := by
    refine ⟨isClosed_eq cf cg, isOpen_iff_mem_nhds.mpr fun s hs => ?_⟩
    have hne : (f s).1 ≠ 0 := by
      intro h0
      have := norm_toE (r1 s)
      rw [show toE (r1 s) = (f s).1 from rfl, h0, norm_zero] at this
      linarith [h1.pos s s.2]
    obtain ⟨K, U, hU, hK⟩ := (newtonField_contDiffAt μ hne).exists_lipschitzOnWith
    have hgU : U ∈ nhds (g s) := (show f s = g s from hs) ▸ hU
    have hI : ∀ᶠ τ in nhds (s : ℝ), τ ∈ I := hIo.mem_nhds s.2
    have heq : f =ᶠ[nhds (s : ℝ)] g :=
      ODE_solution_unique_of_eventually (v := fun _ => newtonField μ) (s := fun _ => U) (K := K)
        (Filter.Eventually.of_forall fun _ => hK)
        ((hI.and ((df s s.2).continuousAt.eventually_mem hU)).mono fun τ h => ⟨df τ h.1, h.2⟩)
        ((hI.and ((dg s s.2).continuousAt.eventually_mem hgU)).mono fun τ h => ⟨dg τ h.1, h.2⟩)
        hs
    exact continuous_subtype_val.continuousAt.preimage_mem_nhds heq
  have huniv := hS.eq_univ ⟨⟨t0, ht0⟩, show f t0 = g t0 by simp only [hf, hg, hr, hv]⟩
  intro t ht
  have h := Set.eq_univ_iff_forall.mp huniv ⟨t, ht⟩
  exact ⟨toE_injective (congrArg Prod.fst h), toE_injective (congrArg Prod.snd h)⟩

end Demos.Orbit
