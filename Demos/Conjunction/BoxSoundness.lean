import Demos.Conjunction.Box
import Demos.Conjunction.Soundness
import Library.Numerics.Interval.FunctionsProof

/-!
Soundness of the probability enclosure for interval inputs.  `pcBoxWith_enclosure` states that an
accepted result of `pcBoxWith` contains the probability of collision `Model.pc` for every real
mean and covariance that its interval arguments enclose, and that each such covariance is positive
definite.  The proof is that of `pc_enclosure`: `setupBox_sound` gives the setup's inclusions for
every point of the intervals, and `panels_sound_of` the inclusion of the integral.
-/

namespace Demos.Conjunction

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

/-- Each accepted field of the setup from intervals contains its real quantity for every point
of the intervals. -/
theorem setupBox_sound {M1 M2 C11 C12 C22 : Interval} {r : Float} {m1 m2 c11 c12 c22 : ℝ}
    (h1 : Encloses M1 m1) (h2 : Encloses M2 m2) (h11 : Encloses C11 c11)
    (h12 : Encloses C12 c12) (h22 : Encloses C22 c22) :
    SetupSound (setupBox M1 M2 C11 C12 C22 r) r m1 m2 c11 c12 c22 := by
  refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
  · exact encloses_mul (fun s => point_lit lit_two s) h11
  · exact encloses_div h12 h11
  · intro h
    have h' : (mul (sqrt (sub C22 (div (sq C12) C11))) (sqrt (point 2.0))).status = 0 := h
    obtain ⟨s1, s2, hm⟩ := mul_sound h'
    obtain ⟨s3, hq⟩ := sqrt_sound s1
    obtain ⟨s4, hq2⟩ := sqrt_sound s2
    obtain ⟨s5, s6, hs⟩ := sub_sound s3
    obtain ⟨s7, s8, hd⟩ := div_sound s6
    obtain ⟨s9, hsq⟩ := sq_sound s7
    have c1 := hs _ _ (h22 s5) (hd _ _ (hsq _ (h12 s9)) (h11 s8)).2
    obtain ⟨n1, c2⟩ := hq _ c1
    obtain ⟨-, c3⟩ := hq2 _ (point_lit lit_two s4)
    exact ⟨n1, hm _ _ c2 c3⟩
  · intro h
    have h' : (sq (point r)).status = 0 := h
    obtain ⟨s1, hsq⟩ := sq_sound h'
    obtain ⟨f1, c1⟩ := point_sound s1
    exact ⟨f1, hsq _ c1⟩

/-- **P1.**  An accepted result of `pcBoxWith` contains the probability of collision for every
real mean and covariance that its interval arguments enclose, and each such covariance is
positive definite. -/
theorem pcBoxWith_enclosure {M1 M2 C11 C12 C22 : Interval} {r : Float} {n : UInt64}
    (h : (pcBoxWith Exp.expTable M1 M2 C11 C12 C22 r n).status = 0)
    {m1 m2 c11 c12 c22 : ℝ} (h1 : Encloses M1 m1) (h2 : Encloses M2 m2)
    (h11 : Encloses C11 c11) (h12 : Encloses C12 c12) (h22 : Encloses C22 c22) :
    0 < c11 ∧ 0 < Model.det c11 c12 c22 ∧ 0 < value r.toBits ∧
      Contains (pcBoxWith Exp.expTable M1 M2 C11 C12 C22 r n)
        (Model.pc m1 m2 c11 c12 c22 (value r.toBits)) := by
  unfold pcBoxWith at h ⊢
  by_cases g1 : (C11.status == 0 && 0 < C11.lo) = true
  · by_cases g2 : (0.0 : Float) < r
    · by_cases g3 : 1 ≤ n
      · by_cases g4 : n ≤ 1048576
        · simp only [g1, g2, g3, g4, ite_true] at h ⊢
          obtain ⟨s0, hcl⟩ := clamp_sound h
          obtain ⟨s1, s2, hm⟩ := mul_sound s0
          obtain ⟨s3, s4, hd⟩ := div_sound s1
          obtain ⟨s5, s6, hm2⟩ := mul_sound s4
          obtain ⟨s7, hq⟩ := sqrt_sound s6
          obtain ⟨-, -, hm3⟩ := mul_sound s7
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g1
          have cc := h11 g1.1
          have hc : 0 < c11 := cc.pos_of_lo g1.2
          have hr : Finite r.toBits → 0 < value r.toBits := fun fr => by
            have := (lt_iff_value lit_zero.1 fr).mp g2
            rwa [lit_zero.2] at this
          obtain ⟨fr, hv, cp⟩ :=
            panels_sound_of (setupBox_sound h1 h2 h11 h12 h22) hc hr g3 s2
          have hdet : 0 < Model.det c11 c12 c22 := by
            have e : Model.det c11 c12 c22 = c11 * Model.condVar c11 c12 c22 := by
              unfold Model.det Model.condVar
              field_simp
            rw [e]
            exact mul_pos hc hv
          have c1 := (hq _ (hm3 _ _ twoPi_sound cc)).2
          have c2 := (hd _ _ (point_lit lit_one s3) (hm2 _ _ (point_lit lit_two s5) c1)).2
          have c3 := hm _ _ c2 cp
          rw [one_div, ← Model.pc_eq _ _ _ _ _ _ hc hdet (hr fr).le] at c3
          exact ⟨hc, hdet, hr fr,
            hcl _ c3 (by rw [lit_zero.2]; exact Model.pc_nonneg _ _ _ _ _ _) c3.2.2.2.2⟩
        · simp only [g1, g2, g3, g4, ite_true, ite_false] at h
          exact absurd h (by decide)
      · simp only [g1, g2, g3, ite_true, ite_false] at h
        exact absurd h (by decide)
    · simp only [g1, g2, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [g1, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- An interval `make lo hi` encloses every real between the values of its ends. -/
theorem encloses_make {lo hi : Float} {x : ℝ} (h1 : value lo.toBits ≤ x)
    (h2 : x ≤ value hi.toBits) : Encloses (make lo hi) x :=
  fun s => (make_sound s).2.2.2 x h1 h2

/-- **P1** for the export `pcBox`: an accepted result contains the probability of collision for
every real mean and covariance between the values of the given ends. -/
theorem pcBox_enclosure {m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi r : Float}
    {n : UInt64}
    (h : (pcBox m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi r n).status = 0)
    {m1 m2 c11 c12 c22 : ℝ}
    (h1 : value m1lo.toBits ≤ m1 ∧ m1 ≤ value m1hi.toBits)
    (h2 : value m2lo.toBits ≤ m2 ∧ m2 ≤ value m2hi.toBits)
    (h11 : value c11lo.toBits ≤ c11 ∧ c11 ≤ value c11hi.toBits)
    (h12 : value c12lo.toBits ≤ c12 ∧ c12 ≤ value c12hi.toBits)
    (h22 : value c22lo.toBits ≤ c22 ∧ c22 ≤ value c22hi.toBits) :
    0 < c11 ∧ 0 < Model.det c11 c12 c22 ∧ 0 < value r.toBits ∧
      Contains (pcBox m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi r n)
        (Model.pc m1 m2 c11 c12 c22 (value r.toBits)) :=
  pcBoxWith_enclosure h (encloses_make h1.1 h1.2) (encloses_make h2.1 h2.2)
    (encloses_make h11.1 h11.2) (encloses_make h12.1 h12.2) (encloses_make h22.1 h22.2)

#print axioms pcBoxWith_enclosure
#print axioms pcBox_enclosure

end Demos.Conjunction
