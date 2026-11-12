import Demos.Conjunction.Adaptive
import Demos.Conjunction.AccuracySoundness

/-!
Soundness of the adaptive panels.  `pcAdaptive_enclosure` states that an accepted result of
`pcAdaptive` contains the probability of the disk `Model.pc` for the real values of the inputs,
and `circularErrorAdaptive_sound` states for `circularErrorAdaptive` the conclusions of
`circularError_sound`.  One invariant carries a march, `Covers`: the covered part `[-r, t]` lies
in `[-r, r]`, a finished march has covered `[-r, r]`, and an accepted sum encloses the integral of
`Model.core` over the covered part.  It holds for every tolerance, length, and number of steps,
so the tolerances and the lengths that the program computes do not enter the proof.  The radius
follows from the search over any enclosure of `AccuracySoundness.lean`.
-/

namespace Demos.Conjunction.Adaptive

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open Demos.Conjunction Demos.Conjunction.Accuracy
open CodeLib.IEEE64 (value Finite)

/-! ### Marches -/

/-- The invariant of a march over `[-r, r]` for the core of the real mean and covariance. -/
def Covers (r : Float) (m1 m2 c11 c12 c22 : ℝ) (m : March) : Prop :=
  Finite m.t.toBits ∧ -value r.toBits ≤ value m.t.toBits ∧ value m.t.toBits ≤ value r.toBits ∧
    (m.state = 1 → m.t = r ∧ (m.sum.status = 0 → 0 < Model.condVar c11 c12 c22)) ∧
    (m.sum.status = 0 → Contains m.sum (∫ x in (-value r.toBits)..(value m.t.toBits),
      Model.core m1 m2 c11 c12 c22 (value r.toBits) x))

theorem panelEnd_spec {r : Float} (t h : Float) (fr : Finite r.toBits) :
    Finite (panelEnd r t h).toBits ∧ value (panelEnd r t h).toBits ≤ value r.toBits ∧
      (¬ panelEnd r t h < r → panelEnd r t h = r) := by
  unfold panelEnd
  by_cases g : (finite (t + h) && t + h < r) = true
  · rw [ite_eq_left g]
    obtain ⟨g1, g2⟩ := Bool.and_eq_true_iff.mp g
    have fs := (finite_iff _).mp g1
    have hs := of_decide_eq_true g2
    exact ⟨fs, ((lt_iff_value fs fr).mp hs).le, fun h => absurd hs h⟩
  · rw [ite_eq_right g]
    exact ⟨fr, le_rfl, fun _ => rfl⟩

section March

variable {st : Setup} {r : Float} {m1 m2 c11 c12 c22 : ℝ}

/-- Accepting the panel from `m.t` to `b` keeps the invariant. -/
theorem accept_covers (S : SetupSound st r m1 m2 c11 c12 c22) (hc : 0 < c11) {b h : Float}
    {m : March} (hm : Covers r m1 m2 c11 c12 c22 m) (fb : Finite b.toBits)
    (htb : value m.t.toBits ≤ value b.toBits) (hbr : value b.toBits ≤ value r.toBits)
    (hlast : ¬ b < r → b = r) :
    Covers r m1 m2 c11 c12 c22 (accept r b h m (panel Exp.expTable st m.t b)) := by
  obtain ⟨-, hlo, -, -, hsum⟩ := hm
  have hab : Finite r.toBits → -value r.toBits ≤ value m.t.toBits ∧ value b.toBits ≤ value r.toBits :=
    fun _ => ⟨hlo, hbr⟩
  unfold accept
  refine ⟨fb, hlo.trans htb, hbr, fun h1 => ?_, fun hs => ?_⟩
  · have h1' : (if b < r then (0 : UInt64) else 1) = 1 := h1
    by_cases g : b < r
    · rw [ite_eq_left g] at h1'
      exact absurd h1' (by decide)
    · refine ⟨hlast g, fun hs => ?_⟩
      have hs' : (add m.sum (panel Exp.expTable st m.t b)).status = 0 := hs
      obtain ⟨-, s2, -⟩ := add_sound hs'
      exact (panel_sound S hc hab s2).2.1
  · have hs' : (add m.sum (panel Exp.expTable st m.t b)).status = 0 := hs
    obtain ⟨s1, s2, ha⟩ := add_sound hs'
    obtain ⟨-, -, c2⟩ := panel_sound S hc hab s2
    have c := ha _ _ (hsum s1) c2
    rw [intervalIntegral.integral_add_adjacent_intervals
      ((Model.continuous_core _ _ _ _ _ _).intervalIntegrable _ _)
      ((Model.continuous_core _ _ _ _ _ _).intervalIntegrable _ _)] at c
    exact c

/-- A step that stops at a panel or shortens the next one keeps the invariant. -/
theorem keep_covers {m : March} (hm : Covers r m1 m2 c11 c12 c22 m) (s u : UInt64)
    (q h : Float) (hs : s ≠ 1) :
    Covers r m1 m2 c11 c12 c22 ⟨s, u, q, m.t, h, m.sum⟩ :=
  ⟨hm.1, hm.2.1, hm.2.2.1, fun h1 => absurd h1 hs, hm.2.2.2.2⟩

theorem marchStep_covers (S : SetupSound st r m1 m2 c11 c12 c22) (hc : 0 < c11)
    (fr : Finite r.toBits) {tau hmin : Float} {fuel : UInt64} {m : March}
    (hm : Covers r m1 m2 c11 c12 c22 m) :
    Covers r m1 m2 c11 c12 c22 (marchStep Exp.expTable st r tau hmin fuel m) := by
  unfold marchStep
  by_cases g0 : m.used + 1 < fuel
  · rw [ite_eq_left g0]
    dsimp only
    obtain ⟨fb, hbr, hlast⟩ := panelEnd_spec m.t m.h fr
    by_cases g1 : ((panel Exp.expTable st m.t (panelEnd r m.t m.h)).status == 0 &&
        decide (m.t ≤ panelEnd r m.t m.h)) = true
    · rw [ite_eq_left g1]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at g1
      have htb := (le_iff_value hm.1 fb).mp g1.2
      by_cases g2 : (panel Exp.expTable st m.t (panelEnd r m.t m.h)).hi -
          (panel Exp.expTable st m.t (panelEnd r m.t m.h)).lo ≤ tau
      · rw [ite_eq_left g2]
        exact accept_covers S hc hm fb htb hbr hlast
      · rw [ite_eq_right g2]
        by_cases g3 : panelEnd r m.t m.h - m.t ≤ hmin
        · rw [ite_eq_left g3]
          exact accept_covers S hc hm fb htb hbr hlast
        · rw [ite_eq_right g3]
          exact keep_covers hm _ _ _ _ (by decide)
    · rw [ite_eq_right g1]
      exact keep_covers hm _ _ _ _ (by decide)
  · rw [ite_eq_right g0]
    exact accept_covers S hc hm fr hm.2.2.1 le_rfl (fun _ => rfl)

theorem march_covers (S : SetupSound st r m1 m2 c11 c12 c22) (hc : 0 < c11)
    (fr : Finite r.toBits) (hr : 0 ≤ value r.toBits) (tau : Float) (fuel : UInt64) :
    Covers r m1 m2 c11 c12 c22 (march Exp.expTable st r tau fuel) := by
  unfold march
  refine loop_inv (Covers r m1 m2 c11 c12 c22) ?_ ?_
  · obtain ⟨fn, vn⟩ := neg_value fr
    refine ⟨fn, ?_, ?_, fun h1 => ?_, fun hs => ?_⟩
    · show -value r.toBits ≤ value (-r).toBits
      rw [vn]
    · show value (-r).toBits ≤ value r.toBits
      rw [vn]
      linarith
    · have h0 : (0 : UInt64) = 1 := h1
      exact absurd h0 (by decide)
    · show Contains (point 0.0) (∫ x in (-value r.toBits)..(value (-r).toBits), _)
      rw [vn, intervalIntegral.integral_same]
      exact point_lit lit_zero hs
  · intro _ m hm
    by_cases g : (m.state == 0) = true
    · rw [ite_eq_left g]
      exact marchStep_covers S hc fr hm
    · rw [ite_eq_right g]
      exact hm

/-- The sum of a finished march, when accepted, encloses the integral of `Model.core` over
`[-r, r]`, and the conditional variance is positive. -/
theorem finished_sound (S : SetupSound st r m1 m2 c11 c12 c22) (hc : 0 < c11)
    (fr : Finite r.toBits) (hr : 0 ≤ value r.toBits) (tau : Float) (fuel : UInt64)
    (h : (if (march Exp.expTable st r tau fuel).state == 1 then (march Exp.expTable st r tau fuel).sum
      else rejected).status = 0) :
    0 < Model.condVar c11 c12 c22 ∧
      Contains (if (march Exp.expTable st r tau fuel).state == 1 then
          (march Exp.expTable st r tau fuel).sum else rejected)
        (∫ x in (-value r.toBits)..(value r.toBits), Model.core m1 m2 c11 c12 c22 (value r.toBits) x) := by
  by_cases g : ((march Exp.expTable st r tau fuel).state == 1) = true
  · rw [ite_eq_left g] at h ⊢
    obtain ⟨-, -, -, hst, hsum⟩ := march_covers S hc fr hr tau fuel
    obtain ⟨ht, hv⟩ := hst (beq_iff_eq.mp g)
    have c := hsum h
    rw [ht] at c
    exact ⟨hv h, c⟩
  · rw [ite_eq_right g] at h
    exact absurd h (by decide)

end March

/-- The part common to two intervals that each contain `x`, when accepted, contains `x`. -/
theorem meet_sound {P : Prop} {a b : Interval} {x : ℝ} (ha : a.status = 0 → P ∧ Contains a x)
    (hb : b.status = 0 → P ∧ Contains b x) (h : (meet a b).status = 0) :
    P ∧ Contains (meet a b) x := by
  unfold meet at h ⊢
  by_cases g1 : (a.status == 0) = true
  · rw [ite_eq_left g1] at h ⊢
    obtain ⟨hP, ca⟩ := ha (beq_iff_eq.mp g1)
    by_cases g2 : (b.status == 0) = true
    · rw [ite_eq_left g2] at h ⊢
      obtain ⟨-, cb⟩ := hb (beq_iff_eq.mp g2)
      obtain ⟨-, fal, fah, hal, hah⟩ := ca
      obtain ⟨-, fbl, fbh, hbl, hbh⟩ := cb
      obtain ⟨-, -, -, hmk⟩ := make_sound h
      refine ⟨hP, hmk x ?_ ?_⟩
      · rw [(fmax_value fal fbl).2]
        exact max_le hal hbl
      · rw [(fmin_value fah fbh).2]
        exact le_min hah hbh
    · rw [ite_eq_right g2] at h ⊢
      exact ⟨hP, ca⟩
  · rw [ite_eq_right g1] at h ⊢
    exact hb h

/-- The constant factor of the probability times a sum that encloses the integral of
`Model.core` over `[-R, R]`, clamped below at 0, contains `Model.pc`. -/
theorem scaled_sound {c11 : Float} {s : Interval} {m1 m2 c12 c22 R : ℝ}
    (hc : 0 < value c11.toBits) (hv : 0 < Model.condVar (value c11.toBits) c12 c22) (hR : 0 ≤ R)
    (cs : Contains s (∫ x in (-R)..R, Model.core m1 m2 (value c11.toBits) c12 c22 R x))
    (h : (clamp (mul (div (point 1.0) (mul (point 2.0) (sqrt (mul twoPi (point c11))))) s) 0.0
      (mul (div (point 1.0) (mul (point 2.0) (sqrt (mul twoPi (point c11))))) s).hi).status = 0) :
    0 < Model.det (value c11.toBits) c12 c22 ∧
      Contains (clamp (mul (div (point 1.0) (mul (point 2.0) (sqrt (mul twoPi (point c11))))) s)
          0.0 (mul (div (point 1.0) (mul (point 2.0) (sqrt (mul twoPi (point c11))))) s).hi)
        (Model.pc m1 m2 (value c11.toBits) c12 c22 R) := by
  obtain ⟨s0, hcl⟩ := clamp_sound h
  obtain ⟨s1, -, hm⟩ := mul_sound s0
  obtain ⟨s3, s4, hd⟩ := div_sound s1
  obtain ⟨s5, s6, hm2⟩ := mul_sound s4
  obtain ⟨s7, hq⟩ := sqrt_sound s6
  obtain ⟨-, s8, hm3⟩ := mul_sound s7
  have cc := (point_sound s8).2
  have hdet : 0 < Model.det (value c11.toBits) c12 c22 := by
    have e : Model.det (value c11.toBits) c12 c22 =
        value c11.toBits * Model.condVar (value c11.toBits) c12 c22 := by
      unfold Model.det Model.condVar
      field_simp
    rw [e]
    exact mul_pos hc hv
  have c1 := (hq _ (hm3 _ _ twoPi_sound cc)).2
  have c2 := (hd _ _ (point_lit lit_one s3) (hm2 _ _ (point_lit lit_two s5) c1)).2
  have c3 := hm _ _ c2 cs
  rw [one_div, ← Model.pc_eq _ _ _ _ _ _ hc hdet hR] at c3
  exact ⟨hdet, hcl _ c3 (by rw [lit_zero.2]; exact Model.pc_nonneg _ _ _ _ _ _) c3.2.2.2.2⟩

/-! ### The probability -/

/-- An accepted result of `pcAdaptive` contains the probability of the disk of the real values of
the inputs, whose covariance is positive definite and whose radius is finite and positive. -/
theorem pcAdaptive_enclosure {m1 m2 c11 c12 c22 r : Float} {n : UInt64}
    (h : (pcAdaptive m1 m2 c11 c12 c22 r n).status = 0) :
    0 < value c11.toBits ∧
      0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
      0 < value r.toBits ∧ Finite r.toBits ∧
      Contains (pcAdaptive m1 m2 c11 c12 c22 r n)
        (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits) (value c12.toBits)
          (value c22.toBits) (value r.toBits)) := by
  unfold pcAdaptive pcAdaptWith at h ⊢
  by_cases g1 : (0.0 : Float) < c11
  · by_cases g2 : (0.0 : Float) < r
    · by_cases g3 : finite r = true
      · by_cases g4 : 16 ≤ n
        · by_cases g5 : n ≤ 1048576
          · simp only [g1, g2, g3, g4, g5, ite_true] at h ⊢
            have fr := (finite_iff r).mp g3
            have fc := (clamp_sound h).1
            obtain ⟨-, -, hm⟩ := mul_sound fc
            have fc11 : Finite c11.toBits := by
              obtain ⟨s1, -, -⟩ := mul_sound fc
              obtain ⟨-, s4, -⟩ := div_sound s1
              obtain ⟨-, s6, -⟩ := mul_sound s4
              obtain ⟨s7, -⟩ := sqrt_sound s6
              obtain ⟨-, s8, -⟩ := mul_sound s7
              exact (point_sound s8).1
            have hc : 0 < value c11.toBits := by
              have := (lt_iff_value lit_zero.1 fc11).mp g1
              rwa [lit_zero.2] at this
            have hr : 0 < value r.toBits := by
              have := (lt_iff_value lit_zero.1 fr).mp g2
              rwa [lit_zero.2] at this
            have S := setup_sound m1 m2 c11 c12 c22 r
            obtain ⟨hv, cs⟩ := meet_sound
              (finished_sound S hc fr hr.le _ _) (finished_sound S hc fr hr.le _ _)
              (mul_sound fc).2.1
            obtain ⟨hdet, cp⟩ := scaled_sound hc hv hr.le cs h
            exact ⟨hc, hdet, hr, fr, cp⟩
          · simp only [g1, g2, g3, g4, g5, ite_true, ite_false] at h
            exact absurd h (by decide)
        · simp only [g1, g2, g3, g4, ite_true, ite_false] at h
          exact absurd h (by decide)
      · simp only [g1, g2, g3, ite_true, ite_false, Bool.false_eq_true] at h
        exact absurd h (by decide)
    · simp only [g1, g2, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [g1, ite_false] at h
    exact absurd h (by decide)

/-! ### The circular error -/

/-- `pcAdaptWith` with the table of `exp` encloses the probability of the disk. -/
theorem adapt_encl (m1 m2 c11 c12 c22 : Float) (n : UInt64) :
    Encl (0 < value c11.toBits ∧
        0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits))
      (fun r => pcAdaptWith Exp.expTable m1 m2 c11 c12 c22 r n)
      (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits) (value c12.toBits)
        (value c22.toBits)) := by
  intro r h
  have h' : (pcAdaptive m1 m2 c11 c12 c22 r n).status = 0 := h
  obtain ⟨hc, hd, hr, fr, hcont⟩ := pcAdaptive_enclosure h'
  exact ⟨⟨hc, hd⟩, fr, hr.le, hcont⟩

theorem adaptSearch_eq (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) :
    adaptSearch tab m1 m2 c11 c12 c22 p n k =
      result (fun r => pcAdaptWith tab m1 m2 c11 c12 c22 r n) p
        (Float.sqrt (c11 + c22) + Float.sqrt (m1 * m1 + m2 * m2)) k := rfl

theorem adaptSearch_sound {m1 m2 c11 c12 c22 p : Float} {n k : UInt64} (hp : Finite p.toBits)
    (hq : 0 < value p.toBits) (h : (adaptSearch Exp.expTable m1 m2 c11 c12 c22 p n k).status = 0) :
    (0 < value c11.toBits ∧
        0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits)) ∧
      Finite (adaptSearch Exp.expTable m1 m2 c11 c12 c22 p n k).lo.toBits ∧
      Finite (adaptSearch Exp.expTable m1 m2 c11 c12 c22 p n k).hi.toBits ∧
      Model.RadiusIn (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits)
          (value c12.toBits) (value c22.toBits)) (value p.toBits)
        (value (adaptSearch Exp.expTable m1 m2 c11 c12 c22 p n k).lo.toBits)
        (value (adaptSearch Exp.expTable m1 m2 c11 c12 c22 p n k).hi.toBits) := by
  rw [adaptSearch_eq] at h ⊢
  obtain ⟨hf, hlo, hhi⟩ := result_parts h
  rw [hlo, hhi]
  exact search_sound (adapt_encl m1 m2 c11 c12 c22 n) hp hq (Model.pc_zero _ _ _ _ _)
    (fun hH => Model.pc_strictMonoOn _ _ _ _ _ hH.2)
    (fun hH => Model.pc_continuousOn _ _ _ _ _ hH.1 hH.2) k hf

theorem circularErrorAdaptWith_eq (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float)
    (n k : UInt64) :
    circularErrorAdaptWith tab m1 m2 c11 c12 c22 p n k =
      guarded 16 (fun a b c d e q => adaptSearch tab a b c d e q n k) m1 m2 c11 c12 c22 p n k :=
  rfl

/-- An accepted result of `circularErrorAdaptive` holds the radius of the disk about the origin
whose probability is `p`, for the real values of the inputs, whose covariance is positive
definite. -/
theorem circularErrorAdaptive_sound {m1 m2 c11 c12 c22 p : Float} {n k : UInt64}
    (h : (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).status = 0) :
    0 < value p.toBits ∧ value p.toBits < 1 ∧ 0 < value c11.toBits ∧
      0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
      Finite (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).lo.toBits ∧
      Finite (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).hi.toBits ∧
      Model.RadiusIn (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits)
          (value c12.toBits) (value c22.toBits)) (value p.toBits)
        (value (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).lo.toBits)
        (value (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).hi.toBits) := by
  rw [circularErrorAdaptive, circularErrorAdaptWith_eq] at h ⊢
  exact guarded_sound (fun _ _ _ _ _ _ hp hq hs => adaptSearch_sound hp hq hs) h

#print axioms pcAdaptive_enclosure
#print axioms circularErrorAdaptive_sound

end Demos.Conjunction.Adaptive
