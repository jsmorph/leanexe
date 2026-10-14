import Verified.Examples.ErfcTrack5
import Verified.Examples.ErfcCast

/-!
The two loops of the polynomial of `erfc_asympt_accurate`, for any number of steps.  The bounds
of the states come as a list `bs` that the kernel checks step by step against `ErfcTrack5.stepF`
and `stepFB` (`ChkA`, `ChkB`), so that no recursion recomputes them.  `loopA` follows the first
loop, with single coefficients, from a `Pr` of the top coefficient; `loopB` the second, with
double-double coefficients.  The values are Horner's sums `hornerA` and `hornerB`.
-/

namespace Verified.Examples.ErfcTaccLoop

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack5 FmaSpec PolyBound

set_option exponentiation.threshold 2200

/-- `V0 U^n + c (n-1) + ... `, Horner's rule from the top: `hornerA (j + 1) = c j + U hornerA j`. -/
noncomputable def hornerA (c : ℕ → ℝ) (U V0 : ℝ) : ℕ → ℝ
  | 0 => V0
  | j + 1 => c j + hornerA c U V0 j * U

/-- Horner's rule with double-double coefficients `c j + d j`. -/
noncomputable def hornerB (c d : ℕ → ℝ) (U V0 : ℝ) : ℕ → ℝ
  | 0 => V0
  | j + 1 => c j + d j + hornerB c d U V0 j * U

/-- The kernel's check of the bounds `bs` of the first loop for coefficient magnitudes `mc`. -/
def ChkA (bs : List (ℚ × ℚ × ℚ)) (mc : List ℚ) (MU LU : ℚ) (n : ℕ) : Prop :=
  ∀ j < n, stepOK (bs.getD j 0).1 (bs.getD j 0).2.1 (bs.getD j 0).2.2 (mc.getD j 0) 0 MU LU ∧
    (stepF (bs.getD j 0).1 (bs.getD j 0).2.1 (bs.getD j 0).2.2 (mc.getD j 0) MU LU).1 ≤
      (bs.getD (j + 1) 0).1 ∧
    (stepF (bs.getD j 0).1 (bs.getD j 0).2.1 (bs.getD j 0).2.2 (mc.getD j 0) MU LU).2.1 ≤
      (bs.getD (j + 1) 0).2.1 ∧
    (stepF (bs.getD j 0).1 (bs.getD j 0).2.1 (bs.getD j 0).2.2 (mc.getD j 0) MU LU).2.2 ≤
      (bs.getD (j + 1) 0).2.2

instance (bs : List (ℚ × ℚ × ℚ)) (mc : List ℚ) (MU LU : ℚ) (n : ℕ) :
    Decidable (ChkA bs mc MU LU n) := by
  unfold ChkA; infer_instance

/-- The kernel's check of the bounds `bs` of the second loop. -/
def ChkB (bs : List (ℚ × ℚ × ℚ)) (mc md : List ℚ) (MU LU : ℚ) (n : ℕ) : Prop :=
  ∀ j < n, stepOK (bs.getD j 0).1 (bs.getD j 0).2.1 (bs.getD j 0).2.2 (mc.getD j 0)
      (md.getD j 0) MU LU ∧
    (stepFB (bs.getD j 0).1 (bs.getD j 0).2.1 (bs.getD j 0).2.2 (mc.getD j 0) (md.getD j 0) MU
      LU).1 ≤ (bs.getD (j + 1) 0).1 ∧
    (stepFB (bs.getD j 0).1 (bs.getD j 0).2.1 (bs.getD j 0).2.2 (mc.getD j 0) (md.getD j 0) MU
      LU).2.1 ≤ (bs.getD (j + 1) 0).2.1 ∧
    (stepFB (bs.getD j 0).1 (bs.getD j 0).2.1 (bs.getD j 0).2.2 (mc.getD j 0) (md.getD j 0) MU
      LU).2.2 ≤ (bs.getD (j + 1) 0).2.2

instance (bs : List (ℚ × ℚ × ℚ)) (mc md : List ℚ) (MU LU : ℚ) (n : ℕ) :
    Decidable (ChkB bs mc md MU LU n) := by
  unfold ChkB; infer_instance

theorem okR {M L e Mc Md MU LU : ℚ} (h : stepOK M L e Mc Md MU LU) :
    (0 : ℝ) ≤ Mc ∧ (0 : ℝ) ≤ Md ∧ (M : ℝ) + e + L ≤ 2 ^ 400 ∧ (MU : ℝ) + LU ≤ 1 ∧
      (Mc : ℝ) + Md ≤ 2 ^ 400 ∧ (Mc : ℝ) ≤ 2 ^ 400 := by
  obtain ⟨-, -, -, h4, h5, -, -, h8, h9, h10⟩ := h
  have q4 : (0 : ℝ) ≤ Mc := by qc h4
  have q5 : (0 : ℝ) ≤ Md := by qc h5
  have q8 : (M : ℝ) + e + L ≤ 2 ^ 400 := by qc h8
  have q9 : (MU : ℝ) + LU ≤ 1 := by qc h9
  have q10 : (Mc : ℝ) + Md ≤ 2 ^ 400 := by qc h10
  exact ⟨q4, q5, q8, q9, q10, by linarith⟩

/-- The first loop. -/
theorem loopA (hF : FmaNearest) {uh ul : Float} {U : ℝ} {MU LU : ℚ}
    (hU : Pr uh ul U MU LU 0) (cs : ℕ → Float) (mc : List ℚ) (bs : List (ℚ × ℚ × ℚ))
    (s0 : Float × Float) (V0 : ℝ)
    (h0 : Pr s0.1 s0.2 V0 (bs.getD 0 0).1 (bs.getD 0 0).2.1 (bs.getD 0 0).2.2) :
    ∀ n : ℕ, (∀ j < n, ff (cs j) ∧ |fv (cs j)| ≤ mc.getD j 0) → ChkA bs mc MU LU n →
      Pr (Nat.fold n (fun j _ s => tStep uh ul (cs j) s) s0).1
        (Nat.fold n (fun j _ s => tStep uh ul (cs j) s) s0).2
        (hornerA (fun j => fv (cs j)) U V0 n) (bs.getD n 0).1 (bs.getD n 0).2.1
        (bs.getD n 0).2.2
  | 0, _, _ => by simpa [hornerA] using h0
  | n + 1, hcs, hchk => by
    have ih := loopA hF hU cs mc bs s0 V0 h0 n (fun j hj => hcs j (by omega))
      (fun j hj => hchk j (by omega))
    obtain ⟨cf, cm⟩ := hcs n (by omega)
    obtain ⟨ok, c1, c2, c3⟩ := hchk n (by omega)
    obtain ⟨q0, -, qM, qU, -, qc⟩ := okR ok
    have st := pr_tStep hF hU ih cf cm q0 qM qU qc
    obtain ⟨e1, e2, e3⟩ := stepF_cast (bs.getD n 0).1 (bs.getD n 0).2.1 (bs.getD n 0).2.2
      (mc.getD n 0) MU LU
    rw [← e1, ← e2, ← e3] at st
    rw [Nat.fold_succ]
    exact st.mono (by qc c1) (by qc c2) (by qc c3)

/-- The second loop. -/
theorem loopB (hF : FmaNearest) {uh ul : Float} {U : ℝ} {MU LU : ℚ}
    (hU : Pr uh ul U MU LU 0) (cs ds : ℕ → Float) (mc md : List ℚ) (bs : List (ℚ × ℚ × ℚ))
    (s0 : Float × Float) (V0 : ℝ)
    (h0 : Pr s0.1 s0.2 V0 (bs.getD 0 0).1 (bs.getD 0 0).2.1 (bs.getD 0 0).2.2) :
    ∀ n : ℕ, (∀ j < n, ff (cs j) ∧ |fv (cs j)| ≤ mc.getD j 0 ∧ ff (ds j) ∧
        |fv (ds j)| ≤ md.getD j 0) → ChkB bs mc md MU LU n →
      Pr (Nat.fold n (fun j _ s => tStepB uh ul (cs j) (ds j) s) s0).1
        (Nat.fold n (fun j _ s => tStepB uh ul (cs j) (ds j) s) s0).2
        (hornerB (fun j => fv (cs j)) (fun j => fv (ds j)) U V0 n) (bs.getD n 0).1
        (bs.getD n 0).2.1 (bs.getD n 0).2.2
  | 0, _, _ => by simpa [hornerB] using h0
  | n + 1, hcs, hchk => by
    have ih := loopB hF hU cs ds mc md bs s0 V0 h0 n (fun j hj => hcs j (by omega))
      (fun j hj => hchk j (by omega))
    obtain ⟨cf, cm, df, dm⟩ := hcs n (by omega)
    obtain ⟨ok, c1, c2, c3⟩ := hchk n (by omega)
    obtain ⟨q0, q0', qM, qU, qcd, -⟩ := okR ok
    have st := pr_tStepB hF hU ih cf cm df dm q0 q0' qM qU qcd
    obtain ⟨e1, e2, e3⟩ := stepFB_cast (bs.getD n 0).1 (bs.getD n 0).2.1 (bs.getD n 0).2.2
      (mc.getD n 0) (md.getD n 0) MU LU
    rw [← e1, ← e2, ← e3] at st
    rw [Nat.fold_succ]
    exact st.mono (by qc c1) (by qc c2) (by qc c3)

#print axioms loopA
#print axioms loopB

end Verified.Examples.ErfcTaccLoop
