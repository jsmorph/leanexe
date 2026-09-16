import Project.TinyGpt2.Score
import Project.Affine.Real

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

theorem attentionScore_perturbed (q0 q1 k0 k1 : UInt64) (p0 p1 r0 r1 : ℝ)
    (hq0 : Approximation q0 p0 15 (1/200000))
    (hq1 : Approximation q1 p1 15 (1/200000))
    (hk0 : Approximation k0 r0 15 (1/200000))
    (hk1 : Approximation k1 r1 15 (1/200000)) :
    Approximation (attentionScore q0 q1 k0 k1)
      ((p0*r0+p1*r1)/Real.sqrt 2) 2051 (1/3000) := by
  have hprod (q k : UInt64) (p r : ℝ)
      (hq : Approximation q p 15 (1/200000))
      (hk : Approximation k r 15 (1/200000)) :
      |value q*value k-p*r| ≤ 31/200000 := by
    have ht := F64ArithmeticBounds.magnitude_of_error p (value q) (1/200000) 15
      (by simpa only [abs_sub_comm] using hq.accuracy) hq.magnitude
    have hp := Affine.Real.product_perturbation (value q) p (value k) r
      (1/200000) (1/200000) hq.accuracy hk.accuracy
    linarith [hk.magnitude]
  have hsum : |(value q0*value k0+value q1*value k1)-(p0*r0+p1*r1)| ≤ 62/200000 := by
    rw [show (value q0*value k0+value q1*value k1)-(p0*r0+p1*r1) =
      (value q0*value k0-p0*r0)+(value q1*value k1-p1*r1) by ring]
    exact (abs_add_le _ _).trans ((add_le_add (hprod _ _ _ _ hq0 hk0)
      (hprod _ _ _ _ hq1 hk1)).trans_eq (by norm_num))
  have hs : (1:ℝ) ≤ Real.sqrt 2 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hp : (0:ℝ) < Real.sqrt 2 := by positivity
  have hd : |(value q0*value k0+value q1*value k1)/Real.sqrt 2-
      (p0*r0+p1*r1)/Real.sqrt 2| ≤ 62/200000 := by
    rw [← sub_div, abs_div, abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    exact hsum.trans (by nlinarith)
  have hc := attentionScore_error q0 q1 k0 k1
    ⟨hq0.finite, hq0.magnitude.trans (by norm_num)⟩
    ⟨hq1.finite, hq1.magnitude.trans (by norm_num)⟩
    ⟨hk0.finite, hk0.magnitude.trans (by norm_num)⟩
    ⟨hk1.finite, hk1.magnitude.trans (by norm_num)⟩
  exact ⟨hc.finite, hc.magnitude,
    (abs_sub_le _ _ _).trans ((add_le_add hc.accuracy hd).trans (by norm_num))⟩

#print axioms attentionScore_perturbed
end Project.TinyGpt2
