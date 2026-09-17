import Project.TinyGpt2.Score
import Project.Affine.BalancedBounds

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem attentionScore_error_wide (q0 q1 k0 k1 : UInt64) (bound : ℝ)
    (hb1 : 1 ≤ bound) (hbMax : bound ≤ 2^40)
    (hq0 : Finite q0) (hq1 : Finite q1) (hk0 : Finite k0) (hk1 : Finite k1)
    (hp0 : |value q0*value k0| ≤ bound) (hp1 : |value q1*value k1| ≤ bound) :
    Approximation (attentionScore q0 q1 k0 k1)
      ((value q0*value k0+value q1*value k1)/Real.sqrt 2)
      (2*bound+3) ((16*bound+3)*arithmeticEpsilon) := by
  have hd := Affine.dot2_error_bounded q0 q1 k0 k1 bound hb1 hbMax hq0 hq1 hk0 hk1 hp0 hp1
  have hs := sqrtTwo_bounds.2.weaken (le_refl (2:ℝ))
    (by norm_num [arithmeticEpsilon] : (1:ℝ)/1000000000000000 ≤ 5*arithmeticEpsilon)
  have hp : |value q0*value k0+value q1*value k1| ≤ 2*bound :=
    (abs_add_le _ _).trans ((add_le_add hp0 hp1).trans_eq (by ring))
  have he := hd.div_ge_one hs sqrtTwo_bounds.1
    ((Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)) hp
    (bound := 2*bound+2) (by linarith) (by norm_num at hbMax ⊢; linarith) (le_refl _)
  exact he.weaken (by norm_num [arithmeticEpsilon] at hbMax ⊢; linarith) (by ring_nf; rfl)

theorem attentionScore_bounded (q0 q1 k0 k1 : UInt64)
    (hq0 : Affine.Bounded q0 1249) (hq1 : Affine.Bounded q1 1249)
    (hk0 : Affine.Bounded k0 1249) (hk1 : Affine.Bounded k1 1249) :
    Affine.Bounded (attentionScore q0 q1 k0 k1) 4000000 := by
  have hp (q k : UInt64) (hq : Affine.Bounded q 1249) (hk : Affine.Bounded k 1249) :
      |value q*value k| ≤ (1249:ℝ)^2 := by
    rw [abs_mul]
    exact (mul_le_mul hq.2 hk.2 (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have h := attentionScore_error_wide q0 q1 k0 k1 (1249^2) (by norm_num) (by norm_num)
    hq0.1 hq1.1 hk0.1 hk1.1 (hp q0 k0 hq0 hk0) (hp q1 k1 hq1 hk1)
  exact ⟨h.finite, h.magnitude.trans (by norm_num)⟩

#print axioms attentionScore_error_wide
#print axioms attentionScore_bounded
end Project.TinyGpt2
