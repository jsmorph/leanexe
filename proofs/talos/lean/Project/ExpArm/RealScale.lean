import Project.ExpArm.CorrectionError
import Project.ExpArm.ScaledTable

namespace Project.ExpArm
open CodeLib.IEEE64

noncomputable def scaleFactor (m : Int) : ℝ := (2 : ℝ)^(1023+m).toNat / 2^1023

theorem scaleFactor_pos (m : Int) : 0 < scaleFactor m := by
  dsimp [scaleFactor]
  positivity

theorem scaleFactor_exp (m : Int) (hm : 0 ≤ 1023+m) :
    scaleFactor m = Real.exp ((m : ℝ)*Real.log 2) := by
  have hp (n : Nat) : (2 : ℝ)^n = Real.exp ((n : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [scaleFactor, hp, hp, ← Real.exp_sub]
  have hc : (((1023+m).toNat : Nat) : ℝ) = 1023+(m : ℝ) := by
    have h := Int.toNat_of_nonneg hm
    exact_mod_cast h
  rw [hc]
  congr 1
  ring

theorem scaleFactor_zpow (m : Int) (hm : 0 ≤ 1023+m) : scaleFactor m = (2 : ℝ)^m := by
  rw [scaleFactor_exp m hm]
  cases m with
  | ofNat n => simp [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  | negSucc n =>
    rw [show Int.negSucc n = -((n+1 : Nat) : Int) by omega,
      Int.cast_neg, Int.cast_natCast, neg_mul, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), zpow_neg, zpow_natCast]

theorem index_quotient (word : UInt64) :
    ((word &&& 127).toNat : Int) + 128*(shiftInteger word/128) = shiftInteger word := by
  rw [index_remainder]
  have h := Int.emod_nonneg (shiftInteger word) (by decide : (128 : Int) ≠ 0)
  omega

theorem exp_decomposition (x : ℝ) (word : UInt64) (c : Int)
    (hc : 0 ≤ 1023+(shiftInteger word/128+c)) :
    Real.exp (((word &&& 127).toNat : ℝ)*Real.log 2/128 +
      (x-(shiftInteger word : ℝ)*(Real.log 2/128))) *
      scaleFactor (shiftInteger word/128+c) = Real.exp (x+(c : ℝ)*Real.log 2) := by
  rw [scaleFactor_exp _ hc, ← Real.exp_add]
  have hk : ((word &&& 127).toNat : ℝ) + 128*((shiftInteger word/128 : Int) : ℝ) =
      (shiftInteger word : ℝ) := by exact_mod_cast index_quotient word
  congr 1
  push_cast
  linear_combination (Real.log 2/128)*hk

theorem scaled_correction_error (x : ℝ) (word r bits : UInt64) (c : Int)
    (hc : 0 ≤ 1023+(shiftInteger word/128+c))
    (hs : value bits * (2 : ℝ)^1023 =
      value (tableScaleWord (word &&& 127).toNat) *
        (2 : ℝ)^(1023+(shiftInteger word/128+c)).toNat)
    (hf : Finite r) (hr : |value r| ≤ 3/1000)
    (hideal : |x-(shiftInteger word : ℝ)*(Real.log 2/128)| ≤ 3/1000)
    (he : |value r-(x-(shiftInteger word : ℝ)*(Real.log 2/128))| ≤
      1/1000000000000000000) :
    |value bits * (1 + value (correctionWord r table[2*(word &&& 127).toNat]!)) -
      Real.exp (x+(c : ℝ)*Real.log 2)| ≤
      (3/100000000000000000) * scaleFactor (shiftInteger word/128+c) := by
  have hi : (word &&& 127).toNat < 128 := by
    have h : (word &&& 127).toNat ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    omega
  have h := table_correction_error r (x-(shiftInteger word : ℝ)*(Real.log 2/128))
    _ hi hf hr hideal he
  have hv : value bits = value (tableScaleWord (word &&& 127).toNat) *
      scaleFactor (shiftInteger word/128+c) := by
    dsimp [scaleFactor]
    rw [← mul_div_assoc]
    apply (eq_div_iff (by positivity)).mpr
    exact hs
  rw [hv, ← exp_decomposition x word c hc]
  have hid (h f t e : ℝ) : h*f*(1+t)-e*f = (h*(1+t)-e)*f := by ring
  rw [hid, abs_mul, abs_of_pos (scaleFactor_pos _)]
  exact mul_le_mul_of_nonneg_right h (scaleFactor_pos _).le

#print axioms scaled_correction_error
end Project.ExpArm
