import LeanExe.ProofKit.F64PositiveOrder

namespace LeanExe.ProofKit.F64PositiveSpacing
open CodeLib.IEEE64 F64PositiveOrder

set_option exponentiation.threshold 4096

theorem boundary_value (e : Nat) (he : 1 ≤ e) (heh : e < 2048) :
    value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ (e + 51) / (2 : ℝ) ^ 1074 := by
  have hn : e * 2 ^ 52 < 2 ^ 63 := by norm_num at heh ⊢; omega
  have hw : (UInt64.ofNat (e * 2 ^ 52)).toNat = e * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (hn.trans (by norm_num : 2 ^ 63 < 2 ^ 64))
  have hd : e * 2 ^ 52 / 2 ^ 52 = e := by omega
  have hm : e * 2 ^ 52 % 2 ^ 52 = 0 := by omega
  rw [F64Adjacent.unsigned_word_value _ (by rw [hw]; exact hn), hw]
  simp only [F64Order.unsignedScaled, hd, hm, show e ≠ 0 by omega,
    ite_false, Nat.add_zero]
  have hp : (2 : Nat) ^ 52 * 2 ^ (e - 1) = 2 ^ (e + 51) := by
    rw [← pow_add]
    congr 1
    omega
  simp only [hp, Nat.cast_pow, Nat.cast_ofNat]

theorem gap_binade (n e : Nat) (he : 1 ≤ e) (heh : e + 1 < 2048)
    (hnl : e * 2 ^ 52 ≤ n) (hnu : n < (e + 1) * 2 ^ 52) :
    value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n) =
      (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 := by
  have hcap : (e + 1) * 2 ^ 52 < 2 ^ 63 := by norm_num at heh ⊢; omega
  have hnp : n + 1 < 2 ^ 63 := lt_of_le_of_lt (by omega) hcap
  have hw : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' ((lt_of_lt_of_le hnu hcap.le).trans
      (by norm_num : 2 ^ 63 < 2 ^ 64))
  have hg := F64Adjacent.positive_successor_gap (UInt64.ofNat n) (by rw [hw]; exact hnp)
  have hi : UInt64.ofNat n + 1 = UInt64.ofNat (n + 1) := (UInt64.ofNat_add n 1).symm
  have hd : n / 2 ^ 52 = e := by omega
  rw [hi, hw, hd] at hg
  exact hg

theorem gap_two_binades (n e : Nat) (he : 2 ≤ e) (heh : e + 1 < 2048)
    (hnl : (e - 1) * 2 ^ 52 ≤ n) (hnu : n < (e + 1) * 2 ^ 52) :
    (2 : ℝ) ^ (e - 2) / (2 : ℝ) ^ 1074 ≤
      value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n) := by
  by_cases hn : n < e * 2 ^ 52
  · have hg := gap_binade n (e - 1) (by omega) (by omega) hnl (by
      have hs : e - 1 + 1 = e := by omega
      simpa only [hs] using hn)
    have hs : e - 1 - 1 = e - 2 := by omega
    exact le_of_eq (by simpa only [hs] using hg.symm)
  · have hg := gap_binade n e (by omega) heh (Nat.le_of_not_gt hn) hnu
    calc
      _ ≤ (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 :=
        div_le_div_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)) (by positivity)
      _ = _ := hg.symm

#print axioms boundary_value
#print axioms gap_binade
#print axioms gap_two_binades

end LeanExe.ProofKit.F64PositiveSpacing
