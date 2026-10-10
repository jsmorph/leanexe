import LeanExe.ProofKit.F64PositiveSpacing
import LeanExe.ProofKit.F64NearestEven

namespace LeanExe.ProofKit.F64NearestBinade
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64PositiveSpacing F64NearestStep

set_option exponentiation.threshold 4096

theorem power_quotient (n : Nat) :
    (2 : ℝ) ^ n / (2 : ℝ) ^ 1074 = (2 : ℝ) ^ ((n : Int) - 1074) := by
  calc
    _ = (2 : ℝ) ^ (n : Int) * (2 : ℝ) ^ (-((1074 : Nat) : Int)) := by
      simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]
    _ = _ := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1

theorem power_quotient_split (n k : Nat) (q : Int) (hn : (n : Int) = q + 1074 - k) :
    (2 : ℝ) ^ n / (2 : ℝ) ^ 1074 = (2 : ℝ) ^ q / (2 : ℝ) ^ k := by
  rw [power_quotient]
  have h : (n : Int) - 1074 = q - k := by omega
  rw [h, sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem boundary_power (e : Nat) (q : Int) (he : 1 ≤ e) (heh : e < 2048)
    (heq : (e : Int) = q + 1023) :
    value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ q := by
  rw [boundary_value e he heh, power_quotient]
  congr 1
  push_cast
  omega

theorem one_step_normal_interval (y : ℝ) (c w : UInt64) (a b : Nat)
    (ha : 1 ≤ a) (hab : a < b) (hwidth : b ≤ a + 2) (hah : a + 2 < 2047)
    (hcf : CodeLib.IEEE64.Finite c) (hw : Nearest y w)
    (hy : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y ∧
      y ≤ value (UInt64.ofNat (b * 2 ^ 52)))
    (hc : value (UInt64.ofNat (a * 2 ^ 52)) ≤ value c ∧
      value c ≤ value (UInt64.ofNat (b * 2 ^ 52)))
    (he : |value c - y| < 3 * ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074) / 2) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  have hlim : limit < 2 ^ 63 := by decide
  have hbn : b * 2 ^ 52 < limit := by change b * 2 ^ 52 < 2047 * 2 ^ 52; omega
  have han : a * 2 ^ 52 < limit :=
    lt_trans (Nat.mul_lt_mul_of_pos_right hab (Nat.two_pow_pos 52)) hbn
  have word_nat (n : Nat) (hn : n < limit) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (hn.trans (by decide : limit < 2 ^ 64))
  have hcp : 0 < value c := by
    have hp : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := by
      rw [boundary_value a ha (by omega)]
      positivity
    exact hp.trans_le hc.1
  have hcn := positive_finite_encoding c hcf hcp
  have hcr : a * 2 ^ 52 ≤ c.toNat ∧ c.toNat ≤ b * 2 ^ 52 := by
    constructor
    · have h := (value_le_iff (by rw [word_nat _ han]; exact han.trans hlim)
        (hcn.trans hlim)).mp hc.1
      simpa only [word_nat _ han] using h
    · have h := (value_le_iff (hcn.trans hlim)
        (by rw [word_nat _ hbn]; exact hbn.trans hlim)).mp hc.2
      simpa only [word_nat _ hbn] using h
  have hwr := nearest_interval y w (UInt64.ofNat (a * 2 ^ 52))
    (UInt64.ofNat (b * 2 ^ 52)) hw
    (by rw [word_nat _ han]; exact han) (by rw [word_nat _ hbn]; exact hbn) hy.1 hy.2
  simp only [word_nat _ han, word_nat _ hbn] at hwr
  apply one_step_of_spacing y ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074) c w
    (a * 2 ^ 52) (b * 2 ^ 52) (by positivity) hbn hcr hw hwr _ he
  intro n hnl hnu
  have hg := gap_two_binades n (a + 1) (by omega) (by omega) (by
    have hs : a + 1 - 1 = a := by omega
    simpa only [hs] using hnl) (by
    have hnb := hnu.trans_le (Nat.mul_le_mul_right (2 ^ 52) hwidth)
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hnb)
  have hs : a + 1 - 2 = a - 1 := by omega
  simpa only [hs] using hg

#print axioms power_quotient
#print axioms power_quotient_split
#print axioms boundary_power
#print axioms one_step_normal_interval

end LeanExe.ProofKit.F64NearestBinade
