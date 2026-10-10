import LeanExe.ProofKit.F64PositiveOrder

namespace LeanExe.ProofKit.F64NearestStep
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder

theorem upper_midpoint (a b y : ℝ) (hab : a < b)
    (h : |a - y| ≤ |b - y|) : 2 * y ≤ a + b := by
  by_cases hy : y ≤ a
  · linarith
  · by_cases hyb : y ≤ b
    · rw [abs_of_nonpos (by linarith : a - y ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ b - y)] at h
      linarith
    · rw [abs_of_nonpos (by linarith : a - y ≤ 0),
        abs_of_nonpos (by linarith : b - y ≤ 0)] at h
      linarith

theorem lower_midpoint (a b y : ℝ) (hba : b < a)
    (h : |a - y| ≤ |b - y|) : a + b ≤ 2 * y := by
  have hn : |(-a) - (-y)| ≤ |(-b) - (-y)| := by
    simpa only [neg_sub_neg, abs_sub_comm] using h
  have hm := upper_midpoint (-a) (-b) (-y) (by linarith) hn
  linarith

theorem one_step_of_spacing (y d : ℝ) (c w : UInt64) (L U : Nat)
    (hd : 0 < d) (hU : U < limit)
    (hc : L ≤ c.toNat ∧ c.toNat ≤ U)
    (hw : Nearest y w) (hwr : L ≤ w.toNat ∧ w.toNat ≤ U)
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n))
    (he : |value c - y| < 3 * d / 2) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  have hlim : limit < 2 ^ 63 := by decide
  have word_nat (n : Nat) (hn : n ≤ U) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (lt_trans (hn.trans_lt hU) (by decide : limit < 2 ^ 64))
  constructor
  · by_contra h
    have hw1 : w.toNat + 1 ≤ U := by omega
    have hw2 : w.toNat + 2 ≤ U := by omega
    have hg1 := hspacing w.toNat hwr.1 (by omega)
    have hg2 := hspacing (w.toNat + 1) (by omega) (by omega)
    simp only [UInt64.ofNat_toNat] at hg1
    have hv : value w < value (UInt64.ofNat (w.toNat + 1)) := by linarith
    have hn : (UInt64.ofNat (w.toNat + 1)).toNat < limit := by
      rw [word_nat _ hw1]
      omega
    have hm := upper_midpoint _ _ y hv (hw.2 _ hn)
    have hc2 : value (UInt64.ofNat (w.toNat + 2)) ≤ value c := by
      apply (value_le_iff (by rw [word_nat _ hw2]; omega)
        (lt_of_le_of_lt hc.2 (hU.trans hlim))).mpr
      rw [word_nat _ hw2]
      omega
    have he' := (le_abs_self (value c - y)).trans_lt he
    norm_num only [Nat.add_assoc, Nat.reduceAdd] at hg2
    linarith
  · by_contra h
    have hwp : 2 ≤ w.toNat := by omega
    have hmL : L ≤ w.toNat - 1 := by omega
    have hpL : L ≤ w.toNat - 2 := by omega
    have hmU : w.toNat - 1 ≤ U := by omega
    have hpU : w.toNat - 2 ≤ U := by omega
    have hg1 := hspacing (w.toNat - 1) hmL (by omega)
    have hg2 := hspacing (w.toNat - 2) hpL (by omega)
    have hmadd : w.toNat - 1 + 1 = w.toNat := by omega
    have hpadd : w.toNat - 2 + 1 = w.toNat - 1 := by omega
    rw [hmadd, UInt64.ofNat_toNat] at hg1
    rw [hpadd] at hg2
    have hv : value (UInt64.ofNat (w.toNat - 1)) < value w := by linarith
    have hn : (UInt64.ofNat (w.toNat - 1)).toNat < limit := by
      rw [word_nat _ hmU]
      omega
    have hm := lower_midpoint _ _ y hv (hw.2 _ hn)
    have hc2 : value c ≤ value (UInt64.ofNat (w.toNat - 2)) := by
      apply (value_le_iff (lt_of_le_of_lt hc.2 (hU.trans hlim))
        (by rw [word_nat _ hpU]; omega)).mpr
      rw [word_nat _ hpU]
      omega
    have he' := (neg_le_abs (value c - y)).trans_lt he
    linarith

#print axioms one_step_of_spacing

end LeanExe.ProofKit.F64NearestStep
