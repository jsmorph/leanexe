import Verified.Examples.ExpCoreState
import Verified.Examples.ExpResidualBounds
import Mathlib.Data.Nat.Bitwise

namespace Verified.Examples.ExpSpecialScale
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def positiveScale (ki : UInt64) : UInt64 :=
  ExpScaleBits.scaleBits ki - ((1009 : UInt64) <<< (52 : UInt64))

def negativeScale (ki : UInt64) : UInt64 :=
  ExpScaleBits.scaleBits ki + ((1022 : UInt64) <<< (52 : UInt64))

private theorem positive_adjustment (w : UInt64) :
    w - ((1009 : UInt64) <<< (52 : UInt64)) = w + UInt64.ofNat (3087 * 2 ^ 52) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat',
    UInt64.toNat_shiftLeft, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  change (2 ^ 64 - 1009 * 2 ^ 52 + w.toNat) % 2 ^ 64 =
    (w.toNat + ((3087 * 2 ^ 52) % 2 ^ 64)) % 2 ^ 64
  rw [Nat.mod_eq_of_lt (by decide : 3087 * 2 ^ 52 < 2 ^ 64)]
  congr 1
  omega

theorem positive_scale_encoding (ki : UInt64) (k q : Int) (j : Fin 128)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hk : k = 128 * q + j.val) (hj : (ki % 128).toNat = j.val)
    (hqlo : 0 ≤ q) (hqhi : q ≤ 2008) :
    positiveScale ki = ExpScaleEncoding.encodedScale j (q - 1009) := by
  let e := (1023 + (q - 1009)).toNat
  have he : e < 2048 := by dsimp [e]; omega
  have heq : 1023 + q + (3087 : Nat) = (e : Int) + 4096 * (1 : Nat) := by
    dsimp [e]
    omega
  rw [positiveScale, positive_adjustment]
  exact ExpScaleBits.scale_bits_adjusted_encoding ki k q j 3087 e 1 hki hk hj heq he

theorem negative_scale_encoding (ki : UInt64) (k q : Int) (j : Fin 128)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hk : k = 128 * q + j.val) (hj : (ki % 128).toNat = j.val)
    (hqlo : -2022 ≤ q) (hqhi : q ≤ 0) :
    negativeScale ki = ExpScaleEncoding.encodedScale j (q + 1022) := by
  let e := (1023 + (q + 1022)).toNat
  have he : e < 2048 := by dsimp [e]; omega
  have heq : 1023 + q + (1022 : Nat) = (e : Int) + 4096 * (0 : Nat) := by
    dsimp [e]
    omega
  have hc : ((1022 : UInt64) <<< (52 : UInt64)) = UInt64.ofNat (1022 * 2 ^ 52) := by
    decide +kernel
  rw [negativeScale, hc]
  exact ExpScaleBits.scale_bits_adjusted_encoding ki k q j 1022 e 0 hki hk hj heq he

theorem quotient_bounds (k q : Int) (j : Fin 128)
    (hk : k = 128 * q + j.val) (hkn : k.natAbs ≤ 147457) :
    -1153 ≤ q ∧ q ≤ 1152 := by
  have h : (k.natAbs : Int) ≤ 147457 := by exact_mod_cast hkn
  rw [← Int.abs_eq_natAbs] at h
  have hb := abs_le.mp h
  have hjb := j.isLt
  omega

theorem positive_quotient (x : UInt64) (k q : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 768) (hxpos : 512 ≤ value x)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) : 9 ≤ q := by
  by_contra hn
  have hkI : k ≤ 1151 := by
    have hjb := j.isLt
    omega
  have hkR : (k : ℝ) ≤ 1151 := by exact_mod_cast hkI
  have hi := abs_le.mp (ExpResidualBounds.ideal_bound x hxf hx)
  dsimp [ExpResidualBounds.ideal] at hi
  rw [hkv] at hi
  have hl := ExpReductionBounds.log_two_coarse_bounds
  have hm := mul_le_mul_of_nonneg_right hkR (by linarith only [hl.1] : 0 ≤ Real.log 2)
  nlinarith only [hi.2, hm, hl.2, hxpos]

theorem negative_quotient (x : UInt64) (k q : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 768) (hxneg : value x ≤ -512)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) : q ≤ -23 := by
  by_contra hn
  have hkI : -2816 ≤ k := by omega
  have hkR : (-2816 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkI
  have hi := abs_le.mp (ExpResidualBounds.ideal_bound x hxf hx)
  dsimp [ExpResidualBounds.ideal] at hi
  rw [hkv] at hi
  have hl := ExpReductionBounds.log_two_coarse_bounds
  have hm := mul_le_mul_of_nonneg_right hkR (by linarith only [hl.1] : 0 ≤ Real.log 2)
  nlinarith only [hi.1, hm, hl.2, hxneg]

theorem positive_scale_value (ki : UInt64) (k q : Int) (j : Fin 128)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hk : k = 128 * q + j.val) (hj : (ki % 128).toNat = j.val)
    (hqlo : 9 ≤ q) (hqhi : q ≤ 2008) :
    Finite (positiveScale ki) ∧
      value (positiveScale ki) = (2 : ℝ) ^ (q - 1009) *
        value (ExpTableBounds.headBits j.val) ∧
      1 / (2 : ℝ) ^ 1000 ≤ value (positiveScale ki) ∧
      value (positiveScale ki) ≤ (2 : ℝ) ^ 1000 := by
  rw [positive_scale_encoding ki k q j hki hk hj (by omega) hqhi]
  exact ExpScaleEncoding.encoded_scale_value j (q - 1009) (by omega) (by omega)

theorem negative_scale_value (ki : UInt64) (k q : Int) (j : Fin 128)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hk : k = 128 * q + j.val) (hj : (ki % 128).toNat = j.val)
    (hqlo : -2022 ≤ q) (hqhi : q ≤ -23) :
    Finite (negativeScale ki) ∧
      value (negativeScale ki) = (2 : ℝ) ^ (q + 1022) *
        value (ExpTableBounds.headBits j.val) ∧
      1 / (2 : ℝ) ^ 1000 ≤ value (negativeScale ki) ∧
      value (negativeScale ki) ≤ (2 : ℝ) ^ 1000 := by
  rw [negative_scale_encoding ki k q j hki hk hj hqlo (by omega)]
  exact ExpScaleEncoding.encoded_scale_value j (q + 1022) (by omega) (by omega)

theorem sign_guard (ki : UInt64) (k : Int)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hkn : k.natAbs ≤ 2 ^ 30) :
    ki &&& 0x80000000 = if k < 0 then 0x80000000 else 0 := by
  have h : (k.natAbs : Int) ≤ 2 ^ 30 := by exact_mod_cast hkn
  rw [← Int.abs_eq_natAbs] at h
  have hb := abs_le.mp h
  by_cases hk : k < 0
  · have hm : ki.toNat / 2 ^ 31 % 2 = 1 := by omega
    have ht : ki.toNat.testBit 31 = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hm]
      rfl
    rw [ite_eq_left hk]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt64.reduceToNat]
    change ki.toNat &&& 2 ^ 31 = 2 ^ 31
    rw [Nat.and_two_pow, ht]
    rfl
  · have hm : ki.toNat / 2 ^ 31 % 2 = 0 := by omega
    have ht : ki.toNat.testBit 31 = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq, hm]
      rfl
    rw [ite_eq_right hk]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt64.reduceToNat]
    change ki.toNat &&& 2 ^ 31 = 0
    rw [Nat.and_two_pow, ht]
    rfl

#print axioms positive_scale_encoding
#print axioms negative_scale_encoding
#print axioms quotient_bounds
#print axioms positive_quotient
#print axioms negative_quotient
#print axioms positive_scale_value
#print axioms negative_scale_value
#print axioms sign_guard

end Verified.Examples.ExpSpecialScale
