import Verified.Examples.ExpScaleBits

namespace Verified.Examples.ExpCoreState
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def shiftedBits (x : UInt64) : UInt64 :=
  ExpIntegerSelection.shifted (ExpReductionSelection.product x)

def tailBits (x : UInt64) : UInt64 :=
  Exp.expTable[(ExpScaleBits.index (shiftedBits x)).toNat]!

def scaleBits (x : UInt64) : UInt64 := ExpScaleBits.scaleBits (shiftedBits x)

theorem prefix_state (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    ∃ (k q : Int) (j : Fin 128),
      value (ExpReductionSelection.integer x) = (k : ℝ) ∧ k = 128 * q + j.val ∧
      tailBits x = ExpTableBounds.tailBits j.val ∧
      ((shiftedBits x).toNat : Int) = (0x4338000000000000 : Int) + k ∧
      ((shiftedBits x) % 128).toNat = j.val ∧ k.natAbs ≤ 147457 := by
  obtain ⟨k, _, hkv, hkn, _⟩ := ExpReductionSelection.integer_selection x hxf hx
  have hp := ExpReductionSelection.product_bounds x hxf hx
  obtain ⟨k', _, hkv', _, hki⟩ :=
    ExpShiftedBits.shifted_encoding (ExpReductionSelection.product x) hp.1 hp.2.1
  change Wasm.IEEE64.scaledValue (ExpReductionSelection.integer x) = k' * 2 ^ 1074 at hkv'
  change ((shiftedBits x).toNat : Int) = (0x4338000000000000 : Int) + k' at hki
  have hkeq : k' = k :=
    mul_right_cancel₀ (by positivity : (2 : Int) ^ 1074 ≠ 0) (hkv'.symm.trans hkv)
  subst k'
  have hv : value (ExpReductionSelection.integer x) = (k : ℝ) := by
    rw [value, hkv]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  have hjk := ExpShiftedBits.euclidean_index k
  let j : Fin 128 := ⟨(k % 128).toNat, hjk.1⟩
  let q := k / 128
  have hk : k = 128 * q + j.val := hjk.2
  have hj : ((shiftedBits x) % 128).toNat = j.val :=
    ExpShiftedBits.table_remainder (shiftedBits x) k hki
  have ht : tailBits x = ExpTableBounds.tailBits j.val := by
    rw [tailBits, (ExpScaleBits.index_values (shiftedBits x) j hj).1]
    rfl
  exact ⟨k, q, j, hv, hk, ht, hki, hj, hkn⟩

theorem reduction_state (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 512) :
    ∃ (k q : Int) (j : Fin 128),
      value (ExpReductionSelection.integer x) = (k : ℝ) ∧ k = 128 * q + j.val ∧
      tailBits x = ExpTableBounds.tailBits j.val ∧
      Finite (scaleBits x) ∧
      value (scaleBits x) = (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val) ∧
      1 / (2 : ℝ) ^ 1000 ≤ value (scaleBits x) ∧
      value (scaleBits x) ≤ (2 : ℝ) ^ 1000 := by
  obtain ⟨k, q, j, hv, hk, ht, hki, hj, _⟩ := prefix_state x hxf (hx.trans (by norm_num))
  obtain ⟨k', _, hscaled, hsmall⟩ := ExpScaleFacts.integer_small x hxf hx
  have hv' : value (ExpReductionSelection.integer x) = (k' : ℝ) := by
    rw [value, hscaled]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  have hkeq : k' = k := by exact_mod_cast (hv'.symm.trans hv)
  subst k'
  have hq : q = k / 128 := by
    have hjb := j.isLt
    omega
  have hqb : -769 ≤ q ∧ q ≤ 768 := by
    rw [hq]
    exact ExpShiftedBits.quotient_bounds k hsmall
  have hqlo : -1000 ≤ q := by omega
  have hqhi : q ≤ 999 := by omega
  have hs : scaleBits x = ExpScaleEncoding.encodedScale j q :=
    ExpScaleBits.scale_bits_encoding (shiftedBits x) k q j hki hk hj hqlo hqhi
  have hsd := ExpScaleEncoding.encoded_scale_value j q hqlo hqhi
  exact ⟨k, q, j, hv, hk, ht, by rw [hs]; exact hsd.1,
    by rw [hs]; exact hsd.2.1, by rw [hs]; exact hsd.2.2.1,
    by rw [hs]; exact hsd.2.2.2⟩

#print axioms prefix_state
#print axioms reduction_state

end Verified.Examples.ExpCoreState
