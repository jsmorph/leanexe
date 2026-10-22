import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64ArithmeticBounds
import Library.Numerics.Float64.Exp.ExpIntegerSelection
import Library.Numerics.Float64.Exp.ExpReductionBounds

namespace Library.Numerics.Float64.Exp.ExpReductionSelection
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def product (x : UInt64) : UInt64 := Wasm.IEEE64.mul 0x40671547652B82FE x

def integer (x : UInt64) : UInt64 := ExpIntegerSelection.selected (product x)

def floatInteger (x : Float) : Float :=
  let z := Float.ofBits 0x40671547652B82FE * x
  let kd := z + Float.ofBits 0x4338000000000000
  kd - Float.ofBits 0x4338000000000000

theorem floatInteger_bits (x : Float) : (floatInteger x).toBits = integer x.toBits := by
  have hi := ExpReductionBounds.reduction_constants_finite.1
  have hm := ExpIntegerSelection.magic_values.1
  simp [floatInteger, integer, product, ExpIntegerSelection.selected, ExpIntegerSelection.shifted,
    F64Bits.toBits_mul, F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_ofBits,
    not_nan_of_finite hi, not_nan_of_finite hm]

private theorem inverse_product_magnitude (x : UInt64) (hx : |value x| ≤ 768) :
    |value 0x40671547652B82FE * value x| ≤ (147456 : ℝ) := by
  have hi : |value 0x40671547652B82FE| ≤ (192 : ℝ) := by
    rw [abs_of_pos ExpReductionBounds.inverse_bounds.1]
    exact ExpReductionBounds.inverse_upper_bound
  rw [abs_mul]
  calc
    _ ≤ 192 * 768 := mul_le_mul hi hx (abs_nonneg _) (by norm_num)
    _ = (147456 : ℝ) := by norm_num

theorem product_bounds (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    Finite (product x) ∧ |value (product x)| ≤ (2 : ℝ) ^ 18 ∧
    |value (product x) - value 0x40671547652B82FE * value x| ≤ 1 / (2 : ℝ) ^ 35 := by
  have hp := inverse_product_magnitude x hx
  have hm := F64MulBounds.mul_real_mixed 0x40671547652B82FE x
    ExpReductionBounds.reduction_constants_finite.1 hxf (hp.trans_lt (by norm_num))
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have he : |value (product x) - value 0x40671547652B82FE * value x| ≤
      1 / (2 : ℝ) ^ 35 := by
    calc
      _ ≤ unitRoundoff64 * |value 0x40671547652B82FE * value x| +
          multiplicationUnderflowEpsilon := hm.2
      _ ≤ unitRoundoff64 * (147456 : ℝ) + multiplicationUnderflowEpsilon :=
        add_le_add (mul_le_mul_of_nonneg_left hp hu) le_rfl
      _ ≤ 1 / (2 : ℝ) ^ 35 := by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
  have hmag : |value (product x)| ≤ (2 : ℝ) ^ 18 :=
    (F64ArithmeticBounds.magnitude_of_error _ _ _ _ he hp).trans (by norm_num)
  exact ⟨hm.1, hmag, he⟩

theorem integer_selection (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    ∃ k : Int, Finite (integer x) ∧
      Wasm.IEEE64.scaledValue (integer x) = k * 2 ^ 1074 ∧ k.natAbs ≤ 147457 ∧
      |(k : ℝ) - value 0x40671547652B82FE * value x| ≤
        1 / 2 + 1 / (2 : ℝ) ^ 35 := by
  have hp := product_bounds x hxf hx
  obtain ⟨k, hkf, hkv, _, hke⟩ :=
    ExpIntegerSelection.selected_integer (product x) hp.1 hp.2.1
  have he : |(k : ℝ) - value 0x40671547652B82FE * value x| ≤
      1 / 2 + 1 / (2 : ℝ) ^ 35 :=
    (abs_sub_le _ (value (product x)) _).trans (add_le_add hke hp.2.2)
  have hkm : |(k : ℝ)| ≤ (147456 : ℝ) + (1 / 2 + 1 / (2 : ℝ) ^ 35) :=
    F64ArithmeticBounds.magnitude_of_error _ _ _ _ he (inverse_product_magnitude x hx)
  have habsR : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hkr : (k.natAbs : ℝ) ≤ 147457 := by
    rw [← habsR]
    exact hkm.trans (by norm_num)
  have hkn : k.natAbs ≤ 147457 := by exact_mod_cast hkr
  exact ⟨k, hkf, hkv, hkn, he⟩

theorem selected_high_product (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    ∃ k : Int, value (integer x) = (k : ℝ) ∧
      Finite (Wasm.IEEE64.mul (integer x) 0xBF762E42FEFA0000) ∧
      value (Wasm.IEEE64.mul (integer x) 0xBF762E42FEFA0000) =
        (k : ℝ) * value 0xBF762E42FEFA0000 ∧ k.natAbs ≤ 147457 ∧
      |(k : ℝ) - value 0x40671547652B82FE * value x| ≤
        1 / 2 + 1 / (2 : ℝ) ^ 35 := by
  obtain ⟨k, hkf, hkv, hkn, hke⟩ := integer_selection x hxf hx
  have hmag : Wasm.IEEE64.scaledMagnitude (integer x) = k.natAbs * 2 ^ 1074 := by
    rw [← natAbs_scaledValue, hkv, Int.natAbs_mul]
    norm_num
  have hp := ExpReductionExact.high_mul_exact (integer x) k.natAbs hkf hmag
    (hkn.trans (by norm_num))
  have hv : value (integer x) = (k : ℝ) := by
    rw [value, hkv]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  exact ⟨k, hv, hp.1, by rw [hp.2, hv], hkn, hke⟩

#print axioms floatInteger_bits
#print axioms product_bounds
#print axioms integer_selection
#print axioms selected_high_product


theorem ideal_reduction (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    ∃ k : Int, value (integer x) = (k : ℝ) ∧
      |value x - (k : ℝ) * (Real.log 2 / 128)| ≤ 1 / 320 := by
  obtain ⟨k, hv, _, _, _, he⟩ := selected_high_product x hxf hx
  exact ⟨k, hv, ExpReductionBounds.ideal_residual_bound (value x) (k : ℝ) (hx.trans (by norm_num))
    (he.trans (by norm_num))⟩

#print axioms ideal_reduction

theorem selection_mixed_error (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    |value (integer x) - value 0x40671547652B82FE * value x| ≤
      1 / 2 + unitRoundoff64 * |value 0x40671547652B82FE * value x| +
        multiplicationUnderflowEpsilon := by
  have hp := product_bounds x hxf hx
  obtain ⟨k, _, hkv, _, hke⟩ :=
    ExpIntegerSelection.selected_integer (product x) hp.1 hp.2.1
  change Wasm.IEEE64.scaledValue (integer x) = k * 2 ^ 1074 at hkv
  have hv : value (integer x) = (k : ℝ) := by
    rw [value, hkv]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  have hm := F64MulBounds.mul_real_mixed 0x40671547652B82FE x
    ExpReductionBounds.reduction_constants_finite.1 hxf
    ((inverse_product_magnitude x hx).trans_lt (by norm_num))
  rw [hv]
  calc
    _ ≤ 1 / 2 + (unitRoundoff64 * |value 0x40671547652B82FE * value x| +
        multiplicationUnderflowEpsilon) :=
      (abs_sub_le _ (value (product x)) _).trans (add_le_add hke hm.2)
    _ = _ := by ring

#print axioms selection_mixed_error

end Library.Numerics.Float64.Exp.ExpReductionSelection
