import Library.Numerics.Float64.Exp.ExpHighResidual

namespace Library.Numerics.Float64.Exp.ExpResidualBounds
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def lowProduct (x : UInt64) : UInt64 :=
  Wasm.IEEE64.mul (ExpReductionSelection.integer x) 0xBD0CF79ABC9E3B3A

def residual (x : UInt64) : UInt64 :=
  Wasm.IEEE64.add (ExpHighResidual.highResidual x) (lowProduct x)

noncomputable def ideal (x : UInt64) : ℝ :=
  value x - value (ExpReductionSelection.integer x) * (Real.log 2 / 128)

theorem integer_bounds (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    Finite (ExpReductionSelection.integer x) ∧
      |value (ExpReductionSelection.integer x)| ≤ (2 : ℝ) ^ 18 := by
  obtain ⟨k, hkf, hkv, hkn, _⟩ := ExpReductionSelection.integer_selection x hxf hx
  have hv : value (ExpReductionSelection.integer x) = (k : ℝ) := by
    rw [value, hkv]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hkr : (k.natAbs : ℝ) ≤ 147457 := by exact_mod_cast hkn
  refine ⟨hkf, ?_⟩
  rw [hv, habs]
  exact hkr.trans (by norm_num)

theorem low_product_bounds (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    Finite (lowProduct x) ∧
      |value (lowProduct x) -
        value (ExpReductionSelection.integer x) * value 0xBD0CF79ABC9E3B3A| ≤
        1 / (2 : ℝ) ^ 79 := by
  have hk := integer_bounds x hxf hx
  have hp : |value (ExpReductionSelection.integer x) * value 0xBD0CF79ABC9E3B3A| ≤
      1 / (2 : ℝ) ^ 27 := by
    rw [abs_mul]
    calc
      _ ≤ (2 : ℝ) ^ 18 * (1 / (2 : ℝ) ^ 45) :=
        mul_le_mul hk.2 ExpReductionBounds.low_magnitude (abs_nonneg _) (by positivity)
      _ = _ := by norm_num
  have hm := F64MulBounds.mul_real_mixed (ExpReductionSelection.integer x)
    0xBD0CF79ABC9E3B3A hk.1 ExpReductionBounds.reduction_constants_finite.2.2.2
    (hp.trans_lt (by norm_num))
  refine ⟨hm.1, ?_⟩
  calc
    _ ≤ unitRoundoff64 *
        |value (ExpReductionSelection.integer x) * value 0xBD0CF79ABC9E3B3A| +
        multiplicationUnderflowEpsilon := hm.2
    _ ≤ unitRoundoff64 * (1 / (2 : ℝ) ^ 27) + multiplicationUnderflowEpsilon :=
      add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num [unitRoundoff64])) le_rfl
    _ ≤ 1 / (2 : ℝ) ^ 79 := by
      norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]

theorem ideal_bound (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    |ideal x| ≤ 1 / 320 := by
  obtain ⟨k, hv, he⟩ := ExpReductionSelection.ideal_reduction x hxf hx
  simpa only [ideal, hv] using he

theorem raw_residual_error (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    |value (ExpHighResidual.highResidual x) + value (lowProduct x) - ideal x| ≤
      1 / (2 : ℝ) ^ 78 := by
  have hh := ExpHighResidual.high_residual_exact x hxf hx
  have hl := low_product_bounds x hxf hx
  have hk := (integer_bounds x hxf hx).2
  have hid : value (ExpHighResidual.highResidual x) + value (lowProduct x) - ideal x =
      (value (lowProduct x) -
        value (ExpReductionSelection.integer x) * value 0xBD0CF79ABC9E3B3A) +
      (-value (ExpReductionSelection.integer x)) *
        (value 0x3F762E42FEFA0000 + value 0x3D0CF79ABC9E3B3A - Real.log 2 / 128) := by
    rw [hh.2, ExpReductionBounds.negative_low_value]
    dsimp [ideal]
    ring
  rw [hid]
  calc
    _ ≤ |value (lowProduct x) -
        value (ExpReductionSelection.integer x) * value 0xBD0CF79ABC9E3B3A| +
      |(-value (ExpReductionSelection.integer x)) *
        (value 0x3F762E42FEFA0000 + value 0x3D0CF79ABC9E3B3A - Real.log 2 / 128)| :=
      abs_add_le _ _
    _ = |value (lowProduct x) -
        value (ExpReductionSelection.integer x) * value 0xBD0CF79ABC9E3B3A| +
      |value (ExpReductionSelection.integer x)| *
        |value 0x3F762E42FEFA0000 + value 0x3D0CF79ABC9E3B3A - Real.log 2 / 128| := by
      rw [abs_mul, abs_neg]
    _ ≤ 1 / (2 : ℝ) ^ 79 + (2 : ℝ) ^ 18 * (1 / (2 : ℝ) ^ 99) :=
      add_le_add hl.2 (mul_le_mul hk ExpReductionBounds.split_error
        (abs_nonneg _) (by positivity))
    _ ≤ 1 / (2 : ℝ) ^ 78 := by norm_num

theorem residual_bounds (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    Finite (residual x) ∧ |value (residual x)| ≤ 1 / 256 ∧
      |value (residual x) - ideal x| ≤ 1 / (2 : ℝ) ^ 60 := by
  have hh := ExpHighResidual.high_residual_exact x hxf hx
  have hl := low_product_bounds x hxf hx
  have hi := ideal_bound x hxf hx
  have hr := raw_residual_error x hxf hx
  have hraw : |value (ExpHighResidual.highResidual x) + value (lowProduct x)| ≤
      1 / 256 :=
    (F64ArithmeticBounds.magnitude_of_error _ _ _ _ hr hi).trans (by norm_num)
  have ha := F64AddBounds.add_real_relative (ExpHighResidual.highResidual x)
    (lowProduct x) hh.1 hl.1 (hraw.trans_lt (by norm_num))
  have hae : |value (residual x) -
      (value (ExpHighResidual.highResidual x) + value (lowProduct x))| ≤
      1 / (2 : ℝ) ^ 61 := by
    calc
      _ ≤ unitRoundoff64 *
          |value (ExpHighResidual.highResidual x) + value (lowProduct x)| := ha.2
      _ ≤ unitRoundoff64 * (1 / 256) :=
        mul_le_mul_of_nonneg_left hraw (by norm_num [unitRoundoff64])
      _ = _ := by norm_num [unitRoundoff64]
  have he : |value (residual x) - ideal x| ≤ 1 / (2 : ℝ) ^ 60 :=
    ((abs_sub_le _ (value (ExpHighResidual.highResidual x) + value (lowProduct x)) _).trans
      (add_le_add hae hr)).trans (by norm_num)
  exact ⟨ha.1, (F64ArithmeticBounds.magnitude_of_error _ _ _ _ he hi).trans
    (by norm_num), he⟩

#print axioms integer_bounds
#print axioms low_product_bounds
#print axioms ideal_bound
#print axioms raw_residual_error
#print axioms residual_bounds

end Library.Numerics.Float64.Exp.ExpResidualBounds
