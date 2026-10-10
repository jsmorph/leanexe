import Verified.Examples.ExpNegativeFinal
import LeanExe.ProofKit.RealExpError

/-!
The special path of `Exp.exp` for `768 < abs a < 1024`, with coarse bounds.  The reduction keeps
a residual of at most `1/256`, although the high product may round, so the reconstruction stays
within a few percent of its scale.  For positive `a` the scale exceeds `2 ^ 98` and the final
product is infinity, as is the reference.  For negative `a` the scale is below `2 ^ -85`, the
compensated sequence gives zero or the smallest subnormal, and the reference is zero.
-/

namespace Verified.Examples.ExpFarRange
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64Magnitude

set_option exponentiation.threshold 4096

theorem far_product (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 1024) :
    Finite (ExpReductionSelection.product x) ∧
      |value (ExpReductionSelection.product x)| ≤ (2 : ℝ) ^ 18 ∧
      |value (ExpReductionSelection.product x) - value 0x40671547652B82FE * value x| ≤
        1 / (2 : ℝ) ^ 34 := by
  have hp : |value 0x40671547652B82FE * value x| ≤ (196608 : ℝ) := by
    have hi : |value 0x40671547652B82FE| ≤ (192 : ℝ) := by
      rw [abs_of_pos ExpReductionBounds.inverse_bounds.1]
      exact ExpReductionBounds.inverse_upper_bound
    rw [abs_mul]
    calc
      _ ≤ 192 * 1024 := mul_le_mul hi hx (abs_nonneg _) (by norm_num)
      _ = (196608 : ℝ) := by norm_num
  have hm := F64MulBounds.mul_real_mixed 0x40671547652B82FE x
    ExpReductionBounds.reduction_constants_finite.1 hxf (hp.trans_lt (by norm_num))
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have he : |value (ExpReductionSelection.product x) - value 0x40671547652B82FE * value x| ≤
      1 / (2 : ℝ) ^ 34 := by
    calc
      _ ≤ unitRoundoff64 * |value 0x40671547652B82FE * value x| +
          multiplicationUnderflowEpsilon := hm.2
      _ ≤ unitRoundoff64 * (196608 : ℝ) + multiplicationUnderflowEpsilon :=
        add_le_add (mul_le_mul_of_nonneg_left hp hu) le_rfl
      _ ≤ 1 / (2 : ℝ) ^ 34 := by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]
  have hmag : |value (ExpReductionSelection.product x)| ≤ (2 : ℝ) ^ 18 :=
    (F64ArithmeticBounds.magnitude_of_error _ _ _ _ he hp).trans (by norm_num)
  exact ⟨hm.1, hmag, he⟩

/-- `ExpCoreState.prefix_state` for `abs a ≤ 1024`. -/
theorem far_state (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 1024) :
    ∃ (k q : Int) (j : Fin 128),
      Finite (ExpReductionSelection.integer x) ∧
      value (ExpReductionSelection.integer x) = (k : ℝ) ∧ k = 128 * q + j.val ∧
      ExpCoreState.tailBits x = ExpTableBounds.tailBits j.val ∧
      ((ExpCoreState.shiftedBits x).toNat : Int) = (0x4338000000000000 : Int) + k ∧
      ((ExpCoreState.shiftedBits x) % 128).toNat = j.val ∧ k.natAbs ≤ 196609 ∧
      |(k : ℝ) - value 0x40671547652B82FE * value x| ≤ 1 / 2 + 1 / (2 : ℝ) ^ 34 := by
  have hp := far_product x hxf hx
  obtain ⟨k, hkf, hkv, _, hke⟩ :=
    ExpIntegerSelection.selected_integer (ExpReductionSelection.product x) hp.1 hp.2.1
  obtain ⟨k', _, hkv', _, hki⟩ :=
    ExpShiftedBits.shifted_encoding (ExpReductionSelection.product x) hp.1 hp.2.1
  change Wasm.IEEE64.scaledValue (ExpReductionSelection.integer x) = k * 2 ^ 1074 at hkv
  change Wasm.IEEE64.scaledValue (ExpReductionSelection.integer x) = k' * 2 ^ 1074 at hkv'
  change ((ExpCoreState.shiftedBits x).toNat : Int) = (0x4338000000000000 : Int) + k' at hki
  have hkeq : k' = k :=
    mul_right_cancel₀ (by positivity : (2 : Int) ^ 1074 ≠ 0) (hkv'.symm.trans hkv)
  subst k'
  have hv : value (ExpReductionSelection.integer x) = (k : ℝ) := by
    rw [value, hkv]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  have he : |(k : ℝ) - value 0x40671547652B82FE * value x| ≤ 1 / 2 + 1 / (2 : ℝ) ^ 34 :=
    (abs_sub_le _ (value (ExpReductionSelection.product x)) _).trans (add_le_add hke hp.2.2)
  have hpm : |value 0x40671547652B82FE * value x| ≤ (196608 : ℝ) := by
    have hi : |value 0x40671547652B82FE| ≤ (192 : ℝ) := by
      rw [abs_of_pos ExpReductionBounds.inverse_bounds.1]
      exact ExpReductionBounds.inverse_upper_bound
    rw [abs_mul]
    calc
      _ ≤ 192 * 1024 := mul_le_mul hi hx (abs_nonneg _) (by norm_num)
      _ = (196608 : ℝ) := by norm_num
  have hkm : |(k : ℝ)| ≤ (196608 : ℝ) + (1 / 2 + 1 / (2 : ℝ) ^ 34) :=
    F64ArithmeticBounds.magnitude_of_error _ _ _ _ he hpm
  have habsR : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hkr : (k.natAbs : ℝ) ≤ 196609 := by
    rw [← habsR]
    exact hkm.trans (by norm_num)
  have hkn : k.natAbs ≤ 196609 := by exact_mod_cast hkr
  have hjk := ExpShiftedBits.euclidean_index k
  let j : Fin 128 := ⟨(k % 128).toNat, hjk.1⟩
  have hj : ((ExpCoreState.shiftedBits x) % 128).toNat = j.val :=
    ExpShiftedBits.table_remainder (ExpCoreState.shiftedBits x) k hki
  have ht : ExpCoreState.tailBits x = ExpTableBounds.tailBits j.val := by
    rw [ExpCoreState.tailBits, (ExpScaleBits.index_values (ExpCoreState.shiftedBits x) j hj).1]
    rfl
  exact ⟨k, k / 128, j, hkf, hv, hjk.2, ht, hki, hj, hkn, he⟩

/-- The residual for `abs a ≤ 1024` is at most `1/256`, whether or not the high product is
exact. -/
theorem far_residual (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 1024) :
    Finite (ExpResidualBounds.residual x) ∧ |value (ExpResidualBounds.residual x)| ≤ 1 / 256 := by
  obtain ⟨k, q, j, hkf, hkv, _, _, _, _, hkn, hke⟩ := far_state x hxf hx
  have hid := ExpReductionBounds.ideal_residual_bound (value x) k hx hke
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hu0 : 0 ≤ unitRoundoff64 := by rw [hu]; positivity
  have heps : multiplicationUnderflowEpsilon ≤ 1 / (2 : ℝ) ^ 100 := by
    norm_num [multiplicationUnderflowEpsilon]
  have hkb : |(k : ℝ)| ≤ (2 : ℝ) ^ 18 := by
    have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    rw [habs]
    have : (k.natAbs : ℝ) ≤ 196609 := by exact_mod_cast hkn
    linarith [show (196609 : ℝ) ≤ 2 ^ 18 by norm_num]
  have hlog := ExpReductionBounds.log_two_coarse_bounds
  have hsplit := abs_le.mp ExpReductionBounds.split_error
  have hNH := ExpHighResidual.negative_high_value
  have hNL := ExpReductionBounds.negative_low_value
  have hlm := ExpReductionBounds.low_magnitude
  rw [hNL, abs_neg] at hlm
  have hLb := abs_le.mp hlm
  have hHc : |value 0x3F762E42FEFA0000| ≤ 1 / 128 := by
    rw [abs_le]
    constructor <;> linarith
  have hfin := ExpReductionBounds.reduction_constants_finite
  -- the high product
  have hkNH : |(k : ℝ) * value 0xBF762E42FEFA0000| ≤ (2 : ℝ) ^ 18 * (1 / 128) := by
    rw [hNH, abs_mul, abs_neg]
    exact mul_le_mul hkb hHc (abs_nonneg _) (by positivity)
  have hm := F64MulBounds.mul_real_mixed (ExpReductionSelection.integer x) 0xBF762E42FEFA0000
    hkf hfin.2.2.1 (by rw [hkv]; exact hkNH.trans_lt (by norm_num))
  rw [hkv] at hm
  have hhp : |value (ExpHighResidual.highProduct x) - (k : ℝ) * value 0xBF762E42FEFA0000| ≤
      1 / (2 : ℝ) ^ 41 := by
    calc
      _ ≤ unitRoundoff64 * |(k : ℝ) * value 0xBF762E42FEFA0000| +
          multiplicationUnderflowEpsilon := hm.2
      _ ≤ 1 / (2 : ℝ) ^ 53 * ((2 : ℝ) ^ 18 * (1 / 128)) + 1 / (2 : ℝ) ^ 100 := by
        rw [hu]
        exact add_le_add (mul_le_mul_of_nonneg_left hkNH (by positivity)) heps
      _ ≤ _ := by norm_num
  -- the split of log 2 / 128
  have hkHL : |(k : ℝ) * (Real.log 2 / 128 - value 0x3F762E42FEFA0000)| ≤ 1 / (2 : ℝ) ^ 26 := by
    rw [abs_mul]
    have hd : |Real.log 2 / 128 - value 0x3F762E42FEFA0000| ≤ 1 / (2 : ℝ) ^ 45 + 1 / (2 : ℝ) ^ 99 := by
      rw [abs_le]
      constructor <;> linarith
    calc
      _ ≤ (2 : ℝ) ^ 18 * (1 / (2 : ℝ) ^ 45 + 1 / (2 : ℝ) ^ 99) :=
        mul_le_mul hkb hd (abs_nonneg _) (by positivity)
      _ ≤ _ := by norm_num
  have hkHL2 : |(k : ℝ) * (Real.log 2 / 128 - value 0x3F762E42FEFA0000 -
      value 0x3D0CF79ABC9E3B3A)| ≤ 1 / (2 : ℝ) ^ 80 := by
    rw [abs_mul]
    have hd : |Real.log 2 / 128 - value 0x3F762E42FEFA0000 - value 0x3D0CF79ABC9E3B3A| ≤
        1 / (2 : ℝ) ^ 99 := by
      rw [abs_le]
      constructor <;> linarith
    calc
      _ ≤ (2 : ℝ) ^ 18 * (1 / (2 : ℝ) ^ 99) := mul_le_mul hkb hd (abs_nonneg _) (by positivity)
      _ ≤ _ := by norm_num
  -- the high residual
  rw [hNH, mul_neg, sub_neg_eq_add] at hhp
  have hxhp : |value x + value (ExpHighResidual.highProduct x)| ≤ 1 / 300 := by
    have h1 := abs_le.mp hid
    have h2 := abs_le.mp hhp
    rw [mul_sub] at hkHL
    have h3 := abs_le.mp hkHL
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hhrf, hhre⟩ := F64AddBounds.add_real_relative x (ExpHighResidual.highProduct x) hxf
    hm.1 (hxhp.trans_lt (by norm_num))
  have hhr : |value (ExpHighResidual.highResidual x) -
      (value x + value (ExpHighResidual.highProduct x))| ≤ 1 / (2 : ℝ) ^ 53 * (1 / 300) := by
    rw [← hu]
    exact hhre.trans (mul_le_mul_of_nonneg_left hxhp hu0)
  -- the low product
  have hkNL : |(k : ℝ) * value 0xBD0CF79ABC9E3B3A| ≤ (2 : ℝ) ^ 18 * (1 / (2 : ℝ) ^ 45) := by
    rw [hNL, abs_mul, abs_neg]
    exact mul_le_mul hkb hlm (abs_nonneg _) (by positivity)
  have hml := F64MulBounds.mul_real_mixed (ExpReductionSelection.integer x) 0xBD0CF79ABC9E3B3A
    hkf hfin.2.2.2 (by rw [hkv]; exact hkNL.trans_lt (by norm_num))
  rw [hkv] at hml
  have hlp : |value (ExpResidualBounds.lowProduct x) - (k : ℝ) * value 0xBD0CF79ABC9E3B3A| ≤
      1 / (2 : ℝ) ^ 79 := by
    calc
      _ ≤ unitRoundoff64 * |(k : ℝ) * value 0xBD0CF79ABC9E3B3A| +
          multiplicationUnderflowEpsilon := hml.2
      _ ≤ 1 / (2 : ℝ) ^ 53 * ((2 : ℝ) ^ 18 * (1 / (2 : ℝ) ^ 45)) + 1 / (2 : ℝ) ^ 100 := by
        rw [hu]
        exact add_le_add (mul_le_mul_of_nonneg_left hkNL (by positivity)) heps
      _ ≤ _ := by norm_num
  -- the residual
  have hsum : |value (ExpHighResidual.highResidual x) + value (ExpResidualBounds.lowProduct x)| ≤
      1 / 310 := by
    have h1 := abs_le.mp hid
    have h2 := abs_le.mp hhp
    have h3 := hkHL2
    have h4 := abs_le.mp hhr
    have h5 := hlp
    rw [mul_sub, mul_sub] at h3
    rw [hNL, mul_neg, sub_neg_eq_add] at h5
    have h3' := abs_le.mp h3
    have h5' := abs_le.mp h5
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hrf, hre⟩ := F64AddBounds.add_real_relative (ExpHighResidual.highResidual x)
    (ExpResidualBounds.lowProduct x) hhrf hml.1 (hsum.trans_lt (by norm_num))
  refine ⟨hrf, ?_⟩
  have hre' : |value (ExpResidualBounds.residual x) - (value (ExpHighResidual.highResidual x) +
      value (ExpResidualBounds.lowProduct x))| ≤ unitRoundoff64 * (1 / 310) :=
    hre.trans (mul_le_mul_of_nonneg_left hsum hu0)
  have hr := abs_le.mp hre'
  have hs := abs_le.mp hsum
  rw [hu] at hr
  have hc : 1 / (2 : ℝ) ^ 53 * (1 / 310) ≤ 1 / 256 - 1 / 310 := by norm_num
  rw [abs_le]
  constructor <;> linarith

theorem log_two_fine : Real.log 2 ≤ 6932 / 10000 := by
  have hu : ExpReductionBounds.upperLogTwo ≤ (6932 / 10000 : ℚ) := by decide +kernel
  have hc : (ExpReductionBounds.upperLogTwo : ℝ) ≤ ((6932 / 10000 : ℚ) : ℝ) := Rat.cast_le.mpr hu
  have h : ((6932 / 10000 : ℚ) : ℝ) = 6932 / 10000 := by norm_num
  rw [h] at hc
  exact ExpReductionBounds.log_two_enclosure.2.trans hc

/-- From 768 on, `exp` reaches the overflow threshold. -/
theorem exp_ge_overflow (a : ℝ) (ha : 768 ≤ a) :
    F64PositiveRounding.overflowThreshold ≤ Real.exp a := by
  have hl := log_two_fine
  have h1 : ((1024 : Nat) : ℝ) * Real.log 2 ≤ a := by push_cast; linarith
  have h2 : (2 : ℝ) ^ 1024 ≤ Real.exp a := by
    rw [← RealExpError.exp_pow_two]
    exact Real.exp_le_exp.mpr h1
  have h3 : F64PositiveRounding.overflowThreshold ≤ (2 : ℝ) ^ 1024 := by
    rw [show F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 from rfl]
    have : (0 : ℝ) ≤ 2 ^ 970 := by positivity
    linarith
  linarith

/-- Up to -768, `exp` is at most `2 ^ -1100`. -/
theorem exp_le_tiny (a : ℝ) (ha : a ≤ -768) : Real.exp a ≤ 1 / (2 : ℝ) ^ 1100 := by
  have hl := log_two_fine
  have h1 : a ≤ -(((1100 : Nat) : ℝ) * Real.log 2) := by push_cast; linarith
  have h2 := Real.exp_le_exp.mpr h1
  rw [Real.exp_neg, RealExpError.exp_pow_two] at h2
  simpa only [one_div] using h2

theorem far_quotient_pos (xv : ℝ) (k q : Int) (j : Fin 128) (hk : k = 128 * q + j.val)
    (hid : |xv - k * (Real.log 2 / 128)| ≤ 1 / 320) (hxpos : 768 ≤ xv) : 1107 ≤ q := by
  by_contra hn
  push Not at hn
  have hkI : k ≤ 141695 := by have := j.isLt; omega
  have hkR : (k : ℝ) ≤ 141695 := by exact_mod_cast hkI
  have hl := log_two_fine
  have hl0 := ExpReductionBounds.log_two_coarse_bounds.1
  have h1 := (abs_le.mp hid).2
  have hm1 : (k : ℝ) * Real.log 2 ≤ 141695 * Real.log 2 :=
    mul_le_mul_of_nonneg_right hkR (by linarith)
  have hm2 : (141695 : ℝ) * Real.log 2 ≤ 141695 * (6932 / 10000) :=
    mul_le_mul_of_nonneg_left hl (by norm_num)
  have he : (k : ℝ) * (Real.log 2 / 128) = (k * Real.log 2) / 128 := by ring
  rw [he] at h1
  linarith

theorem far_quotient_neg (xv : ℝ) (k q : Int) (j : Fin 128) (hk : k = 128 * q + j.val)
    (hid : |xv - k * (Real.log 2 / 128)| ≤ 1 / 320) (hxneg : xv ≤ -768) : q ≤ -1108 := by
  by_contra hn
  push Not at hn
  have hkI : -141696 ≤ k := by have := j.isLt; omega
  have hkR : (-141696 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkI
  have hl := log_two_fine
  have hl0 := ExpReductionBounds.log_two_coarse_bounds.1
  have h1 := (abs_le.mp hid).1
  have hm1 : (-141696 : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hkR (by linarith)
  have hm2 : (141696 : ℝ) * Real.log 2 ≤ 141696 * (6932 / 10000) :=
    mul_le_mul_of_nonneg_left hl (by norm_num)
  have he : (k : ℝ) * (Real.log 2 / 128) = (k * Real.log 2) / 128 := by ring
  rw [he] at h1
  linarith

theorem quotient_bounds_far (k q : Int) (j : Fin 128) (hk : k = 128 * q + j.val)
    (hkn : k.natAbs ≤ 196609) : -1537 ≤ q ∧ q ≤ 1536 := by
  have h : (k.natAbs : Int) ≤ 196609 := by exact_mod_cast hkn
  rw [← Int.abs_eq_natAbs] at h
  have hb := abs_le.mp h
  have hjb := j.isLt
  omega

/-- For finite `768 ≤ a < 1024`, `Exp.exp` gives positive infinity, and `exp a` reaches the
overflow threshold. -/
theorem far_positive (x : Float) (hxf : Finite x.toBits) (hxhi : |value x.toBits| < 1024)
    (hxpos : 768 ≤ value x.toBits) :
    (Exp.exp x).toBits = F64PositiveRounding.positiveInfinity ∧
      F64PositiveRounding.overflowThreshold ≤ Real.exp (value x.toBits) := by
  refine ⟨?_, exp_ge_overflow _ hxpos⟩
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hx : |value x.toBits| ≤ 1024 := hxhi.le
  have hxlo : 512 ≤ |value x.toBits| := by rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨k, q, j, hkf, hkv, hk, ht, hki, hj, hkn, hke⟩ := far_state x.toBits hxf hx
  have hid := ExpReductionBounds.ideal_residual_bound (value x.toBits) k hx hke
  have hq := far_quotient_pos _ k q j hk hid hxpos
  have hqb := quotient_bounds_far k q j hk hkn
  have hk0 : ¬ k < 0 := by have := j.isLt; omega
  have hguard : ExpCoreState.shiftedBits x.toBits &&& 0x80000000 = 0 := by
    simpa only [ite_eq_right hk0] using
      ExpSpecialScale.sign_guard _ k hki (hkn.trans (by norm_num))
  have hcore := ExpSpecialPositiveCore.core_positive_eq x
    (by rw [ExpCoreBounds.floatShifted_bits, hguard]; rfl)
  obtain ⟨hsf, hsv, hslo, hshi⟩ :=
    ExpSpecialScale.positive_scale_value _ k q j hki hk hj (by omega) (by omega)
  have htf : Finite (ExpCoreState.tailBits x.toBits) := by
    rw [ht]
    exact (ExpTableBounds.entry_bounds j).2.1
  rw [Exp.exp, ExpBranches.special_selected _ x (ExpBranches.special_exponent _ hxlo hxhi), hcore,
    F64Bits.toBits_mul, F64Bits.toBits_ofBits,
    ExpSpecialReconstruction.reconstruction_bits _ x hsf htf]
  simp only [show Wasm.IEEE64.isNaN 0x7F00000000000000 = false by decide, Bool.false_eq_true,
    ite_false]
  obtain ⟨hrf, hr⟩ := far_residual x.toBits hxf hx
  obtain ⟨_, htf', _, _, htb⟩ := ExpTableBounds.entry_bounds j
  have hrec := ExpReconstructionBounds.reconstruction_error _ (ExpResidualBounds.residual x.toBits)
    (ExpTableBounds.tailBits j.val) hsf hrf htf' hslo hshi hr htb
  have hdef : ExpSpecialReconstruction.reconstruction ExpSpecialScale.positiveScale x.toBits =
      ExpReconstructionBounds.reconstruction (ExpSpecialScale.positiveScale
        (ExpCoreState.shiftedBits x.toBits)) (ExpResidualBounds.residual x.toBits)
        (ExpTableBounds.tailBits j.val) := by
    simp only [ExpSpecialReconstruction.reconstruction, ht]
  rw [hdef]
  set y := ExpReconstructionBounds.reconstruction (ExpSpecialScale.positiveScale
    (ExpCoreState.shiftedBits x.toBits)) (ExpResidualBounds.residual x.toBits)
    (ExpTableBounds.tailBits j.val) with hy_def
  set S := value (ExpSpecialScale.positiveScale (ExpCoreState.shiftedBits x.toBits)) with hS_def
  -- the scale is at least 2 ^ 98
  obtain ⟨_, _, hH1, _, _⟩ := ExpTableBounds.entry_bounds j
  have hpow : (2 : ℝ) ^ (98 : Int) ≤ (2 : ℝ) ^ (q - 1009) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hS98 : (2 : ℝ) ^ (98 : Int) ≤ S := by
    rw [hsv]
    calc
      (2 : ℝ) ^ (98 : Int) = (2 : ℝ) ^ (98 : Int) * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ (q - 1009) * value (ExpTableBounds.headBits j.val) :=
        mul_le_mul hpow hH1 (by norm_num) (by positivity)
  -- the reconstruction is at least half the scale
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hS98
  have hrb := abs_le.mp hr
  have htbb := abs_le.mp htb
  have hexpr : 255 / 256 ≤ Real.exp (value (ExpResidualBounds.residual x.toBits)) := by
    have := Real.add_one_le_exp (value (ExpResidualBounds.residual x.toBits))
    linarith
  have hm1 : S * (1 - 1 / (2 : ℝ) ^ 53) ≤ S * (1 + value (ExpTableBounds.tailBits j.val)) :=
    mul_le_mul_of_nonneg_left (by linarith) hSpos.le
  have hm2 : S * (1 - 1 / (2 : ℝ) ^ 53) * (255 / 256) ≤
      S * (1 + value (ExpTableBounds.tailBits j.val)) *
        Real.exp (value (ExpResidualBounds.residual x.toBits)) :=
    mul_le_mul hm1 hexpr (by norm_num) (by nlinarith)
  have hyb := abs_le.mp hrec.2
  have hhalf : S / 2 ≤ value y := by
    rw [hu] at hyb
    linarith
  have h97 : (2 : ℝ) ^ (((1120 : Nat) : Int) - 1023) = (2 : ℝ) ^ (98 : Int) / 2 := by
    rw [show (((1120 : Nat) : Int) - 1023) = 98 - 1 by norm_num, zpow_sub₀ (by norm_num), zpow_one]
  have hy97 : (2 : ℝ) ^ (((1120 : Nat) : Int) - 1023) ≤ value y := by
    rw [h97]
    linarith
  have hey := exponent_ge_of_value y 1120 (by norm_num) hy97
  have hsmall : 1 / (2 : ℝ) ^ 1022 < (2 : ℝ) ^ (98 : Int) / 2 := by norm_num
  have hys := (normal_of_value y (by linarith)).2
  rw [ExpSpecialPositive.scale_up_word, F64PowerScale.mul_power_overflow 2032 y (by norm_num)
    (by norm_num) hrec.1 (by omega) (by omega) (by omega), hys, ExpSpecialPositive.infinity_word]

/-- For finite `-1024 < a ≤ -768`, `Exp.exp` is within one step of the nonnegative nearest-even
reference of `exp a`, which is zero. -/
theorem far_negative (x : Float) (hxf : Finite x.toBits) (hxhi : |value x.toBits| < 1024)
    (hxneg : value x.toBits ≤ -768) :
    (Exp.exp x).toBits.toNat ≤ limit ∧
      (Exp.exp x).toBits.toNat ≤
        (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat ≤
        (Exp.exp x).toBits.toNat + 1 := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hx : |value x.toBits| ≤ 1024 := hxhi.le
  have hxlo : 512 ≤ |value x.toBits| := by rw [abs_of_neg (by linarith)]; linarith
  obtain ⟨k, q, j, hkf, hkv, hk, ht, hki, hj, hkn, hke⟩ := far_state x.toBits hxf hx
  have hid := ExpReductionBounds.ideal_residual_bound (value x.toBits) k hx hke
  have hq := far_quotient_neg _ k q j hk hid hxneg
  have hqb := quotient_bounds_far k q j hk hkn
  have hkneg : k < 0 := by have := j.isLt; omega
  have hguard := ExpSpecialScale.sign_guard (ExpCoreState.shiftedBits x.toBits) k hki
    (hkn.trans (by norm_num))
  rw [ite_eq_left hkneg] at hguard
  have hg : ¬ ((ExpCoreBounds.floatShifted x).toBits &&& 0x80000000 == 0) = true := by
    rw [ExpCoreBounds.floatShifted_bits, hguard]
    decide
  obtain ⟨hsf, hsv, hslo, hshi⟩ :=
    ExpSpecialScale.negative_scale_value _ k q j hki hk hj (by omega) (by omega)
  have htf : Finite (ExpCoreState.tailBits x.toBits) := by
    rw [ht]
    exact (ExpTableBounds.entry_bounds j).2.1
  have hexp := ExpSpecialNegative.special_negative_bits x hxlo hxhi j hg hsf htf ht
  obtain ⟨hrf, hr⟩ := far_residual x.toBits hxf hx
  obtain ⟨_, htf', _, hH2, htb⟩ := ExpTableBounds.entry_bounds j
  obtain ⟨hpf, hPm, _⟩ := ExpReconstructionBounds.presum_error _
    (ExpResidualBounds.residual x.toBits) (ExpTableBounds.tailBits j.val) hsf hrf htf' hslo hshi
    hr htb
  generalize hs : ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x.toBits) = s at *
  generalize hp : Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation
    (ExpResidualBounds.residual x.toBits) (ExpTableBounds.tailBits j.val)) = p at *
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  have hS85 : value s ≤ 1 / (2 : ℝ) ^ 85 := by
    have hpow : (2 : ℝ) ^ (q + 1022) ≤ (2 : ℝ) ^ (-86 : Int) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h86 : (2 : ℝ) ^ (-86 : Int) * 2 = 1 / (2 : ℝ) ^ 85 := by norm_num
    rw [hsv, ← h86]
    exact mul_le_mul hpow hH2 (by linarith) (by positivity)
  have hPb := abs_le.mp hPm
  have hSPb : |value s + value p| < (2 : ℝ) ^ 1023 := by
    rw [abs_lt]
    have : (1 : ℝ) / 2 ^ 85 < 2 ^ 1023 := by norm_num
    constructor <;> linarith
  obtain ⟨hyf, hye⟩ := F64AddBounds.add_real_relative s p hsf hpf hSPb
  have hy1 : value (Wasm.IEEE64.add s p) < 1 := by
    have hb := abs_le.mp hye
    have hm : unitRoundoff64 * |value s + value p| ≤ 1 * |value s + value p| :=
      mul_le_mul_of_nonneg_right (by rw [hu]; norm_num) (abs_nonneg _)
    have h85 : (1 : ℝ) / 2 ^ 85 < 1 / 8 := by norm_num
    have hab : |value s + value p| ≤ 1 / 4 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  rw [ExpSpecialNegative.lt_one_iff _ hyf, decide_eq_true hy1, ite_eq_left rfl] at hexp
  have hE := Real.exp_pos (value x.toBits)
  have hEt := exp_le_tiny _ hxneg
  have hTE : (2 : ℝ) ^ (1022 : Int) * Real.exp (value x.toBits) ≤ 1 / (2 : ℝ) ^ 78 := by
    rw [ExpSpecialNegative.two_zpow_1022]
    calc
      _ ≤ (2 : ℝ) ^ 1022 * (1 / (2 : ℝ) ^ 1100) :=
        mul_le_mul_of_nonneg_left hEt (by positivity)
      _ = 1 / (2 : ℝ) ^ 78 := by
        rw [show (2 : ℝ) ^ 1100 = 2 ^ 1022 * 2 ^ 78 by rw [← pow_add]]
        field_simp
  have hTE0 : 0 ≤ (2 : ℝ) ^ (1022 : Int) * Real.exp (value x.toBits) := by positivity
  have hpre : |value s + value p - (2 : ℝ) ^ (1022 : Int) * Real.exp (value x.toBits)| ≤
      11 / 16 * unitRoundoff64 := by
    have h1 : (1 : ℝ) / 2 ^ 85 ≤ 1 / 2 ^ 78 := by norm_num
    have h2 : (1 : ℝ) / 2 ^ 78 ≤ 11 / 16 * (1 / 2 ^ 53) := by norm_num
    rw [hu, abs_le]
    constructor <;> linarith
  obtain ⟨hclim, hc1, hc2⟩ :=
    ExpSpecialNegative.compensated_one_step s p _ hsf hpf hS hshi hPm hy1 hE hpre
  rw [hexp]
  exact ⟨hclim.le, hc1, hc2⟩

#print axioms far_product
#print axioms far_state
#print axioms far_residual
#print axioms log_two_fine
#print axioms exp_ge_overflow
#print axioms exp_le_tiny
#print axioms far_quotient_pos
#print axioms far_quotient_neg
#print axioms quotient_bounds_far
#print axioms far_positive
#print axioms far_negative

end Verified.Examples.ExpFarRange
