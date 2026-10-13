import Verified.Examples.PowSubnormal

/-!
`Pow.pow` for a positive finite `x` and a finite `y`: the result lies within one step of the
nearest-even reference of `Real.rpow x y`.  A zero `y` gives 1.  A nonzero `|y| < 2 ^ -65` gives
1 for `x = 1` and `1 ± y` otherwise, within one step of `x ^ y = exp (y log x)` with
`|y log x| < 2 ^ -55`.  A finite `|y| ≥ 2 ^ 63` gives 1 for `x = 1` and otherwise the overflow
or underflow product, since `|y log x| ≥ 1024`.  Otherwise `powMain` runs on the word of `x`,
normalized for a subnormal `x`, and gives 1 for `x = 1`.
-/

namespace Verified.Examples.PowPositive
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- A word equal to its target lies within one step of it. -/
theorem exact_within (c : UInt64) (hcf : Finite c) (E : ℝ) (hE : value c = E)
    (hE1 : 1 / 2 ^ 1000 ≤ |E|) : F64SignedRounding.WithinSteps 1 E c := by
  apply F64RelativeStep.within_one_relative _ _ hcf hE1
  rw [hE, sub_self, abs_zero]
  have hu : (0 : ℝ) ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  exact mul_nonneg (mul_nonneg (by norm_num) hu) (abs_nonneg _)

theorem one_word_value : value 0x3FF0000000000000 = 1 := ExpTinyError.one_value

/-- `1 ± w` against `exp t` for `|w| ≤ 2 ^ -64` and `|t| ≤ 2 ^ -55`. -/
theorem near_one_within (w : UInt64) (hwf : Finite w) (hw : |value w| ≤ 1 / 2 ^ 64) (t : ℝ)
    (ht : |t| ≤ 1 / 2 ^ 55) :
    F64SignedRounding.WithinSteps 1 (Real.exp t) (Wasm.IEEE64.add 0x3FF0000000000000 w) ∧
      F64SignedRounding.WithinSteps 1 (Real.exp t) (Wasm.IEEE64.sub 0x3FF0000000000000 w) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have honef : Finite (0x3FF0000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  have hwb := abs_le.mp hw
  have htb := abs_le.mp ht
  have he := Real.abs_exp_sub_one_sub_id_le (ht.trans (by norm_num))
  have heb := abs_le.mp he
  have ht2 : t ^ 2 ≤ (1 / 2 ^ 55) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ht 2
  have hpos : 1 - 1 / 2 ^ 54 ≤ Real.exp t := by
    have := Real.add_one_le_exp t
    linarith [show (1 : ℝ) / 2 ^ 55 ≤ 1 / 2 ^ 54 by norm_num]
  constructor
  · obtain ⟨hcf, hce⟩ := F64AddBounds.add_real_relative _ w honef hwf (by
      rw [one_word_value]
      have := abs_add_le (1 : ℝ) (value w)
      rw [abs_one] at this
      linarith [show (1 : ℝ) + 1 / 2 ^ 64 < 2 ^ 1023 by norm_num])
    rw [one_word_value, hu] at hce
    have h1 : |1 + value w| ≤ 1 + 1 / 2 ^ 64 := by
      rw [abs_le]; constructor <;> linarith
    have hce' := abs_le.mp (hce.trans (mul_le_mul_of_nonneg_left h1 (by positivity)))
    apply F64RelativeStep.within_one_relative _ _ hcf
    · rw [abs_of_pos (Real.exp_pos _)]
      linarith [show (1 : ℝ) / 2 ^ 1000 ≤ 1 - 1 / 2 ^ 54 by norm_num]
    · rw [abs_of_pos (Real.exp_pos _), hu]
      have hm : 11 / 8 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 54) ≤ 11 / 8 * (1 / (2 : ℝ) ^ 53) * Real.exp t :=
        mul_le_mul_of_nonneg_left hpos (by positivity)
      have hn : (1 : ℝ) / 2 ^ 53 * (1 + 1 / 2 ^ 64) + 1 / 2 ^ 64 + 1 / 2 ^ 55 + (1 / 2 ^ 55) ^ 2 ≤
          11 / 8 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 54) := by norm_num
      rw [abs_le]
      constructor <;> linarith
  · obtain ⟨hcf, hce⟩ := F64AddBounds.sub_real_relative _ w honef hwf (by
      rw [one_word_value]
      have := abs_sub (1 : ℝ) (value w)
      rw [abs_one] at this
      linarith [show (1 : ℝ) + 1 / 2 ^ 64 < 2 ^ 1023 by norm_num])
    rw [one_word_value, hu] at hce
    have h1 : |1 - value w| ≤ 1 + 1 / 2 ^ 64 := by
      rw [abs_le]; constructor <;> linarith
    have hce' := abs_le.mp (hce.trans (mul_le_mul_of_nonneg_left h1 (by positivity)))
    apply F64RelativeStep.within_one_relative _ _ hcf
    · rw [abs_of_pos (Real.exp_pos _)]
      linarith [show (1 : ℝ) / 2 ^ 1000 ≤ 1 - 1 / 2 ^ 54 by norm_num]
    · rw [abs_of_pos (Real.exp_pos _), hu]
      have hm : 11 / 8 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 54) ≤ 11 / 8 * (1 / (2 : ℝ) ^ 53) * Real.exp t :=
        mul_le_mul_of_nonneg_left hpos (by positivity)
      have hn : (1 : ℝ) / 2 ^ 53 * (1 + 1 / 2 ^ 64) + 1 / 2 ^ 64 + 1 / 2 ^ 55 + (1 / 2 ^ 55) ^ 2 ≤
          11 / 8 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 54) := by norm_num
      rw [abs_le]
      constructor <;> linarith

theorem xor_high (w : UInt64) :
    (w ^^^ 0x0008000000000000).toNat / 2 ^ 52 = w.toNat / 2 ^ 52 := by
  rw [UInt64.toNat_xor, show (0x0008000000000000 : UInt64).toNat = 2 ^ 51 by rfl]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
  simp

/-- A finite `x` is not a signaling NaN. -/
theorem not_signaling (x : Float) (hxf : Wasm.IEEE64.exponent x.toBits < 2047) :
    Pow.issignaling x = false := by
  have h := xor_high x.toBits
  have hT := (x.toBits ^^^ 0x0008000000000000).toNat_lt
  have he : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 < 2047 := hxf
  simp only [Pow.issignaling, decide_eq_false_iff_not, gt_iff_lt]
  intro hlt
  have hn := UInt64.lt_iff_toNat_lt.mp hlt
  simp only [UInt64.toNat_mul, UInt64.reduceToNat] at hn
  simp only [Nat.reducePow] at h hT he hn
  omega

theorem y_zero (x y : Float) (hxf : Wasm.IEEE64.exponent x.toBits < 2047)
    (hy0 : 2 * y.toBits = 0) : (Pow.pow x y).toBits = 0x3FF0000000000000 := by
  have hy : y.toBits.toNat = 0 ∨ y.toBits.toNat = 2 ^ 63 := by
    have := congrArg UInt64.toNat hy0
    simp only [UInt64.toNat_mul, UInt64.reduceToNat] at this
    have := y.toBits.toNat_lt
    simp only [Nat.reducePow] at this ⊢
    omega
  have hcond : ((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be := by
    have hw := ExpBranches.exponent_word_spec y.toBits
    simp only [ExpBranches.exponentWord] at hw
    have he : Wasm.IEEE64.exponent y.toBits = 0 := by
      show y.toBits.toNat / 2 ^ 52 % 2 ^ 11 = 0
      rcases hy with h | h <;> simp only [h, Nat.reducePow, Nat.reduceDiv, Nat.reduceMod]
    have hs : (((y.toBits >>> 52) &&& 0x7ff) - 0x3be).toNat =
        (2 ^ 64 - 958 + Wasm.IEEE64.exponent y.toBits) % 2 ^ 64 := by
      rw [UInt64.toNat_sub, hw]
      rfl
    apply UInt64.le_iff_toNat_le.mpr
    rw [hs, he]
    decide
  have hc : (decide ((x.toBits >>> 52) - 1 ≥ (0x7ff : UInt64) - 1) ||
      decide (((y.toBits >>> 52) &&& 0x7ff) - 0x3be ≥ (0x43e : UInt64) - 0x3be)) = true := by
    simp only [hcond, decide_true, Bool.or_true]
  simp only [Pow.pow, Pow.powWith, hc, ite_true, PowBranches.zeroinfnan_zero _ hy0, hy0,
    beq_self_eq_true, not_signaling x hxf, Bool.false_eq_true, ite_false]
  rfl

/-- `powMain` for `x = 1` gives exactly 1. -/
theorem main_one (y : Float) (hyf : Wasm.IEEE64.exponent y.toBits < 2047)
    (hey : 1 ≤ Wasm.IEEE64.exponent y.toBits) :
    (Pow.powMain Pow.powLogTable Exp.expTable 0x3FF0000000000000 y y.toBits 0).toBits =
      0x3FF0000000000000 := by
  obtain ⟨h1, -⟩ := PowMainPath.log_one
  simp only [Pow.powMain]
  generalize hP : Pow.powLog Pow.powLogTable 0x3FF0000000000000 = P at h1
  obtain ⟨a, b⟩ := P
  simp only at h1 ⊢
  have hyf' : Finite y.toBits := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
    omega
  obtain ⟨hmf, -, -, -, -⟩ := PowProduct.mask_state y.toBits hyf' hey
  set ehi := Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000) * Float.ofBits (a.toBits &&& 0xFFFFFFFFF8000000)
  have hehi : ehi.toBits = 0 ∨ ehi.toBits = 0x8000000000000000 := by
    have hz : (Float.ofBits (a.toBits &&& 0xFFFFFFFFF8000000)).toBits = 0 := by
      rw [h1, F64Bits.toBits_ofBits]
      decide
    have hm : (Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000)).toBits = PowProduct.mask y.toBits :=
      PowExpPaths.ofBits_finite _ hmf
    simp only [ehi, F64Bits.toBits_mul, hz, hm]
    simp only [Wasm.IEEE64.mul, not_nan_of_finite hmf, not_infinite_of_finite hmf,
      show Wasm.IEEE64.isNaN 0 = false by decide, show Wasm.IEEE64.isInfinite 0 = false by decide,
      show Wasm.IEEE64.scaledMagnitude 0 = 0 by decide, Bool.or_false, Bool.false_eq_true,
      ite_false, beq_self_eq_true, Bool.or_true, ite_true]
    cases Wasm.IEEE64.sign (PowProduct.mask y.toBits) <;> decide
  have hexp : Wasm.IEEE64.exponent ehi.toBits < 969 := by
    rcases hehi with h | h <;> rw [h] <;> decide
  rw [PowExpBranches.tiny_selected _ ehi _ hexp, ExpTinyError.float_result_bits]
  rcases hehi with h | h <;> rw [h] <;> decide +kernel

#print axioms main_one
#print axioms xor_high
#print axioms not_signaling
#print axioms y_zero
#print axioms exact_within
#print axioms near_one_within

end Verified.Examples.PowPositive
