import Verified.Examples.PowExpCore
import Verified.Examples.PowExpBranches
import Verified.Examples.Exp2Theorem

/-!
The paths of `Pow.powExp` with `signBias = 0` against `exp L` for a target `L` near `x + xtail`.
Below 512 the reconstruction is `ArmTight.ordinary_tight`.  From 512 to 768, `powSpecialCase`
scales the reconstruction up by `2 ^ 1009` or, for negative `x`, rounds it at the precision of
the subnormal range and scales it down by `2 ^ -1022`; on a positive scale its sequence is that
of `ExpSpecialNegative`.  From 768 to 1024 the coarse evaluation suffices: the scale exceeds
`2 ^ 98` and the result overflows, or the scale is below `2 ^ -85` and the result lies within
one step of 0, the reference of `exp L`.  Below `2 ^ -54` the result is `1 + x`.
-/

namespace Verified.Examples.PowExpPaths
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude ExpSpecialNegative

set_option exponentiation.threshold 4096

theorem ofBits_finite (w : UInt64) (hw : Finite w) : (Float.ofBits w).toBits = w := by
  rw [F64Bits.toBits_ofBits, not_nan_of_finite hw]
  rfl

theorem rho_bounds (a : ℝ) (ha : |a| ≤ 1 / 359) :
    319 / 320 ≤ Real.exp a ∧ Real.exp a ≤ 257 / 256 := by
  have h := Real.abs_exp_sub_one_sub_id_le (ha.trans (by norm_num))
  have h2 : a ^ 2 ≤ (1 / 359) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have h3 := abs_le.mp h
  have h4 := abs_le.mp ha
  have h5 := Real.add_one_le_exp a
  constructor <;> nlinarith

theorem upward_test : (1.0 + Float.ofBits 0x3C30000000000000 != (1.0 : Float)) = false := by
  rw [bne, F64Bits.beq_eq, F64Bits.toBits_add, F64Bits.toBits_ofBits, one_bits]
  decide +kernel

/-- `exp` reaches the overflow threshold from 710 on. -/
theorem exp_overflow (a : ℝ) (ha : 710 ≤ a) : (2 : ℝ) ^ 1024 ≤ Real.exp a := by
  have hl := ExpFarRange.log_two_fine
  have h1 : ((1024 : Nat) : ℝ) * Real.log 2 ≤ a := by push_cast; linarith
  rw [← RealExpError.exp_pow_two]
  exact Real.exp_le_exp.mpr h1

/-- `exp` is at most `2 ^ -1100` up to `-763`. -/
theorem exp_tiny (a : ℝ) (ha : a ≤ -763) : Real.exp a ≤ 1 / (2 : ℝ) ^ 1100 := by
  have hl := ExpFarRange.log_two_fine
  have h1 : a ≤ -(((1100 : Nat) : ℝ) * Real.log 2) := by push_cast; linarith
  have h2 := Real.exp_le_exp.mpr h1
  rw [Real.exp_neg, RealExpError.exp_pow_two] at h2
  simpa only [one_div] using h2

/-- `1 + x` for `|x| ≤ 2 ^ -54`, against `exp L` for `L` within `2 ^ -70` of `x`. -/
theorem tiny_within (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 1 / 2 ^ 54) (L : ℝ)
    (hL : |value x - L| ≤ 1 / 2 ^ 70) :
    F64SignedRounding.WithinSteps 1 (Real.exp L) (ExpTinyError.result x) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hone := ExpTinyError.one_value
  have honef : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  have hxb := abs_le.mp hx
  have hLb := abs_le.mp hL
  have hsum : |value 0x3FF0000000000000 + value x| < (2 : ℝ) ^ 1023 := by
    rw [hone, abs_lt]
    constructor <;> linarith [show (1 : ℝ) / 2 ^ 54 ≤ 1 by norm_num,
      show (2 : ℝ) < 2 ^ 1023 by norm_num]
  obtain ⟨hrf, hre⟩ := F64AddBounds.add_real_relative _ x honef hxf hsum
  rw [hone] at hre
  have hy : |L| ≤ 1 / 2 ^ 54 + 1 / 2 ^ 70 := by
    rw [abs_le]
    constructor <;> linarith
  have hb := Real.abs_exp_sub_one_sub_id_le (hy.trans (by norm_num))
  have hy2 : L ^ 2 ≤ (1 / 2 ^ 54 + 1 / 2 ^ 70) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hb' := abs_le.mp hb
  have hpos : 1 - (1 / 2 ^ 54 + 1 / 2 ^ 70) ≤ Real.exp L := by
    have := Real.add_one_le_exp L
    have := (abs_le.mp hy).1
    linarith
  have h1x : |1 + value x| ≤ 1 + 1 / 2 ^ 54 := by
    rw [abs_le]
    constructor <;> linarith [show (1 : ℝ) / 2 ^ 54 ≤ 1 by norm_num]
  have hre' : |value (Wasm.IEEE64.add 0x3FF0000000000000 x) - (1 + value x)| ≤
      1 / 2 ^ 53 * (1 + 1 / 2 ^ 54) := by
    rw [hu] at hre
    exact hre.trans (mul_le_mul_of_nonneg_left h1x (by positivity))
  have hre'' := abs_le.mp hre'
  apply F64RelativeStep.within_one_relative _ _ hrf
  · rw [abs_of_pos (Real.exp_pos _)]
    have : (1 : ℝ) / 2 ^ 1000 ≤ 1 - (1 / 2 ^ 54 + 1 / 2 ^ 70) := by norm_num
    linarith
  · rw [abs_of_pos (Real.exp_pos _), hu]
    have hnum : (1 : ℝ) / 2 ^ 53 * (1 + 1 / 2 ^ 54) + 1 / 2 ^ 70 +
        (1 / 2 ^ 54 + 1 / 2 ^ 70) ^ 2 ≤
        11 / 8 * (1 / 2 ^ 53) * (1 - (1 / 2 ^ 54 + 1 / 2 ^ 70)) := by norm_num
    have hmono : 11 / 8 * (1 / 2 ^ 53) * (1 - (1 / 2 ^ 54 + 1 / 2 ^ 70)) ≤
        11 / 8 * (1 / 2 ^ 53) * Real.exp L :=
      mul_le_mul_of_nonneg_left hpos (by positivity)
    rw [abs_le]
    constructor <;> linarith

/-- The ordinary path, `|x| < 512`. -/
theorem ordinary_within (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits)
    (htf : Finite xtail.toBits) (hx : |value x.toBits| < 512) (ht : |value xtail.toBits| ≤ 1 / 2 ^ 14)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ 1 / 2 ^ 55) :
    F64SignedRounding.WithinSteps 1 (Real.exp L)
      (Pow.powExpCore Exp.expTable x xtail 0 false).toBits := by
  obtain ⟨k, q, j, _, hk, hki, hj, _, hke, hRt, htmf, htmb, htme⟩ :=
    PowExpCore.core_state x xtail L hxf htf (hx.le.trans (by norm_num)) ht hL
  have hinv := ExpReductionBounds.inverse_upper_bound
  have hinv0 := ExpReductionBounds.inverse_bounds.1
  have hkb : |(k : ℝ)| ≤ 98305 := by
    have h1 := abs_le.mp hke
    have h2 := abs_lt.mp hx
    have h3 : |value 0x40671547652B82FE * value x.toBits| ≤ 192 * 512 := by
      rw [abs_mul, abs_of_pos hinv0]
      exact mul_le_mul hinv hx.le (abs_nonneg _) (by norm_num)
    have h4 := abs_le.mp h3
    rw [abs_le]
    constructor <;> linarith
  have hkI : |k| ≤ 98305 := by exact_mod_cast hkb
  have hkb' := abs_le.mp hkI
  have hjb := j.isLt
  have hqlo : -1000 ≤ q := by omega
  have hqhi : q ≤ 999 := by omega
  have hscale := ExpScaleBits.scale_bits_encoding _ k q j hki hk hj hqlo hqhi
  obtain ⟨hsf, hsv, _, _⟩ := ExpScaleEncoding.encoded_scale_value j q hqlo hqhi
  rw [← hscale] at hsf hsv
  rw [PowExpCore.core_eq]
  simp only [Bool.false_eq_true, ite_false]
  have hsw : PowExpCore.scaleWord x = ExpScaleBits.scaleBits (ExpCoreState.shiftedBits x.toBits) := by
    rw [PowExpCore.scaleWord, ExpCoreBounds.floatShifted_bits]
  rw [F64Bits.toBits_add, F64Bits.toBits_mul, hsw, ofBits_finite _ hsf]
  obtain ⟨hρl, hρu⟩ := rho_bounds _ hRt
  have h := ArmTight.ordinary_tight _ _ q j _ hsf htmf hsv hqlo hqhi htmb htme hρl hρu
  rwa [PowExpCore.target_eq L k q j hk] at h

/-- Bits of `powSpecialCase` for a positive key: the sum scaled up by `2 ^ 1009`. -/
theorem positive_bits (tmp : Float) (sbits ki : UInt64) (hg : (ki &&& 0x80000000 == 0) = true)
    (hsf : Finite (sbits - ((1009 : UInt64) <<< (52 : UInt64)))) :
    (Pow.powSpecialCase tmp sbits ki).toBits =
      Wasm.IEEE64.mul
        (Wasm.IEEE64.add (sbits - ((1009 : UInt64) <<< (52 : UInt64)))
          (Wasm.IEEE64.mul (sbits - ((1009 : UInt64) <<< (52 : UInt64))) tmp.toBits))
        0x7F00000000000000 := by
  unfold Pow.powSpecialCase
  rw [ite_eq_left hg]
  simp only [upward_test, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [F64Bits.toBits_mul, F64Bits.toBits_add, F64Bits.toBits_mul, ofBits_finite _ hsf,
    ofBits_finite 0x7F00000000000000 (by unfold CodeLib.IEEE64.Finite; decide)]

theorem abs_of_sign (y : UInt64) (hs : Wasm.IEEE64.sign y = false) : Wasm.IEEE64.abs y = y := by
  apply UInt64.toNat_inj.mp
  have hs' : y.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hy := y.toNat_lt
  have hlt : y.toNat / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 + y.toNat % 2 ^ 52 < 2 ^ 64 := by omega
  simp only [Wasm.IEEE64.abs, Wasm.IEEE64.encodeFinite, Wasm.IEEE64.exponent,
    Wasm.IEEE64.fraction, Bool.false_eq_true, ite_false, zero_add]
  rw [UInt64.toNat_ofNat_of_lt' hlt]
  omega

theorem sign_of_pos (y : UInt64) (hy : 0 < value y) : Wasm.IEEE64.sign y = false := by
  cases hs : Wasm.IEEE64.sign y
  · rfl
  · exfalso
    have : value y ≤ 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast]
      have : (0 : ℝ) ≤ (Wasm.IEEE64.scaledMagnitude y : ℝ) / 2 ^ 1074 := by positivity
      rw [neg_div]
      linarith
    linarith

theorem mask_zero (w : UInt64) (hs : Wasm.IEEE64.sign w = false) :
    w &&& 0x8000000000000000 = 0 := by
  apply UInt64.toNat_inj.mp
  simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
  rw [UInt64.toNat_and, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 by rfl,
    show (0 : UInt64).toNat = 0 by rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : i = 63
  · subst hi
    rw [Nat.testBit_lt_two_pow hs]
    rfl
  · simp [Ne.symm hi]

theorem lt_zero_false (y : UInt64) (hyf : Finite y) (hy : 0 < value y) :
    Wasm.IEEE64.lt y 0 = false := by
  unfold Wasm.IEEE64.lt
  rw [not_nan_of_finite hyf, show Wasm.IEEE64.isNaN 0 = false by decide]
  simp only [Bool.or_false, Bool.false_eq_true, ite_false, decide_eq_false_iff_not, not_lt]
  have hs := sign_of_pos y hy
  simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
    show Wasm.IEEE64.scaledMagnitude 0 = 0 by decide]
  positivity

/-- `powSpecialCase` for a negative key and a positive scale whose sum is positive is the
`negativeResult` of `ExpSpecialNegative`. -/
theorem negative_eq (tmp : Float) (sbits ki : UInt64) (hg : ¬ (ki &&& 0x80000000 == 0) = true)
    (hsf : Finite (sbits + ((1022 : UInt64) <<< (52 : UInt64))))
    (hss : Wasm.IEEE64.sign (sbits + ((1022 : UInt64) <<< (52 : UInt64))) = false)
    (hyf : Finite (Wasm.IEEE64.add (sbits + ((1022 : UInt64) <<< (52 : UInt64)))
      (Wasm.IEEE64.mul (sbits + ((1022 : UInt64) <<< (52 : UInt64))) tmp.toBits)))
    (hy : 0 < value (Wasm.IEEE64.add (sbits + ((1022 : UInt64) <<< (52 : UInt64)))
      (Wasm.IEEE64.mul (sbits + ((1022 : UInt64) <<< (52 : UInt64))) tmp.toBits))) :
    Pow.powSpecialCase tmp sbits ki =
      negativeResult (Float.ofBits (sbits + ((1022 : UInt64) <<< (52 : UInt64)))) tmp := by
  unfold Pow.powSpecialCase
  rw [ite_eq_right hg]
  generalize hS : sbits + ((1022 : UInt64) <<< (52 : UInt64)) = s at *
  have hSb : (Float.ofBits s).toBits = s := ofBits_finite s hsf
  have hYb : (Float.ofBits s + Float.ofBits s * tmp).toBits =
      Wasm.IEEE64.add s (Wasm.IEEE64.mul s tmp.toBits) := by
    rw [F64Bits.toBits_add, F64Bits.toBits_mul, hSb]
  rw [← hYb] at hyf hy
  have hYs := sign_of_pos _ hy
  have hneg : ¬ (Float.ofBits s + Float.ofBits s * tmp) < 0.0 := by
    rw [F64Bits.lt_iff, zero_bits, lt_zero_false _ hyf hy]
    simp
  have habs : (Float.ofBits s + Float.ofBits s * tmp).abs < 1.0 ↔
      (Float.ofBits s + Float.ofBits s * tmp) < 1.0 := by
    rw [F64Bits.lt_iff, F64Bits.lt_iff, F64Bits.toBits_abs, abs_of_sign _ hYs]
  have hzero : Float.ofBits (s &&& 0x8000000000000000) = 0.0 := by
    rw [mask_zero s hss, ← zero_bits, F64Bits.ofBits_toBits]
  simp only [negativeResult, compensated, ite_eq_right hneg, hzero]
  apply congrArg (HMul.hMul (Float.ofBits 0x0010000000000000))
  by_cases h : Float.ofBits s + Float.ofBits s * tmp < 1.0
  · rw [ite_eq_left (habs.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (habs.mp h')), ite_eq_right h]

/-- Bits of `powSpecialCase` for a negative key and a positive scale whose sum is positive. -/
theorem negative_bits (tmp : Float) (sbits ki : UInt64) (hg : ¬ (ki &&& 0x80000000 == 0) = true)
    (hsf : Finite (sbits + ((1022 : UInt64) <<< (52 : UInt64))))
    (hss : Wasm.IEEE64.sign (sbits + ((1022 : UInt64) <<< (52 : UInt64))) = false)
    (hyf : Finite (Wasm.IEEE64.add (sbits + ((1022 : UInt64) <<< (52 : UInt64)))
      (Wasm.IEEE64.mul (sbits + ((1022 : UInt64) <<< (52 : UInt64))) tmp.toBits)))
    (hy : 0 < value (Wasm.IEEE64.add (sbits + ((1022 : UInt64) <<< (52 : UInt64)))
      (Wasm.IEEE64.mul (sbits + ((1022 : UInt64) <<< (52 : UInt64))) tmp.toBits))) :
    (Pow.powSpecialCase tmp sbits ki).toBits =
      Wasm.IEEE64.mul 0x0010000000000000
        (if Wasm.IEEE64.lt (Wasm.IEEE64.add (sbits + ((1022 : UInt64) <<< (52 : UInt64)))
            (Wasm.IEEE64.mul (sbits + ((1022 : UInt64) <<< (52 : UInt64))) tmp.toBits)) one then
          compRounded (compSum (sbits + ((1022 : UInt64) <<< (52 : UInt64)))
            (Wasm.IEEE64.mul (sbits + ((1022 : UInt64) <<< (52 : UInt64))) tmp.toBits))
        else Wasm.IEEE64.add (sbits + ((1022 : UInt64) <<< (52 : UInt64)))
          (Wasm.IEEE64.mul (sbits + ((1022 : UInt64) <<< (52 : UInt64))) tmp.toBits)) := by
  rw [negative_eq tmp sbits ki hg hsf hss hyf hy, negativeResult_bits, F64Bits.toBits_add,
    F64Bits.toBits_mul, ofBits_finite _ hsf]

#print axioms ofBits_finite
#print axioms rho_bounds
#print axioms upward_test
#print axioms exp_overflow
#print axioms exp_tiny
#print axioms tiny_within
#print axioms ordinary_within
#print axioms positive_bits
#print axioms abs_of_sign
#print axioms sign_of_pos
#print axioms mask_zero
#print axioms lt_zero_false
#print axioms negative_eq
#print axioms negative_bits

end Verified.Examples.PowExpPaths
