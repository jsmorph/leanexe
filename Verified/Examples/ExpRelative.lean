import Verified.Examples.ExpBranches
import Verified.Examples.ExpCoreRange
import Verified.Examples.ExpSpecialNegative

/-!
The relative error of `Exp.expWith` with `Exp.expTable` below 512 in magnitude: at most
`1.405 · 2^-53` of `exp x`.  Below `2^-54` the code returns `1 + x`, one rounding from a number
within `x²` of `exp x`.  Otherwise `ExpCoreBounds.expCore_error` bounds the error by
`(7/5) · 2^-53` times the scale `2^q H_j`, and the scale is at most `1.0032 exp x`, since `H_j (1 + t_j)`
encloses `2^(j/128)` within `2^-100`, `|t_j| ≤ 2^-53`, and the residual factor `exp r` of `exp x` is at
least `319/320`.
-/

namespace Verified.Examples.ExpRelative
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- The scale of the reconstruction is at most `1.0032 exp x`. -/
theorem scale_le (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 512) :
    value (ExpCoreState.scaleBits x) ≤ (10032 / 10000) * Real.exp (value x) := by
  obtain ⟨k, q, j, hkv, hk, _, _, hs, _, _⟩ := ExpCoreState.reduction_state x hxf hx
  have hf := ExpCoreRange.target_factor x k q j hkv hk
  have hr := ExpCoreRange.ideal_exponential_range x hxf (hx.trans (by norm_num))
  have he := ExpTableBounds.scale_enclosure j
  obtain ⟨_, _, hH1, _, ht⟩ := ExpTableBounds.entry_bounds j
  have hQ : (0 : ℝ) < (2 : ℝ) ^ q := zpow_pos (by norm_num) q
  set H := value (ExpTableBounds.headBits j.val)
  set t := value (ExpTableBounds.tailBits j.val)
  set E := Real.exp ((j.val : ℝ) * Real.log 2 / 128)
  have hscale : ExpTableBounds.scale j.val = H * (1 + t) := rfl
  have htb := abs_le.mp ht
  have hHE : H * (1 - 1 / 2 ^ 53) * (1 - 1 / 2 ^ 100) ≤ E := by
    have h1 : H * (1 - 1 / 2 ^ 53) ≤ H * (1 + t) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith [htb.1]
    have h2 := he.1
    rw [hscale] at h2
    have h3 : H * (1 - 1 / 2 ^ 53) * (1 - 1 / 2 ^ 100) ≤ H * (1 + t) * (1 - 1 / 2 ^ 100) :=
      mul_le_mul_of_nonneg_right h1 (by norm_num)
    linarith
  rw [hs, hf]
  have hEpos : 0 < E := Real.exp_pos _
  have hrpos := hr.1
  have hc : H ≤ (10032 / 10000) * (E * (319 / 320)) := by
    have hk : (1 : ℝ) ≤ (10032 / 10000) * (319 / 320) * ((1 - 1 / 2 ^ 53) * (1 - 1 / 2 ^ 100)) := by
      norm_num
    nlinarith
  calc (2 : ℝ) ^ q * H ≤ (2 : ℝ) ^ q * ((10032 / 10000) * (E * (319 / 320))) :=
        mul_le_mul_of_nonneg_left hc hQ.le
    _ ≤ (2 : ℝ) ^ q * ((10032 / 10000) * (E * Real.exp (ExpResidualBounds.ideal x))) := by
        gcongr
    _ = (10032 / 10000) * ((2 : ℝ) ^ q * E * Real.exp (ExpResidualBounds.ideal x)) := by ring

/-- `Exp.expWith Exp.expTable` errs by at most `1.405 · 2^-53` relative to `exp x` for `|x| < 512`. -/
theorem expWith_relative (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| < 512) :
    Finite (Exp.expWith Exp.expTable x).toBits ∧
      |value (Exp.expWith Exp.expTable x).toBits - Real.exp (value x.toBits)| ≤
        (1405 / 1000) * unitRoundoff64 * Real.exp (value x.toBits) := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have he : Wasm.IEEE64.exponent x.toBits < 1032 :=
    F64ExponentBounds.exponent_lt_of_magnitude_lt x.toBits 1032 (by decide) (by
      rw [ExpBranches.small_boundary, abs_of_pos (by norm_num : (0 : ℝ) < 512)]
      exact hx)
  by_cases ht : Wasm.IEEE64.exponent x.toBits < 969
  · -- `1 + x` below `2^-54`
    have hxt : |value x.toBits| ≤ 1 / (2 : ℝ) ^ 54 := by
      have h := F64ExponentBounds.magnitude_le_boundary x.toBits 969 (by decide) ht
      rw [ExpBranches.tiny_boundary, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 54)] at h
      exact h
    rw [ExpBranches.tiny_selected Exp.expTable x ht, F64Bits.toBits_add]
    have hone : (1.0 : Float).toBits = ExpSpecialNegative.one := rfl
    rw [hone]
    have hof := ExpSpecialNegative.one_finite
    have hov := ExpSpecialNegative.one_value
    obtain ⟨hf, herr⟩ := F64AddBounds.add_real_relative _ _ hof hxf (by
      rw [hov]
      calc |1 + value x.toBits| ≤ 1 + |value x.toBits| := by
            simpa using abs_add_le 1 (value x.toBits)
        _ < (2 : ℝ) ^ 1023 := by
            have : (1 : ℝ) / 2 ^ 54 < 1 := by norm_num
            have h2 : (2 : ℝ) ≤ 2 ^ 1023 := by norm_num
            linarith)
    rw [hov] at herr
    refine ⟨hf, ?_⟩
    have hb := abs_le.mp hxt
    have hex := Real.abs_exp_sub_one_sub_id_le (x := value x.toBits) (by
      linarith [show (1 : ℝ) / 2 ^ 54 ≤ 1 by norm_num])
    have hsq : value x.toBits ^ 2 ≤ (1 / (2 : ℝ) ^ 54) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hxt 2
    have hexp_lo : 1 - 1 / (2 : ℝ) ^ 53 ≤ Real.exp (value x.toBits) := by
      have := Real.add_one_le_exp (value x.toBits)
      have : (1 : ℝ) / 2 ^ 54 ≤ 1 / 2 ^ 53 := by norm_num
      linarith
    have h1 : |1 + value x.toBits| ≤ 1 + 1 / (2 : ℝ) ^ 54 := by
      calc |1 + value x.toBits| ≤ 1 + |value x.toBits| := by
            simpa using abs_add_le 1 (value x.toBits)
        _ ≤ 1 + 1 / 2 ^ 54 := by linarith
    have herr' : |value (Wasm.IEEE64.add ExpSpecialNegative.one x.toBits) - (1 + value x.toBits)| ≤
        (1 / (2 : ℝ) ^ 53) * (1 + 1 / 2 ^ 54) := by
      rw [hu] at herr
      exact herr.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    calc |value (Wasm.IEEE64.add ExpSpecialNegative.one x.toBits) - Real.exp (value x.toBits)|
        ≤ |value (Wasm.IEEE64.add ExpSpecialNegative.one x.toBits) - (1 + value x.toBits)| +
          |Real.exp (value x.toBits) - 1 - value x.toBits| := by
          have := abs_sub_le (value (Wasm.IEEE64.add ExpSpecialNegative.one x.toBits))
            (1 + value x.toBits) (Real.exp (value x.toBits))
          rw [abs_sub_comm (1 + value x.toBits), show Real.exp (value x.toBits) -
            (1 + value x.toBits) = Real.exp (value x.toBits) - 1 - value x.toBits by ring] at this
          exact this
      _ ≤ (1 / (2 : ℝ) ^ 53) * (1 + 1 / 2 ^ 54) + (1 / (2 : ℝ) ^ 54) ^ 2 :=
          add_le_add herr' (hex.trans hsq)
      _ ≤ (1405 / 1000) * unitRoundoff64 * Real.exp (value x.toBits) := by
          rw [hu]
          have : (1405 / 1000) * (1 / (2 : ℝ) ^ 53) * (1 - 1 / 2 ^ 53) ≤
              (1405 / 1000) * (1 / (2 : ℝ) ^ 53) * Real.exp (value x.toBits) :=
            mul_le_mul_of_nonneg_left hexp_lo (by positivity)
          have h2 : (1 / (2 : ℝ) ^ 53) * (1 + 1 / 2 ^ 54) + (1 / (2 : ℝ) ^ 54) ^ 2 ≤
              (1405 / 1000) * (1 / (2 : ℝ) ^ 53) * (1 - 1 / 2 ^ 53) := by norm_num
          linarith
  · have hlo : 969 ≤ Wasm.IEEE64.exponent x.toBits := by omega
    rw [ExpBranches.ordinary_selected Exp.expTable x hlo he]
    obtain ⟨hf, herr⟩ := ExpCoreBounds.expCore_error x hxf hx.le
    refine ⟨hf, herr.trans ?_⟩
    have hs := scale_le x.toBits hxf hx.le
    have hu0 : (0 : ℝ) ≤ unitRoundoff64 := by rw [hu]; positivity
    calc (7 / 5) * unitRoundoff64 * value (ExpCoreState.scaleBits x.toBits)
        ≤ (7 / 5) * unitRoundoff64 * ((10032 / 10000) * Real.exp (value x.toBits)) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (1405 / 1000) * unitRoundoff64 * Real.exp (value x.toBits) := by
          have := Real.exp_pos (value x.toBits)
          nlinarith

#print axioms scale_le
#print axioms expWith_relative

end Verified.Examples.ExpRelative
