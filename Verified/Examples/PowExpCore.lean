import Verified.Examples.PowExpEval
import Verified.Examples.ArmTight
import Verified.Examples.ExpResidualFloat
import Verified.Examples.ExpEvaluationFloat
import Verified.Examples.ExpCoreBounds
import Verified.Examples.ExpFarRange
import Verified.Examples.Pow

/-!
`Pow.powExpCore` on `Exp.expTable` with `signBias = 0`: Arm's `exp_inline` for `x + xtail`.  The
key, the scale, and the reduction of `x` are those of `Exp.expCore`, and the residual is the
reduced `x` plus `xtail`.  For `|x| ≤ 768`, `|xtail| ≤ 2 ^ -14`, and a target `L` within `2 ^ -55`
of `x + xtail`, the ideal residual `L - k log 2 / 128` stays within `1/359`, and the evaluation
approximates `T + exp (L - k log 2 / 128) - 1` within `ArmTight.allowance`, so that the
reconstruction lemmas of `ArmTight` apply to `exp L = 2 ^ q exp (j log 2 / 128) ρ`.
-/

namespace Verified.Examples.PowExpCore
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- The residual of `Pow.powExpCore`: the reduction of `x` of `Exp.expCore`, plus `xtail`. -/
def floatResidual (x xtail : Float) : Float := ExpResidualBounds.floatResidual x + xtail

/-- The table tail selected by the key of `x`. -/
def tailFloat (x : Float) : Float :=
  Float.ofBits Exp.expTable[(ExpScaleBits.index (ExpCoreBounds.floatShifted x).toBits).toNat]!

/-- The polynomial evaluation of `Pow.powExpCore`. -/
def tmpFloat (x xtail : Float) : Float :=
  ExpEvaluationBounds.floatEvaluation (floatResidual x xtail) (tailFloat x)

/-- The scale bits for the key of `x`. -/
def scaleWord (x : Float) : UInt64 := ExpScaleBits.scaleBits (ExpCoreBounds.floatShifted x).toBits

theorem core_eq (x xtail : Float) (special : Bool) :
    Pow.powExpCore Exp.expTable x xtail 0 special =
      if special then
        Pow.powSpecialCase (tmpFloat x xtail) (scaleWord x) (ExpCoreBounds.floatShifted x).toBits
      else Float.ofBits (scaleWord x) + Float.ofBits (scaleWord x) * tmpFloat x xtail := by
  have h0 : ∀ ki : UInt64, ki + 0 = ki := fun ki => UInt64.add_zero ki
  cases special <;> simp only [Pow.powExpCore, h0, Bool.false_eq_true, ite_false, ite_true] <;> rfl

theorem residual_bits (x xtail : Float) :
    (floatResidual x xtail).toBits =
      Wasm.IEEE64.add (ExpResidualBounds.residual x.toBits) xtail.toBits := by
  rw [floatResidual, F64Bits.toBits_add, ExpResidualBounds.residual_bits]

theorem tmp_bits (x xtail : Float) (j : Fin 128)
    (hj : ((ExpCoreBounds.floatShifted x).toBits % 128).toNat = j.val) :
    (tmpFloat x xtail).toBits =
      ExpEvaluationBounds.evaluation
        (Wasm.IEEE64.add (ExpResidualBounds.residual x.toBits) xtail.toBits)
        (ExpTableBounds.tailBits j.val) := by
  have hidx := (ExpScaleBits.index_values _ j hj).1
  have htf := (ExpTableBounds.entry_bounds j).2.1
  have htail : (tailFloat x).toBits = ExpTableBounds.tailBits j.val := by
    simp only [tailFloat, F64Bits.toBits_ofBits, hidx]
    simp only [ExpTableBounds.tailBits] at htf ⊢
    simp only [not_nan_of_finite htf, Bool.false_eq_true, ite_false]
  rw [tmpFloat, ExpEvaluationBounds.evaluation_bits, residual_bits, htail]

/-- The ideal residual of the reduction for `|x| ≤ 768`, sharper than `1/320`. -/
theorem ideal_tight (x k : ℝ) (hx : |x| ≤ 768)
    (hk : |k - value 0x40671547652B82FE * x| ≤ 1 / 2 + 1 / (2 : ℝ) ^ 35) :
    |x - k * (Real.log 2 / 128)| ≤ 677 / 250000 := by
  set d := Real.log 2 / 128
  set inv := value 0x40671547652B82FE
  have hl := ExpReductionBounds.log_two_coarse_bounds
  have hd : 0 ≤ d := by
    simp only [d]
    linarith [hl.1]
  have hdu : |d| ≤ 6932 / 1280000 := by
    rw [abs_of_nonneg hd]
    simp only [d]
    linarith [ExpFarRange.log_two_fine]
  have hi : |1 - inv * d| ≤ 1 / (2 : ℝ) ^ 53 := by
    rw [abs_sub_comm]
    simpa only [d, inv, mul_div_assoc, mul_one] using ExpReductionBounds.inverse_bounds.2.2
  have hk' : |inv * x - k| ≤ 1 / 2 + 1 / (2 : ℝ) ^ 35 := by
    rw [abs_sub_comm]
    exact hk
  calc
    _ = |x * (1 - inv * d) + (inv * x - k) * d| := by
      congr 1
      ring
    _ ≤ |x * (1 - inv * d)| + |(inv * x - k) * d| := abs_add_le _ _
    _ = |x| * |1 - inv * d| + |inv * x - k| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ 768 * (1 / (2 : ℝ) ^ 53) + (1 / 2 + 1 / (2 : ℝ) ^ 35) * (6932 / 1280000) :=
      add_le_add (mul_le_mul hx hi (abs_nonneg _) (by norm_num))
        (mul_le_mul hk' hdu (abs_nonneg _) (by norm_num))
    _ ≤ 677 / 250000 := by norm_num

/-- `2 ^ q exp (j log 2 / 128) exp (L - k log 2 / 128) = exp L` for `k = 128 q + j`. -/
theorem target_eq (L : ℝ) (k q : Int) (j : Fin 128) (hk : k = 128 * q + j.val) :
    (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) *
      Real.exp (L - k * (Real.log 2 / 128)) = Real.exp L := by
  have h2 : (2 : ℝ) ^ q = Real.exp (q * Real.log 2) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [h2, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [hk]
  push_cast
  ring

/-- The state of `Pow.powExpCore` for `|x| ≤ 768` and a target `L` near `x + xtail`. -/
theorem core_state (x xtail : Float) (L : ℝ) (hxf : Finite x.toBits) (htf : Finite xtail.toBits)
    (hx : |value x.toBits| ≤ 768) (ht : |value xtail.toBits| ≤ 1 / 2 ^ 14)
    (hL : |value x.toBits + value xtail.toBits - L| ≤ 1 / 2 ^ 55) :
    ∃ (k q : Int) (j : Fin 128),
      value (ExpReductionSelection.integer x.toBits) = (k : ℝ) ∧ k = 128 * q + j.val ∧
      ((ExpCoreState.shiftedBits x.toBits).toNat : Int) = (0x4338000000000000 : Int) + k ∧
      ((ExpCoreState.shiftedBits x.toBits) % 128).toNat = j.val ∧ k.natAbs ≤ 147457 ∧
      |(k : ℝ) - value 0x40671547652B82FE * value x.toBits| ≤ 1 / 2 + 1 / (2 : ℝ) ^ 35 ∧
      |L - k * (Real.log 2 / 128)| ≤ 1 / 359 ∧
      Finite (tmpFloat x xtail).toBits ∧ |value (tmpFloat x xtail).toBits| ≤ 1 / 256 ∧
      |value (tmpFloat x xtail).toBits - (value (ExpTableBounds.tailBits j.val) +
        Real.exp (L - k * (Real.log 2 / 128)) - 1)| ≤ ArmTight.allowance := by
  obtain ⟨k, q, j, hkv, hk, _, hki, hj, hkn⟩ := ExpCoreState.prefix_state x.toBits hxf hx
  obtain ⟨k', _, hkv', _, hke⟩ := ExpReductionSelection.integer_selection x.toBits hxf hx
  have hkk : (k' : ℝ) = k := by
    rw [← hkv, value, hkv']
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    field_simp
  rw [hkk] at hke
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hu0 : 0 ≤ unitRoundoff64 := by rw [hu]; positivity
  have hid := ideal_tight (value x.toBits) k hx hke
  obtain ⟨hrf, _, hre⟩ := ExpResidualBounds.residual_bounds x.toBits hxf hx
  simp only [ExpResidualBounds.ideal, hkv] at hre
  set d := Real.log 2 / 128
  set res := ExpResidualBounds.residual x.toBits
  -- the residual with the tail
  have hsum : |value res + value xtail.toBits| ≤ 677 / 250000 + 1 / 2 ^ 60 + 1 / 2 ^ 14 := by
    have h1 := abs_le.mp hre
    have h2 := abs_le.mp hid
    have h3 := abs_le.mp ht
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hr'f, hr'e⟩ := F64AddBounds.add_real_relative res xtail.toBits hrf htf
    (hsum.trans_lt (by norm_num))
  set r' := Wasm.IEEE64.add res xtail.toBits
  have hr'e' : |value r' - (value res + value xtail.toBits)| ≤
      1 / 2 ^ 53 * (677 / 250000 + 1 / 2 ^ 60 + 1 / 2 ^ 14) := by
    rw [← hu]
    exact hr'e.trans (mul_le_mul_of_nonneg_left hsum hu0)
  have hr' : |value r'| ≤ 1 / 360 := by
    have h1 := abs_le.mp hr'e'
    have h2 := abs_le.mp hsum
    have hn : (677 / 250000 + 1 / 2 ^ 60 + 1 / 2 ^ 14 : ℝ) +
        1 / 2 ^ 53 * (677 / 250000 + 1 / 2 ^ 60 + 1 / 2 ^ 14) ≤ 1 / 360 := by norm_num
    rw [abs_le]
    constructor <;> linarith
  -- the computed residual against the ideal one
  set Rt := L - k * d with hRtdef
  have hδ : |value r' - Rt| ≤ 1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61 := by
    have h1 := abs_le.mp hr'e'
    have h2 := abs_le.mp hre
    have h3 := abs_le.mp hL
    have hn : 1 / 2 ^ 53 * (677 / 250000 + 1 / 2 ^ 60 + 1 / 2 ^ 14 : ℝ) ≤ 1 / 2 ^ 61 := by
      norm_num
    rw [hRtdef, abs_le]
    constructor <;> linarith
  have hRt : |Rt| ≤ 1 / 359 := by
    have h1 := abs_le.mp hδ
    have h2 := abs_le.mp hr'
    have hn : (1 : ℝ) / 360 + (1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61) ≤ 1 / 359 := by norm_num
    rw [abs_le]
    constructor <;> linarith
  -- the evaluation
  have hj' : ((ExpCoreBounds.floatShifted x).toBits % 128).toNat = j.val := by
    rw [ExpCoreBounds.floatShifted_bits]
    exact hj
  have htb := (ExpTableBounds.entry_bounds j).2.2.2.2
  have htf' := (ExpTableBounds.entry_bounds j).2.1
  have hev := PowExpEval.evaluation_tight r' _ hr'f htf' hr' htb
  have hexp := PowExpEval.evaluation_exp_tight r' _ hr'f htf' hr' htb
  have htmp : (tmpFloat x xtail).toBits = ExpEvaluationBounds.evaluation r'
      (ExpTableBounds.tailBits j.val) := tmp_bits x xtail j hj'
  rw [← htmp] at hev hexp
  -- `exp r'` against `exp Rt`
  have hERt : Real.exp Rt ≤ 1 + 1 / 359 + 1 / 359 ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (hRt.trans (by norm_num))
    have h2 : Rt ^ 2 ≤ (1 / 359) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hRt 2
    have h3 := (abs_le.mp h).2
    have h4 := (abs_le.mp hRt).2
    linarith
  have hρ : |Real.exp (value r') - Real.exp Rt| ≤
      (1 + 1 / 359 + 1 / 359 ^ 2) * ((1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61) +
        (1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61) ^ 2) := by
    have hid' : Real.exp (value r') - Real.exp Rt =
        Real.exp Rt * (Real.exp (value r' - Rt) - 1) := by
      rw [mul_sub, ← Real.exp_add, add_sub_cancel, mul_one]
    have hd := Real.abs_exp_sub_one_sub_id_le (hδ.trans (by norm_num))
    have hd2 : (value r' - Rt) ^ 2 ≤ (1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
    have hd' : |Real.exp (value r' - Rt) - 1| ≤ (1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61) +
        (1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61) ^ 2 := by
      have := abs_sub_abs_le_abs_sub (Real.exp (value r' - Rt) - 1) (value r' - Rt)
      linarith
    rw [hid', abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul hERt hd' (abs_nonneg _) (by norm_num)
  refine ⟨k, q, j, hkv, hk, hki, hj, hkn, hke, hRt, hev.1, hev.2.1, ?_⟩
  calc
    _ ≤ |value (tmpFloat x xtail).toBits -
          (value (ExpTableBounds.tailBits j.val) + Real.exp (value r') - 1)| +
        |Real.exp (value r') - Real.exp Rt| := by
      have := abs_sub_le (value (tmpFloat x xtail).toBits)
        (value (ExpTableBounds.tailBits j.val) + Real.exp (value r') - 1)
        (value (ExpTableBounds.tailBits j.val) + Real.exp Rt - 1)
      rw [show value (ExpTableBounds.tailBits j.val) + Real.exp (value r') - 1 -
        (value (ExpTableBounds.tailBits j.val) + Real.exp Rt - 1) =
        Real.exp (value r') - Real.exp Rt by ring] at this
      exact this
    _ ≤ 17 / 2 ^ 63 + (1 + 1 / 359 + 1 / 359 ^ 2) * ((1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61) +
        (1 / 2 ^ 55 + 1 / 2 ^ 60 + 1 / 2 ^ 61) ^ 2) := add_le_add hexp hρ
    _ ≤ ArmTight.allowance := by
      rw [ArmTight.allowance]
      norm_num

#print axioms core_eq
#print axioms residual_bits
#print axioms tmp_bits
#print axioms ideal_tight
#print axioms target_eq
#print axioms core_state

end Verified.Examples.PowExpCore
