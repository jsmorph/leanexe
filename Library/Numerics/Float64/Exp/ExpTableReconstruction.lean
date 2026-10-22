import Library.Numerics.Float64.Exp.ExpReducedReconstruction
import Library.Numerics.Float64.Exp.ExpTableBounds
import LeanExe.ProofKit.RealExpError

namespace Library.Numerics.Float64.Exp.ExpTableReconstruction
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem exponential_factor (k q : Int) (j : Fin 128) (hk : k = 128 * q + j.val) :
    (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) =
      Real.exp ((k : ℝ) * Real.log 2 / 128) := by
  have hp : (2 : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 2) := by
    rw [RealExpError.exp_int_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hp, ← Real.exp_add, hk]
  congr 1
  push_cast
  ring

/-- Replacing the table entry by `2 ^ (j/128)` and the ideal residual by its exponential:
`s (1 + T j) exp a` is within `s / 2 ^ 98` of `2 ^ d exp x`. -/
theorem table_change (x s : UInt64) (k q d : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 768)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val)
    (hs : value s = (2 : ℝ) ^ (q + d) * value (ExpTableBounds.headBits j.val))
    (hS : 0 < value s) :
    |value s * (1 + value (ExpTableBounds.tailBits j.val)) *
        Real.exp (ExpResidualBounds.ideal x) - (2 : ℝ) ^ d * Real.exp (value x)| ≤
      value s * (1 / (2 : ℝ) ^ 98) := by
  let P := (2 : ℝ) ^ (q + d)
  let T := value (ExpTableBounds.tailBits j.val)
  let a := ExpResidualBounds.ideal x
  obtain ⟨_, _, _, _, ht⟩ := ExpTableBounds.entry_bounds j
  have hP : 0 < P := zpow_pos (by norm_num) _
  have hT : |1 + T| ≤ 2 := by
    calc
      _ ≤ |(1 : ℝ)| + |T| := abs_add_le _ _
      _ ≤ 1 + 1 / (2 : ℝ) ^ 53 := by
        simpa only [abs_one] using add_le_add (le_refl (1 : ℝ)) ht
      _ ≤ 2 := by norm_num
  have hbase :
      (2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * Real.exp a =
        Real.exp (value x) := by
    rw [exponential_factor k q j hk, ← Real.exp_add]
    congr 1
    dsimp [a, ExpResidualBounds.ideal]
    rw [hkv]
    ring
  have htarget :
      P * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * Real.exp a =
        (2 : ℝ) ^ d * Real.exp (value x) := by
    calc
      _ = (2 : ℝ) ^ d *
          ((2 : ℝ) ^ q * Real.exp ((j.val : ℝ) * Real.log 2 / 128) * Real.exp a) := by
        dsimp [P]
        rw [zpow_add₀ (by norm_num)]
        ring
      _ = _ := by rw [hbase]
  have htable :
      |value s * (1 + T) - P * Real.exp ((j.val : ℝ) * Real.log 2 / 128)| ≤
        value s * (1 / (2 : ℝ) ^ 99) := by
    have hid : value s * (1 + T) - P * Real.exp ((j.val : ℝ) * Real.log 2 / 128) =
        P * (ExpTableBounds.scale j.val - Real.exp ((j.val : ℝ) * Real.log 2 / 128)) := by
      rw [hs]
      dsimp [P, T, ExpTableBounds.scale]
      ring
    rw [hid, abs_mul, abs_of_pos hP]
    calc
      _ ≤ P * (ExpTableBounds.scale j.val / (2 : ℝ) ^ 100) :=
        mul_le_mul_of_nonneg_left (ExpTableBounds.scale_error j) hP.le
      _ = value s * (1 + T) / (2 : ℝ) ^ 100 := by
        rw [hs]
        dsimp [P, T, ExpTableBounds.scale]
        ring
      _ ≤ value s * 2 / (2 : ℝ) ^ 100 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left ((le_abs_self (1 + T)).trans hT) hS.le) (by positivity)
      _ = value s * (1 / (2 : ℝ) ^ 99) := by norm_num; ring
  have hi := ExpResidualBounds.ideal_bound x hxf hx
  have hae : |Real.exp a| ≤ 2 := by
    rw [abs_of_pos (Real.exp_pos a)]
    have he := Real.exp_bound (hi.trans (by norm_num : (1 / 320 : ℝ) ≤ 1))
      (n := 1) (by decide)
    norm_num [Finset.sum_range_succ] at he
    have h := (le_abs_self (Real.exp a - 1)).trans he
    linarith only [h, hi]
  rw [← htarget, ← sub_mul, abs_mul]
  calc
    _ ≤ (value s * (1 / (2 : ℝ) ^ 99)) * 2 :=
      mul_le_mul htable hae (abs_nonneg _) (by positivity)
    _ = _ := by norm_num; ring

theorem table_reconstruction_scaled_error (x s : UInt64) (k q d : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 768)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) (hsf : Finite s)
    (hs : value s = (2 : ℝ) ^ (q + d) * value (ExpTableBounds.headBits j.val))
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000) :
    Finite (ExpReconstructionBounds.reconstruction s (ExpResidualBounds.residual x)
      (ExpTableBounds.tailBits j.val)) ∧
      |value (ExpReconstructionBounds.reconstruction s (ExpResidualBounds.residual x)
        (ExpTableBounds.tailBits j.val)) - (2 : ℝ) ^ d * Real.exp (value x)| ≤
        (7 / 5) * unitRoundoff64 * value s := by
  let T := value (ExpTableBounds.tailBits j.val)
  let a := ExpResidualBounds.ideal x
  obtain ⟨_, htf, _, _, ht⟩ := ExpTableBounds.entry_bounds j
  have hrec := ExpReducedReconstruction.reconstruction_ideal_error x s
    (ExpTableBounds.tailBits j.val) hxf hx hsf htf hslo hshi ht
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  have hbetween := table_change x s k q d j hxf hx hkv hk hs hS
  refine ⟨hrec.1, ?_⟩
  calc
    _ ≤ (11 / 8) * unitRoundoff64 * value s + value s * (1 / (2 : ℝ) ^ 98) :=
      (abs_sub_le _ (value s * (1 + T) * Real.exp a) _).trans (add_le_add hrec.2 hbetween)
    _ ≤ (7 / 5) * unitRoundoff64 * value s := by
      have hc : (11 / 8) * unitRoundoff64 + 1 / (2 : ℝ) ^ 98 ≤
          (7 / 5) * unitRoundoff64 := by norm_num [unitRoundoff64]
      nlinarith only [mul_le_mul_of_nonneg_right hc hS.le]

/-- The reconstruction's sum before its final rounding is within `(21/64) u s` of
`2 ^ d exp x`. -/
theorem presum_scaled_error (x s : UInt64) (k q d : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 768)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) (hsf : Finite s)
    (hs : value s = (2 : ℝ) ^ (q + d) * value (ExpTableBounds.headBits j.val))
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000) :
    Finite (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation (ExpResidualBounds.residual x)
      (ExpTableBounds.tailBits j.val))) ∧
    |value (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation (ExpResidualBounds.residual x)
      (ExpTableBounds.tailBits j.val)))| ≤ value s / 32 ∧
    |value s + value (Wasm.IEEE64.mul s (ExpEvaluationBounds.evaluation
        (ExpResidualBounds.residual x) (ExpTableBounds.tailBits j.val))) -
      (2 : ℝ) ^ d * Real.exp (value x)| ≤ (21 / 64) * unitRoundoff64 * value s := by
  obtain ⟨_, htf, _, _, ht⟩ := ExpTableBounds.entry_bounds j
  have hr := ExpResidualBounds.residual_bounds x hxf hx
  have hS : 0 < value s := lt_of_lt_of_le (by positivity) hslo
  obtain ⟨hpf, hPm, hpre⟩ := ExpReconstructionBounds.presum_error s
    (ExpResidualBounds.residual x) (ExpTableBounds.tailBits j.val) hsf hr.1 htf hslo hshi
    hr.2.1 ht
  have hres := ExpReducedReconstruction.residual_change x s (ExpTableBounds.tailBits j.val)
    hxf hx hS ht
  have htab := table_change x s k q d j hxf hx hkv hk hs hS
  refine ⟨hpf, hPm, ?_⟩
  have hc : (37 / 128) * unitRoundoff64 + 1 / (2 : ℝ) ^ 58 + 1 / (2 : ℝ) ^ 98 ≤
      (21 / 64) * unitRoundoff64 := by norm_num [unitRoundoff64]
  calc
    _ ≤ (37 / 128) * unitRoundoff64 * value s +
        (value s * (1 / (2 : ℝ) ^ 58) + value s * (1 / (2 : ℝ) ^ 98)) :=
      (abs_sub_le _ _ _).trans (add_le_add hpre ((abs_sub_le _ _ _).trans
        (add_le_add hres htab)))
    _ ≤ (21 / 64) * unitRoundoff64 * value s := by
      nlinarith only [mul_le_mul_of_nonneg_right hc hS.le]

theorem table_reconstruction_error (x s : UInt64) (k q : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 512)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) (hsf : Finite s)
    (hs : value s = (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val))
    (hslo : 1 / (2 : ℝ) ^ 1000 ≤ value s) (hshi : value s ≤ (2 : ℝ) ^ 1000) :
    Finite (ExpReconstructionBounds.reconstruction s (ExpResidualBounds.residual x)
      (ExpTableBounds.tailBits j.val)) ∧
      |value (ExpReconstructionBounds.reconstruction s (ExpResidualBounds.residual x)
        (ExpTableBounds.tailBits j.val)) - Real.exp (value x)| ≤
        (7 / 5) * unitRoundoff64 * value s := by
  have h := table_reconstruction_scaled_error x s k q 0 j hxf
    (hx.trans (by norm_num)) hkv hk hsf (by simpa only [add_zero] using hs) hslo hshi
  simpa only [zpow_zero, one_mul] using h

#print axioms exponential_factor
#print axioms table_change
#print axioms table_reconstruction_scaled_error
#print axioms presum_scaled_error
#print axioms table_reconstruction_error

end Library.Numerics.Float64.Exp.ExpTableReconstruction
