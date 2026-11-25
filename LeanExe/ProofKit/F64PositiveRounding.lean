module

public import LeanExe.ProofKit.F64NearestEven
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

public section

namespace LeanExe.ProofKit.F64PositiveRounding
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

@[expose] def positiveInfinity : UInt64 := 0x7FF0000000000000

@[expose] noncomputable def overflowThreshold : ℝ := (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970

def IsRoundNearestEven (y : ℝ) (w : UInt64) : Prop :=
  0 ≤ y ∧
    ((y < overflowThreshold ∧ F64NearestNonnegative.NearestEven y w) ∨
      (overflowThreshold ≤ y ∧ w = positiveInfinity))

noncomputable def roundNearestEven (y : ℝ) : UInt64 :=
  if overflowThreshold ≤ y then positiveInfinity
  else F64NearestEven.roundNearestEven y

theorem largest_finite_value :
    value (0x7FEFFFFFFFFFFFFF : UInt64) = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 971 := by
  have h : Wasm.IEEE64.scaledValue (0x7FEFFFFFFFFFFFFF : UInt64) =
      (2 : Int) ^ 2098 - (2 : Int) ^ 2045 := by decide +kernel
  rw [value, h]
  norm_num

theorem overflow_threshold_midpoint :
    overflowThreshold = (value (0x7FEFFFFFFFFFFFFF : UInt64) + (2 : ℝ) ^ 1024) / 2 := by
  rw [largest_finite_value, overflowThreshold]
  norm_num

theorem threshold_positive : 0 < overflowThreshold := by
  norm_num [overflowThreshold]

theorem reference_finite (y : ℝ) (hy : y < overflowThreshold) :
    roundNearestEven y = F64NearestEven.roundNearestEven y := by
  exact ite_eq_right (not_le_of_gt hy)

theorem reference_overflow (y : ℝ) (hy : overflowThreshold ≤ y) :
    roundNearestEven y = positiveInfinity :=
  ite_eq_left hy

theorem roundNearestEven_spec (y : ℝ) (hy : 0 ≤ y) :
    IsRoundNearestEven y (roundNearestEven y) := by
  refine ⟨hy, ?_⟩
  by_cases h : overflowThreshold ≤ y
  · exact Or.inr ⟨h, reference_overflow y h⟩
  · have hl : y < overflowThreshold := lt_of_not_ge h
    exact Or.inl ⟨hl, by rw [reference_finite y hl]; exact
      F64NearestEven.roundNearestEven_spec y⟩

theorem reference_unique (y : ℝ) (w : UInt64) (hw : IsRoundNearestEven y w) :
    roundNearestEven y = w := by
  rcases hw.2 with ⟨hy, hn⟩ | ⟨hy, he⟩
  · rw [reference_finite y hy]
    exact F64NearestEven.roundNearestEven_eq y w hn
  · rw [reference_overflow y hy, he]

#print axioms largest_finite_value
#print axioms overflow_threshold_midpoint
#print axioms threshold_positive
#print axioms roundNearestEven_spec
#print axioms reference_unique

end LeanExe.ProofKit.F64PositiveRounding
