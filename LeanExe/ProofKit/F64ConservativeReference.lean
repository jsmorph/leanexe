module

public import LeanExe.ProofKit.F64ConservativeUpdate
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
import LeanExe.ProofKit.F64RoundingResidual

public section

/-! The error of a rounded conservative update against the exact update with exact fluxes. -/

namespace LeanExe.ProofKit.F64ConservativeUpdate
open CodeLib.IEEE64
open LeanExe.ProofKit.F64RoundingResidual (radius)

theorem reference_bound {ratio state fluxL fluxR output : UInt64}
    (h : Certificate ratio state fluxL fluxR output)
    (referenceL referenceR boundL boundR : ℝ)
    (hl : |value fluxL - referenceL| ≤ boundL)
    (hr : |value fluxR - referenceR| ≤ boundR) :
    |value output - (value state - value ratio * (referenceR - referenceL))| ≤
      |value ratio| * radius (Wasm.IEEE64.sub fluxR fluxL) +
      radius (Wasm.IEEE64.mul ratio (Wasm.IEEE64.sub fluxR fluxL)) + radius output +
      |value ratio| * (boundL + boundR) := by
  have heq : value output - (value state - value ratio * (referenceR - referenceL)) =
      residual ratio state fluxL fluxR output +
        value ratio * ((value fluxL - referenceL) - (value fluxR - referenceR)) := by
    unfold residual
    ring
  rw [heq]
  calc
    _ ≤ |residual ratio state fluxL fluxR output| +
        |value ratio * ((value fluxL - referenceL) - (value fluxR - referenceR))| :=
      abs_add_le _ _
    _ = |residual ratio state fluxL fluxR output| +
        |value ratio| * |(value fluxL - referenceL) - (value fluxR - referenceR)| := by
      rw [abs_mul]
    _ ≤ _ := by
      apply add_le_add (residual_bound h)
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (abs_sub _ _).trans (add_le_add hl hr)

end LeanExe.ProofKit.F64ConservativeUpdate
