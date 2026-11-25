module

public import LeanExe.ProofKit.F64RoundingResidual
import LeanExe.ProofKit.F64DivEnclosure
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

/-! The error of a rounded binary64 quotient, bounded by its rounding radius. -/

namespace LeanExe.ProofKit.F64RoundingResidual
open CodeLib.IEEE64

theorem div_error (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.div a b)) :
    |value (Wasm.IEEE64.div a b) - value a / value b| ≤ radius (Wasm.IEEE64.div a b) :=
  enclosure_error _ _ (F64Adjacent.div_enclosure a b ha hb hb0 hf)

end LeanExe.ProofKit.F64RoundingResidual
