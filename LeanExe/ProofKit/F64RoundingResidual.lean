module

public import LeanExe.ProofKit.F64Adjacent
import LeanExe.ProofKit.F64AddEnclosure
import LeanExe.ProofKit.F64MulEnclosure
import LeanExe.ProofKit.F64AdjacentSigned
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

/-! The rounding radius of a binary64 word, the larger of its gaps to its two neighbors, bounds
the error of a finite rounded sum, difference, or product against the exact result. -/

namespace LeanExe.ProofKit.F64RoundingResidual
open CodeLib.IEEE64
open LeanExe.ProofKit.F64Adjacent
noncomputable section

def radius (word : UInt64) : ℝ :=
  max (value word - value (nextDown word)) (value (nextUp word) - value word)

theorem radius_positive (word : UInt64) (hf : CodeLib.IEEE64.Finite word) :
    0 < radius word :=
  (sub_pos.mpr (nextUp_lt word hf)).trans_le (le_max_right _ _)

theorem enclosure_error (word : UInt64) (exactValue : ℝ)
    (h : value (nextDown word) ≤ exactValue ∧ exactValue ≤ value (nextUp word)) :
    |value word - exactValue| ≤ radius word := by
  have hl := le_max_left (value word - value (nextDown word))
    (value (nextUp word) - value word)
  have hr := le_max_right (value word - value (nextDown word))
    (value (nextUp word) - value word)
  unfold radius
  exact abs_le.mpr ⟨by linarith [h.2], by linarith [h.1]⟩

theorem add_error (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.add a b)) :
    |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ radius (Wasm.IEEE64.add a b) :=
  enclosure_error _ _ (add_enclosure a b ha hb hf)

theorem sub_error (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.sub a b)) :
    |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤ radius (Wasm.IEEE64.sub a b) :=
  enclosure_error _ _ (sub_enclosure a b ha hb hf)

theorem mul_error (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) (hf : CodeLib.IEEE64.Finite (Wasm.IEEE64.mul a b)) :
    |value (Wasm.IEEE64.mul a b) - value a * value b| ≤ radius (Wasm.IEEE64.mul a b) :=
  enclosure_error _ _ (mul_enclosure a b ha hb hf)


end
end LeanExe.ProofKit.F64RoundingResidual
