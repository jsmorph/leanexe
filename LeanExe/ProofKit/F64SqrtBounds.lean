module

public import CodeLib.IEEE64.Roundoff
public import Mathlib.Analysis.Real.Sqrt
import LeanExe.ProofKit.F64SqrtRounding
import LeanExe.ProofKit.F64NormalizeTiny
import CodeLib.IEEE64.Operations
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Basify

public section

/-! The relative error of the rounded binary64 square root of a word's value. -/

namespace LeanExe.ProofKit.F64SqrtBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem sqrt_real_relative (a : UInt64) (ha : Finite a)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hsign : Wasm.IEEE64.sign a = false) :
    Finite (Wasm.IEEE64.sqrt a) ∧
    |value (Wasm.IEEE64.sqrt a) - Real.sqrt (value a)| ≤
      unitRoundoff64 * Real.sqrt (value a) := by
  let magnitude := Wasm.IEEE64.scaledMagnitude a
  let result := Wasm.IEEE64.roundSqrtMagnitude magnitude
  have hmax : magnitude < 2^2098 :=
    (F64NormalizeTiny.scaledMagnitude_bound a).trans_le
      (Nat.pow_le_pow_right (by omega)
        (by have := F64Admissibility.finite_exponent_bound a ha; omega))
  have hs := F64SqrtRounding.sqrt_relative magnitude ha0 hmax
  rw [sqrt_positive_finite a ha ha0 hsign]
  refine ⟨hs.1, ?_⟩
  have hscalePos : (0 : ℝ) < (2 : ℝ)^1074 := by positivity
  have hsqrtScale : Real.sqrt ((2 : ℝ)^1074) = (2 : ℝ)^537 := by
    rw [show (2 : ℝ)^1074 = ((2 : ℝ)^537)^2 by rw [← pow_mul]]
    exact Real.sqrt_sq (by positivity)
  have hsqrtScaled : Real.sqrt ((magnitude : ℝ) / (2 : ℝ)^1074) =
      Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074) / (2 : ℝ)^1074 := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ magnitude),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ magnitude), hsqrtScale]
    field_simp
  have hvalueA : value a = (magnitude : ℝ) / (2 : ℝ)^1074 := by
    simp [value, magnitude, Wasm.IEEE64.scaledValue, hsign]
  have hvalueResult : value result =
      (Wasm.IEEE64.scaledMagnitude result : ℝ) / (2 : ℝ)^1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hs.2.1, result]
  have heq : value result - Real.sqrt (value a) =
      ((Wasm.IEEE64.scaledMagnitude result : ℝ) -
        Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074)) / (2 : ℝ)^1074 := by
    rw [hvalueA, hvalueResult, hsqrtScaled]
    ring
  change |value result - Real.sqrt (value a)| ≤ unitRoundoff64 * Real.sqrt (value a)
  rw [heq, abs_div, abs_of_pos hscalePos, hvalueA, hsqrtScaled]
  have herr : |(Wasm.IEEE64.scaledMagnitude result : ℝ) -
      Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074)| ≤
      unitRoundoff64 * Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074) := by
    simpa only [result, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hs.2.2
  exact (div_le_div_of_nonneg_right herr hscalePos.le).trans_eq (by ring)

end LeanExe.ProofKit.F64SqrtBounds
