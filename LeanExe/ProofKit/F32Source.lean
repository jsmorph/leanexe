module

public import LeanExe.Dialect.Float32
import Interpreter.Wasm.IEEE32
import Mathlib.Tactic
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

namespace LeanExe.ProofKit.F32Source

def add (left right : UInt32) : UInt32 :=
  (Float32.Model.add (Float32.Model.ofBits left) (Float32.Model.ofBits right)).toBits

def sub (left right : UInt32) : UInt32 :=
  (Float32.Model.sub (Float32.Model.ofBits left) (Float32.Model.ofBits right)).toBits

def mul (left right : UInt32) : UInt32 :=
  (Float32.Model.mul (Float32.Model.ofBits left) (Float32.Model.ofBits right)).toBits

def div (left right : UInt32) : UInt32 :=
  (Float32.Model.div (Float32.Model.ofBits left) (Float32.Model.ofBits right)).toBits

def sqrt (value : UInt32) : UInt32 :=
  (Float32.Model.sqrt (Float32.Model.ofBits value)).toBits

theorem add_source (left right : UInt32) : LeanExe.Float32.addBits left right = add left right := by rfl
theorem sub_source (left right : UInt32) : LeanExe.Float32.subBits left right = sub left right := by rfl
theorem mul_source (left right : UInt32) : LeanExe.Float32.mulBits left right = mul left right := by rfl
theorem div_source (left right : UInt32) : LeanExe.Float32.divBits left right = div left right := by rfl
theorem sqrt_source (value : UInt32) : LeanExe.Float32.sqrtBits value = sqrt value := by rfl

#print axioms add_source
#print axioms sub_source
#print axioms mul_source
#print axioms div_source
#print axioms sqrt_source

end LeanExe.ProofKit.F32Source
