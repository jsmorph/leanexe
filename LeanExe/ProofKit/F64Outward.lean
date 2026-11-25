module

public import LeanExe.ProofKit.F64Adjacent
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
import LeanExe.ProofKit.F64Order

public section

namespace LeanExe.ProofKit.F64Outward
open LeanExe.ProofKit.F64Order
open LeanExe.ProofKit.F64Adjacent

structure Checked where
  status : UInt64
  value : UInt64
  deriving DecidableEq, Inhabited, Repr

@[expose] def rejected : Checked := ⟨1, 0⟩

@[expose] def neighbor (up : Bool) (bits : UInt64) : UInt64 :=
  if up then nextUp bits else nextDown bits

@[expose] def endpoint (up : Bool) (rounded : UInt64) : Checked :=
  if finiteBits rounded then
    let bits := neighbor up rounded
    if finiteBits bits then ⟨0, bits⟩ else rejected
  else rejected

@[expose] def add (up : Bool) (a b : UInt64) : Checked :=
  if finiteBits a && finiteBits b then endpoint up (Wasm.IEEE64.add a b)
  else rejected

@[expose] def sub (up : Bool) (a b : UInt64) : Checked :=
  if finiteBits a && finiteBits b then endpoint up (Wasm.IEEE64.sub a b)
  else rejected

@[expose] def mul (up : Bool) (a b : UInt64) : Checked :=
  if finiteBits a && finiteBits b then endpoint up (Wasm.IEEE64.mul a b)
  else rejected

@[expose] def div (up : Bool) (a b : UInt64) : Checked :=
  if finiteBits a && finiteBits b && decide (0 < absBits b) then
    endpoint up (Wasm.IEEE64.div a b)
  else rejected

@[expose] def sqrt (up : Bool) (a : UInt64) : Checked :=
  if finiteBits a && decide (a ≤ 0x8000000000000000) then
    endpoint up (Wasm.IEEE64.sqrt a)
  else rejected

end LeanExe.ProofKit.F64Outward
