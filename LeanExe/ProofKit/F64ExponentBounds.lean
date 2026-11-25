module

public import LeanExe.ProofKit.F64Order
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

namespace LeanExe.ProofKit.F64ExponentBounds
open CodeLib.IEEE64 F64Order

set_option exponentiation.threshold 4096

@[expose] def boundary (e : Nat) : UInt64 := UInt64.ofNat (e * 2 ^ 52)

theorem boundary_fields (e : Nat) (he : e < 2048) :
    (boundary e).toNat = e * 2 ^ 52 ∧ absBits (boundary e) = boundary e := by
  have hn : e * 2 ^ 52 < 2 ^ 63 := by
    calc
      _ < 2048 * 2 ^ 52 := Nat.mul_lt_mul_of_pos_right he (Nat.two_pow_pos 52)
      _ = _ := by norm_num
  have hw : (boundary e).toNat = e * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (hn.trans (by norm_num : 2 ^ 63 < 2 ^ 64))
  refine ⟨hw, ?_⟩
  apply UInt64.toNat_inj.mp
  rw [absBits_toNat, hw, Nat.mod_eq_of_lt hn]

theorem magnitude_le_boundary (x : UInt64) (e : Nat) (he : e < 2048)
    (hx : Wasm.IEEE64.exponent x < e) :
    |value x| ≤ |value (boundary e)| := by
  have hb := boundary_fields e he
  apply abs_value_mono x (boundary e)
  rw [hb.2]
  apply UInt64.le_iff_toNat_le.mpr
  rw [hb.1]
  rw [exponent_abs] at hx
  omega

theorem exponent_lt_of_magnitude_lt (x : UInt64) (e : Nat) (he : e < 2048)
    (hx : |value x| < |value (boundary e)|) :
    Wasm.IEEE64.exponent x < e := by
  by_contra hn
  have hb := boundary_fields e he
  have hord : absBits (boundary e) ≤ absBits x := by
    rw [hb.2]
    apply UInt64.le_iff_toNat_le.mpr
    rw [hb.1]
    rw [exponent_abs] at hn
    omega
  exact (not_lt_of_ge (abs_value_mono (boundary e) x hord)) hx

#print axioms boundary_fields
#print axioms magnitude_le_boundary
#print axioms exponent_lt_of_magnitude_lt

end LeanExe.ProofKit.F64ExponentBounds
