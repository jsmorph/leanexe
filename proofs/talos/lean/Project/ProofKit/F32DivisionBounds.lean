import Project.ProofKit.F32RationalBounds
import CodeLib.IEEE32.Division

set_option exponentiation.threshold 512

namespace Project.ProofKit.F32DivisionBounds
open Wasm CodeLib.IEEE32

theorem div_scaled_error (a b : UInt32) (bound : Nat)
    (hLower : 24 ≤ bound) (hUpper : bound ≤ 275)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0)
    (hab : Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤
      Wasm.IEEE32.scaledMagnitude b * 2 ^ bound) :
    CodeLib.IEEE32.Finite (Wasm.IEEE32.div a b) ∧
      |Wasm.IEEE32.scaledValue (Wasm.IEEE32.div a b) *
          Wasm.IEEE32.scaledValue b -
        Wasm.IEEE32.scaledValue a * (2 : Int) ^ 149| ≤
          Wasm.IEEE32.scaledMagnitude b * 2 ^ (bound - 24) := by
  let numerator := Wasm.IEEE32.scaledMagnitude a * 2 ^ 149
  let denominator := Wasm.IEEE32.scaledMagnitude b
  have hbound : numerator ≤ denominator * 2 ^ bound := hab
  have hs := F32RationalBounds.roundRationalMagnitude_spec
    (Wasm.IEEE32.sign a != Wasm.IEEE32.sign b)
    numerator denominator bound hLower hUpper hb0 hbound
  have hdiv := div_finite_rounder a b ha hb hb0
  rw [hdiv]
  constructor
  · exact hs.1
  · have herr := hs.2.2
    have hresultSign := hs.2.1
    have habs (x y : Int) : |-x + y| = |x + -y| := by
      rw [show -x + y = -(x + -y) by ring, abs_neg]
    cases hsa : Wasm.IEEE32.sign a <;>
      cases hsb : Wasm.IEEE32.sign b <;>
      simp [numerator, denominator, hsa, hsb] at hresultSign <;>
      simp [Wasm.IEEE32.scaledValue, hresultSign, hsa, hsb,
        numerator, denominator] at herr ⊢
    all_goals
      first
      | simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr
      | rw [habs]
        simpa [Int.natCast_mul, sub_eq_add_neg, add_comm] using herr

noncomputable def epsilon (bound : Nat) : ℝ := (2 : ℝ) ^ (bound - 24) / 2 ^ 149

theorem div_real_error (a b : UInt32) (bound : Nat)
    (hLower : 24 ≤ bound) (hUpper : bound ≤ 275)
    (ha : CodeLib.IEEE32.Finite a) (hb : CodeLib.IEEE32.Finite b)
    (hb0 : Wasm.IEEE32.scaledMagnitude b ≠ 0)
    (hab : Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤
      Wasm.IEEE32.scaledMagnitude b * 2 ^ bound) :
    CodeLib.IEEE32.Finite (Wasm.IEEE32.div a b) ∧
      |value (Wasm.IEEE32.div a b) - value a / value b| ≤
        epsilon bound := by
  have hs := div_scaled_error a b bound hLower hUpper ha hb hb0 hab
  constructor
  · exact hs.1
  · let z : Int :=
      Wasm.IEEE32.scaledValue (Wasm.IEEE32.div a b) *
          Wasm.IEEE32.scaledValue b -
        Wasm.IEEE32.scaledValue a * (2 : Int) ^ 149
    have hz : |z| ≤ Wasm.IEEE32.scaledMagnitude b * 2 ^ (bound - 24) := hs.2
    have hbScaled : Wasm.IEEE32.scaledValue b ≠ 0 := by
      intro h
      apply hb0
      rw [← natAbs_scaledValue]
      simp [h]
    have hbScaledReal : (Wasm.IEEE32.scaledValue b : ℝ) ≠ 0 := by
      exact_mod_cast hbScaled
    have heq :
        value (Wasm.IEEE32.div a b) - value a / value b =
          (z : ℝ) /
            ((2 : ℝ) ^ 149 * Wasm.IEEE32.scaledValue b) := by
      simp [value, z]
      field_simp
      ring
    have hbAbs :
        |(Wasm.IEEE32.scaledValue b : ℝ)| =
          Wasm.IEEE32.scaledMagnitude b := by
      simp [Wasm.IEEE32.scaledValue]
      split <;> simp
    rw [heq, abs_div]
    have hdenPos :
        0 < |(2 : ℝ) ^ 149 * Wasm.IEEE32.scaledValue b| := by
      positivity
    apply (div_le_iff₀ hdenPos).2
    have hzReal :
        |(z : ℝ)| ≤
          (Wasm.IEEE32.scaledMagnitude b : ℝ) * 2 ^ (bound - 24) := by
      exact_mod_cast hz
    calc
      |(z : ℝ)| ≤
          (Wasm.IEEE32.scaledMagnitude b : ℝ) * 2 ^ (bound - 24) := hzReal
      _ = epsilon bound *
          |(2 : ℝ) ^ 149 * Wasm.IEEE32.scaledValue b| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ 149),
          hbAbs]
        unfold epsilon
        field_simp

#print axioms div_scaled_error
#print axioms div_real_error
end Project.ProofKit.F32DivisionBounds
