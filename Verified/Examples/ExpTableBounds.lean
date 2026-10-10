import Verified.Examples.Exp
import CodeLib.IEEE64.Roundoff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Verified.Examples.ExpTableBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

def headBits (j : Nat) : UInt64 :=
  Exp.expTable[2 * j + 1]! + (UInt64.ofNat j <<< (45 : UInt64))

def tailBits (j : Nat) : UInt64 :=
  Exp.expTable[2 * j]!

noncomputable def scale (j : Nat) : ℝ :=
  value (headBits j) * (1 + value (tailBits j))

def rationalScale (j : Nat) : ℚ :=
  ((Wasm.IEEE64.scaledValue (headBits j) : ℚ) / (2 : ℚ) ^ 1074) *
    (1 + (Wasm.IEEE64.scaledValue (tailBits j) : ℚ) / (2 : ℚ) ^ 1074)

theorem rationalScale_cast (j : Nat) : (rationalScale j : ℝ) = scale j := by
  simp [rationalScale, scale, value]

theorem checked_table_bounds : ∀ j : Fin 128,
    Finite (headBits j.val) ∧ Finite (tailBits j.val) ∧
    0 < rationalScale j.val ∧
    (rationalScale j.val * (1 - 1 / (2 : ℚ) ^ 100)) ^ 128 ≤ (2 : ℚ) ^ j.val ∧
    (2 : ℚ) ^ j.val ≤ (rationalScale j.val * (1 + 1 / (2 : ℚ) ^ 100)) ^ 128 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem target_power (j : Nat) :
    (Real.exp ((j : ℝ) * Real.log 2 / 128)) ^ 128 = (2 : ℝ) ^ j := by
  calc
    _ = Real.exp ((128 : ℝ) * ((j : ℝ) * Real.log 2 / 128)) :=
      (Real.exp_nat_mul _ 128).symm
    _ = Real.exp ((j : ℝ) * Real.log 2) := by congr 1; ring
    _ = (Real.exp (Real.log 2)) ^ j := Real.exp_nat_mul _ j
    _ = (2 : ℝ) ^ j := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem scale_enclosure (j : Fin 128) :
    scale j.val * (1 - 1 / (2 : ℝ) ^ 100) ≤
        Real.exp ((j.val : ℝ) * Real.log 2 / 128) ∧
    Real.exp ((j.val : ℝ) * Real.log 2 / 128) ≤
        scale j.val * (1 + 1 / (2 : ℝ) ^ 100) := by
  have hc := checked_table_bounds j
  have hs : (0 : ℝ) < scale j.val := by
    rw [← rationalScale_cast]
    exact_mod_cast hc.2.2.1
  have hl : (scale j.val * (1 - 1 / (2 : ℝ) ^ 100)) ^ 128 ≤
      (2 : ℝ) ^ j.val := by
    rw [← rationalScale_cast]
    have hcast :
        (((rationalScale j.val * (1 - 1 / (2 : ℚ) ^ 100)) ^ 128 : ℚ) : ℝ) ≤
          (((2 : ℚ) ^ j.val : ℚ) : ℝ) := Rat.cast_le.mpr hc.2.2.2.1
    simpa only [Rat.cast_pow, Rat.cast_mul, Rat.cast_sub, Rat.cast_one,
      Rat.cast_div, Rat.cast_ofNat] using hcast
  have hu : (2 : ℝ) ^ j.val ≤
      (scale j.val * (1 + 1 / (2 : ℝ) ^ 100)) ^ 128 := by
    rw [← rationalScale_cast]
    have hcast :
        (((2 : ℚ) ^ j.val : ℚ) : ℝ) ≤
          (((rationalScale j.val * (1 + 1 / (2 : ℚ) ^ 100)) ^ 128 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hc.2.2.2.2
    simpa only [Rat.cast_pow, Rat.cast_mul, Rat.cast_add, Rat.cast_one,
      Rat.cast_div, Rat.cast_ofNat] using hcast
  constructor
  · by_contra h
    have hp := pow_lt_pow_left₀ (lt_of_not_ge h)
      (Real.exp_pos _).le (by decide : (128 : Nat) ≠ 0)
    rw [target_power] at hp
    exact (not_lt_of_ge hl) hp
  · by_contra h
    have hb : 0 ≤ scale j.val * (1 + 1 / (2 : ℝ) ^ 100) :=
      mul_nonneg hs.le (by norm_num)
    have hp := pow_lt_pow_left₀ (lt_of_not_ge h) hb
      (by decide : (128 : Nat) ≠ 0)
    rw [target_power] at hp
    exact (not_lt_of_ge hu) hp

theorem scale_error (j : Fin 128) :
    |scale j.val - Real.exp ((j.val : ℝ) * Real.log 2 / 128)| ≤
      scale j.val / (2 : ℝ) ^ 100 := by
  obtain ⟨hl, hu⟩ := scale_enclosure j
  have hden : scale j.val / (2 : ℝ) ^ 100 =
      scale j.val * (1 / (2 : ℝ) ^ 100) := div_eq_mul_one_div _ _
  rw [hden]
  apply abs_le.mpr
  constructor <;> nlinarith

#print axioms checked_table_bounds
#print axioms scale_enclosure
#print axioms scale_error


theorem checked_entry_magnitudes : ∀ j : Fin 128,
    (1 : ℚ) ≤ (Wasm.IEEE64.scaledValue (headBits j.val) : ℚ) / (2 : ℚ) ^ 1074 ∧
    (Wasm.IEEE64.scaledValue (headBits j.val) : ℚ) / (2 : ℚ) ^ 1074 ≤ 2 ∧
    |(Wasm.IEEE64.scaledValue (tailBits j.val) : ℚ) / (2 : ℚ) ^ 1074| ≤
      1 / (2 : ℚ) ^ 53 := by
  decide +kernel

theorem entry_bounds (j : Fin 128) :
    Finite (headBits j.val) ∧ Finite (tailBits j.val) ∧
    1 ≤ value (headBits j.val) ∧ value (headBits j.val) ≤ 2 ∧
    |value (tailBits j.val)| ≤ 1 / (2 : ℝ) ^ 53 := by
  obtain ⟨hl, hu, ht⟩ := checked_entry_magnitudes j
  have hlr : (1 : ℝ) ≤ value (headBits j.val) := by
    have hc : ((1 : ℚ) : ℝ) ≤
        (((Wasm.IEEE64.scaledValue (headBits j.val) : ℚ) / (2 : ℚ) ^ 1074 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hl
    simpa [value] using hc
  have hur : value (headBits j.val) ≤ (2 : ℝ) := by
    have hc : (((Wasm.IEEE64.scaledValue (headBits j.val) : ℚ) / (2 : ℚ) ^ 1074 : ℚ) : ℝ) ≤
        ((2 : ℚ) : ℝ) := Rat.cast_le.mpr hu
    simpa [value] using hc
  have htr : |value (tailBits j.val)| ≤ 1 / (2 : ℝ) ^ 53 := by
    have hc : ((|(Wasm.IEEE64.scaledValue (tailBits j.val) : ℚ) / (2 : ℚ) ^ 1074| : ℚ) : ℝ) ≤
        ((1 / (2 : ℚ) ^ 53 : ℚ) : ℝ) := Rat.cast_le.mpr ht
    simpa [value] using hc
  have hf := checked_table_bounds j
  exact ⟨hf.1, hf.2.1, hlr, hur, htr⟩

#print axioms checked_entry_magnitudes
#print axioms entry_bounds

end Verified.Examples.ExpTableBounds
