import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64PackRelative
import LeanExe.ProofKit.F64GridExact
import CodeLib.IEEE64.Operations

/-!
Exact products of binary64 words.  When the scaled magnitudes are `ma 2 ^ sa` and `mb 2 ^ sb`
with `ma mb < 2 ^ 53` and `sa + sb` at least 1074, the rounded product is the exact product, with
scaled magnitude `ma mb 2 ^ (sa + sb - 1074)`.  `int_mul_exact` is the case of a word that holds
an integer `n`, whose scaled magnitude is `n 2 ^ 1074`.
-/

namespace LeanExe.ProofKit.F64ExactProduct
open CodeLib.IEEE64

theorem mul_exact_scaled (a b : UInt64) (ha : Finite a) (hb : Finite b) (ma mb sa sb : Nat)
    (hma : Wasm.IEEE64.scaledMagnitude a = ma * 2 ^ sa)
    (hmb : Wasm.IEEE64.scaledMagnitude b = mb * 2 ^ sb)
    (hm : ma * mb < 2 ^ 53) (hs : 1074 ≤ sa + sb) (hs2 : sa + sb ≤ 1074 + 2043) :
    Finite (Wasm.IEEE64.mul a b) ∧ value (Wasm.IEEE64.mul a b) = value a * value b ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul a b) = (ma * mb) * 2 ^ (sa + sb - 1074) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.mul a b) = (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
  set t := sa + sb - 1074 with ht
  have hst : sa + sb = 1074 + t := by omega
  have hprod : Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b =
      (ma * mb) * 2 ^ (1074 + t) := by
    rw [hma, hmb, ← hst, pow_add]
    ring
  rw [mul_finite_rounder a b ha hb, hprod, F64PowerScale.dyadic_shifted_exact _ _ _ hm]
  have hmax : (ma * mb) * 2 ^ t < 2 ^ 2097 := by
    calc (ma * mb) * 2 ^ t < 2 ^ 53 * 2 ^ t := Nat.mul_lt_mul_of_pos_right hm (by positivity)
      _ = 2 ^ (53 + t) := by rw [pow_add]
      _ ≤ 2 ^ 2097 := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hpf, hpm, hps⟩ := F64PackRelative.pack_spec
    (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) _ hmax
  rw [F64GridExact.roundedMagnitude_shifted_small _ _ hm.le] at hpm
  refine ⟨hpf, ?_, hpm, hps⟩
  have hN : (ma * mb * 2 ^ t) * 2 ^ 1074 = (ma * 2 ^ sa) * (mb * 2 ^ sb) := by
    rw [mul_mul_mul_comm, ← pow_add, hst, pow_add]
    ring
  have hZ : ((ma * mb * 2 ^ t : Nat) : Int) * 2 ^ 1074 =
      ((ma * 2 ^ sa : Nat) : Int) * ((mb * 2 ^ sb : Nat) : Int) := by
    exact_mod_cast hN
  have hI : Wasm.IEEE64.scaledValue
      (Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b)
        (ma * mb * 2 ^ t)) * 2 ^ 1074 =
      Wasm.IEEE64.scaledValue a * Wasm.IEEE64.scaledValue b := by
    simp only [Wasm.IEEE64.scaledValue, hps, hpm, hma, hmb]
    have e1 : (true != true) = false := rfl
    have e2 : (true != false) = true := rfl
    have e3 : (false != true) = true := rfl
    have e4 : (false != false) = false := rfl
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;>
      simp only [e1, e2, e3, e4, ↓reduceIte, Bool.false_eq_true] <;>
      first | linear_combination hZ | linear_combination -hZ
  have hR : (Wasm.IEEE64.scaledValue
      (Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b)
        (ma * mb * 2 ^ t)) : ℝ) * 2 ^ 1074 =
      (Wasm.IEEE64.scaledValue a : ℝ) * Wasm.IEEE64.scaledValue b := by
    exact_mod_cast hI
  simp only [value]
  rw [div_mul_div_comm, ← hR]
  field_simp

/-- A word holding the integer `n` times a word of scaled magnitude `m 2 ^ s`. -/
theorem int_mul_exact (a b : UInt64) (ha : Finite a) (hb : Finite b) (n m s : Nat)
    (hma : Wasm.IEEE64.scaledMagnitude a = n * 2 ^ 1074)
    (hmb : Wasm.IEEE64.scaledMagnitude b = m * 2 ^ s)
    (hnm : n * m < 2 ^ 53) (hs : s ≤ 2043) :
    Finite (Wasm.IEEE64.mul a b) ∧ value (Wasm.IEEE64.mul a b) = value a * value b ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul a b) = (n * m) * 2 ^ s ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.mul a b) = (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by
  have h := mul_exact_scaled a b ha hb n m 1074 s hma hmb hnm (by omega) (by omega)
  rw [show 1074 + s - 1074 = s by omega] at h
  exact h

#print axioms mul_exact_scaled
#print axioms int_mul_exact

end LeanExe.ProofKit.F64ExactProduct
