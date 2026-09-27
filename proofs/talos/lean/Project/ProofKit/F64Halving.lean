import Project.ProofKit.F64DyadicBounds
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64Halving
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem half_scaled (word : UInt64) (hf : Finite word)
    (hsign : Wasm.IEEE64.sign word = false)
    (hbound : Wasm.IEEE64.scaledMagnitude word ≤ 2^1073) :
    Finite (Wasm.IEEE64.mul 0x3FE0000000000000 word) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.mul 0x3FE0000000000000 word) = false ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul 0x3FE0000000000000 word) ≤
        Wasm.IEEE64.scaledMagnitude word := by
  let m := Wasm.IEEE64.scaledMagnitude word
  have hhalf : Finite 0x3FE0000000000000 := by unfold CodeLib.IEEE64.Finite; decide
  have heq : Wasm.IEEE64.mul 0x3FE0000000000000 word =
      Wasm.IEEE64.roundDyadicMagnitude false (2^1073*m) 1074 := by
    rw [mul_finite_rounder _ _ hhalf hf]
    have hs : Wasm.IEEE64.sign 0x3FE0000000000000 = false := by decide
    have hm : Wasm.IEEE64.scaledMagnitude 0x3FE0000000000000 = 2^1073 := by decide
    rw [hs, hsign, hm]
    rfl
  have hproduct : 2^1073*m < 2^3170 := by
    calc
      2^1073*m ≤ 2^1073*2^1073 := Nat.mul_le_mul_left _ hbound
      _ = 2^2146 := by rw [← pow_add]
      _ < 2^3170 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hs := F64DyadicBounds.dyadic_relative false (2^1073*m) hproduct
  rw [heq]
  refine ⟨hs.1, hs.2.1, ?_⟩
  have hmax : (if 2^1073*m = 0 then 0 else max (2^1073*m) (2^1126)) ≤
      2^1126*m := by
    by_cases hm : m = 0
    · simp [hm]
    · rw [ite_eq_right (Nat.mul_ne_zero (by positivity) hm)]
      apply max_le
      · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
      · exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm)
  have hmaxInt : ((if 2^1073*m = 0 then 0 else max (2^1073*m) (2^1126) : Nat) : Int) ≤
      ((2^1126*m : Nat) : Int) := by exact_mod_cast hmax
  have he := hs.2.2.trans hmaxInt
  have hl := mul_le_mul_of_nonneg_right
    (le_abs_self (((Wasm.IEEE64.scaledMagnitude
      (Wasm.IEEE64.roundDyadicMagnitude false (2^1073*m) 1074) *
      2^1074 : Nat) : Int) - (2^1073*m : Nat)))
    (by positivity : (0 : Int) ≤ 2^53)
  have hb := hl.trans he
  push_cast at hb
  change _ ≤ m
  omega

def Bounded (word : UInt64) : Prop :=
  Finite word ∧ Wasm.IEEE64.sign word = false ∧
    Wasm.IEEE64.scaledMagnitude word ≤ 2^1073

theorem zero_bounded : Bounded 0 := by
  constructor
  · unfold CodeLib.IEEE64.Finite
    decide
  · constructor <;> decide

theorem half_bounded : Bounded 0x3FE0000000000000 := by
  constructor
  · unfold CodeLib.IEEE64.Finite
    decide
  · constructor <;> decide

theorem half_preserves {word : UInt64} (h : Bounded word) :
    Bounded (Wasm.IEEE64.mul 0x3FE0000000000000 word) ∧
      Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul 0x3FE0000000000000 word) ≤
        Wasm.IEEE64.scaledMagnitude word := by
  have hs := half_scaled word h.1 h.2.1 h.2.2
  exact ⟨⟨hs.1, hs.2.1, hs.2.2.trans h.2.2⟩, hs.2.2⟩

theorem bounded_value {word : UInt64} (h : Bounded word) :
    0 ≤ value word ∧ value word ≤ 1/2 := by
  have hv : value word = (Wasm.IEEE64.scaledMagnitude word : ℝ)/(2:ℝ)^1074 := by
    simp [value, Wasm.IEEE64.scaledValue, h.2.1]
  rw [hv]
  refine ⟨by positivity, ?_⟩
  have hb : (Wasm.IEEE64.scaledMagnitude word : ℝ) ≤ (2:ℝ)^1073 := by
    exact_mod_cast h.2.2
  have hu := div_le_div_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 2^1074)
  norm_num at hu ⊢
  exact hu

#print axioms half_scaled
#print axioms half_preserves
#print axioms bounded_value
end Project.ProofKit.F64Halving
