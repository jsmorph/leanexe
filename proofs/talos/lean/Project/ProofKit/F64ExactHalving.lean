import Project.ProofKit.F64DyadicBounds
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64ExactHalving
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem dyadic_shifted (negative : Bool) (significand shift : Nat)
    (hl : 2^52 ≤ significand) (hu : significand < 2^53) :
    Wasm.IEEE64.roundDyadicMagnitude negative (significand*2^(1074+shift)) 1074 =
      Wasm.IEEE64.roundScaledMagnitude negative (significand*2^shift) := by
  have hn : significand ≠ 0 := by omega
  have hlog : Nat.log2 significand = 52 :=
    (Nat.log2_eq_iff hn).mpr ⟨hl, by simpa using hu⟩
  have hs : Nat.log2 (significand*2^(1074+shift))-(1074+52) = shift := by
    rw [F64DyadicBounds.log2_mul_two_pow _ _ hn, hlog]
    omega
  have hnprod : significand*2^(1074+shift) ≠ 0 := Nat.mul_ne_zero hn (by positivity)
  simp only [Wasm.IEEE64.roundDyadicMagnitude, beq_iff_eq, hnprod, ite_false, hs]
  by_cases hz : shift = 0
  · subst shift
    simp only [Nat.add_zero, ite_true, pow_zero, Nat.mul_one, show ¬1074 = 0 by omega, ite_false]
    rw [F64DyadicBounds.roundShift_mul_two_pow _ _ (by omega)]
  · rw [ite_eq_right hz, F64DyadicBounds.roundShift_mul_two_pow _ _ (by omega)]

theorem half_exact (word : UInt64) (hf : Finite word)
    (he : 2 ≤ Wasm.IEEE64.exponent word) :
    Finite (Wasm.IEEE64.mul word 0x3FE0000000000000) ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.mul word 0x3FE0000000000000) = Wasm.IEEE64.sign word ∧
      value (Wasm.IEEE64.mul word 0x3FE0000000000000) = value word/2 := by
  let e := Wasm.IEEE64.exponent word
  let s := 2^52+Wasm.IEEE64.fraction word
  have hfrac : Wasm.IEEE64.fraction word < 2^52 := Nat.mod_lt _ (by positivity)
  have hlo : 2^52 ≤ s := by dsimp [s]; omega
  have hhi : s < 2^53 := by dsimp [s]; omega
  have hehi : e < 2047 := by
    have hm : Wasm.IEEE64.exponent word < 2^11 := Nat.mod_lt _ (by positivity)
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
    dsimp [e]
    omega
  have hm : Wasm.IEEE64.scaledMagnitude word = s*2^(e-1) := by
    simp [Wasm.IEEE64.scaledMagnitude, s, e, show Wasm.IEEE64.exponent word ≠ 0 by omega]
  have hp : Wasm.IEEE64.scaledMagnitude word * Wasm.IEEE64.scaledMagnitude 0x3FE0000000000000 =
      s*2^(1074+(e-2)) := by
    rw [hm]
    change s*2^(e-1)*2^1073 = _
    rw [Nat.mul_assoc, ← pow_add]
    congr 2
    dsimp [e]
    omega
  have hcap : s*2^(e-2) < 2^2097 := by
    calc
      _ < 2^53*2^(e-2) := Nat.mul_lt_mul_of_pos_right hhi (by positivity)
      _ ≤ 2^53*2^2044 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ = 2^2097 := by norm_num
  have hpack := F64Packing.pack_spec (Wasm.IEEE64.sign word) (s*2^(e-2)) hcap
  have hr := F64DyadicBounds.roundedMagnitude_shifted s (e-2) hlo hhi.le
  have hmul : Wasm.IEEE64.mul word 0x3FE0000000000000 =
      Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign word) (s*2^(e-2)) := by
    rw [mul_finite_rounder _ _ hf (by unfold CodeLib.IEEE64.Finite; decide), hp]
    have hsign : Wasm.IEEE64.sign 0x3FE0000000000000 = false := by decide
    simp only [hsign, Bool.bne_false]
    exact dyadic_shifted (Wasm.IEEE64.sign word) s (e-2) hlo hhi
  have htwice : s*2^(e-2)*2 = Wasm.IEEE64.scaledMagnitude word := by
    rw [hm, Nat.mul_assoc, ← pow_succ]
    congr 2
    dsimp [e]
    omega
  rw [hmul]
  refine ⟨hpack.1, hpack.2.2, ?_⟩
  have hsigned : Wasm.IEEE64.scaledValue
      (Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign word) (s*2^(e-2))) * 2 =
      Wasm.IEEE64.scaledValue word := by
    simp only [Wasm.IEEE64.scaledValue, hpack.2.1, hr, hpack.2.2]
    have hi : ((s*2^(e-2) : Nat) : Int)*2 = Wasm.IEEE64.scaledMagnitude word := by
      exact_mod_cast htwice
    cases Wasm.IEEE64.sign word <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · exact hi
    · linarith only [hi]
  have hv : (Wasm.IEEE64.scaledValue
      (Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE64.sign word) (s*2^(e-2))) : ℝ)*2 =
      Wasm.IEEE64.scaledValue word := by exact_mod_cast hsigned
  simp only [value]
  rw [← hv]
  ring

#print axioms half_exact
end Project.ProofKit.F64ExactHalving
