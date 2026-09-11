import Project.ProofKit.F64Bounds
import Project.ProofKit.F64Order

namespace Project.ProofKit.F64Normalize
open CodeLib.IEEE64
open Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

def exponentBits (bits : UInt64) : UInt64 := absBits bits / 0x0010000000000000

def normalizedMagnitude (bits top : UInt64) : UInt64 :=
  if absBits bits == 0 then 0
  else (exponentBits bits + 1021 - top) * 0x0010000000000000 +
    absBits bits % 0x0010000000000000

theorem exponentBits_toNat (bits : UInt64) :
    (exponentBits bits).toNat = Wasm.IEEE64.exponent bits := by
  simp only [exponentBits, UInt64.toNat_div]
  exact (exponent_abs bits).symm

theorem normalizedMagnitude_eq (bits top : UInt64)
    (hz : absBits bits ≠ 0)
    (he : 0 < Wasm.IEEE64.exponent bits)
    (ht : top.toNat ≤ 2046)
    (hle : Wasm.IEEE64.exponent bits ≤ top.toNat)
    (hlo : top.toNat < Wasm.IEEE64.exponent bits + 1021) :
    normalizedMagnitude bits top = Wasm.IEEE64.encodeFinite false
      (Wasm.IEEE64.exponent bits + 1021 - top.toNat) (Wasm.IEEE64.fraction bits) := by
  have hadd : (exponentBits bits + 1021).toNat = Wasm.IEEE64.exponent bits + 1021 := by
    rw [UInt64.toNat_add, exponentBits_toNat]
    change (Wasm.IEEE64.exponent bits + 1021) % 2^64 = Wasm.IEEE64.exponent bits + 1021
    omega
  have hsub : top ≤ exponentBits bits + 1021 := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hadd]
    omega
  have hn : 0 < Wasm.IEEE64.exponent bits + 1021 - top.toNat ∧
      Wasm.IEEE64.exponent bits + 1021 - top.toNat ≤ 1021 := by omega
  have hf : Wasm.IEEE64.fraction bits < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  apply UInt64.toNat_inj.mp
  simp only [normalizedMagnitude, beq_iff_eq, hz, ite_false,
    UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub_of_le _ _ hsub,
    hadd, UInt64.toNat_mod]
  change (((Wasm.IEEE64.exponent bits + 1021 - top.toNat) * 2^52) % 2^64 +
    (absBits bits).toNat % 2^52) % 2^64 = _
  rw [← fraction_abs]
  simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add]
  norm_num

theorem abs_value_scaledMagnitude (bits : UInt64) :
    |value bits| = (Wasm.IEEE64.scaledMagnitude bits : ℝ) / (2 : ℝ)^1074 := by
  simp only [value, abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ)^1074)]
  congr 1
  simp only [Wasm.IEEE64.scaledValue]
  split <;> simp

theorem normalizedMagnitude_spec (bits top : UInt64)
    (ht : top.toNat ≤ 2046)
    (hle : Wasm.IEEE64.exponent bits ≤ top.toNat)
    (hn : absBits bits = 0 ∨
      (0 < Wasm.IEEE64.exponent bits ∧ top.toNat < Wasm.IEEE64.exponent bits + 1021)) :
    Finite (normalizedMagnitude bits top) ∧
      |value (normalizedMagnitude bits top)| ≤ 1 / 2 ∧
      value (normalizedMagnitude bits top) * (2 : ℝ)^top.toNat =
        |value bits| * (2 : ℝ)^1021 := by
  rcases hn with hz | ⟨he, hlo⟩
  · have hb : Wasm.IEEE64.scaledMagnitude bits = 0 := by
      simp [Wasm.IEEE64.scaledMagnitude, exponent_abs, fraction_abs, hz]
    have hnz : normalizedMagnitude bits top = 0 := by simp [normalizedMagnitude, hz]
    rw [hnz, abs_value_scaledMagnitude bits, hb]
    norm_num [CodeLib.IEEE64.Finite, value, Wasm.IEEE64.isFinite, Wasm.IEEE64.scaledValue,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
      Wasm.IEEE64.sign]
  · have hz : absBits bits ≠ 0 := by
      intro hz
      rw [exponent_abs, hz] at he
      norm_num at he
    rw [normalizedMagnitude_eq bits top hz he ht hle hlo]
    let e := Wasm.IEEE64.exponent bits + 1021 - top.toNat
    let f := Wasm.IEEE64.fraction bits
    have he' : 0 < e ∧ e ≤ 1021 := by dsimp [e]; omega
    have hf : f < 2^52 := Nat.mod_lt _ (by positivity)
    have hfinite := finite_encodeFinite false e f (by omega) hf
    have hvalue : value (Wasm.IEEE64.encodeFinite false e f) =
        ((2^52 + f : Nat) : ℝ) * (2 : ℝ)^(e-1) / (2 : ℝ)^1074 := by
      rw [value, scaledValue_encodeFinite false e f (by omega) hf]
      simp [show e ≠ 0 by omega, Nat.cast_mul, Nat.cast_pow]
    have hbound : |value (Wasm.IEEE64.encodeFinite false e f)| ≤ 1 / 2 := by
      apply (Project.ProofKit.F64Bounds.boundedByHalf_spec _ ?_).2
      simp only [Project.ProofKit.F64Bounds.boundedByHalfBits, decide_eq_true_eq]
      apply UInt64.le_iff_toNat_le.mpr
      change (absBits (Wasm.IEEE64.encodeFinite false e f)).toNat ≤ _
      rw [absBits_toNat]
      simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add, UInt64.toNat_ofNat]
      norm_num
      omega
    refine ⟨hfinite, hbound, ?_⟩
    rw [hvalue, abs_value_scaledMagnitude]
    have hmag : Wasm.IEEE64.scaledMagnitude bits =
        (2^52 + f) * 2^(Wasm.IEEE64.exponent bits - 1) := by
      simp [Wasm.IEEE64.scaledMagnitude, show Wasm.IEEE64.exponent bits ≠ 0 by omega, f]
    rw [hmag]
    push_cast
    have hexp : e - 1 + top.toNat = Wasm.IEEE64.exponent bits - 1 + 1021 := by dsimp [e]; omega
    have hpow : (2 : ℝ)^(e-1) * 2^top.toNat =
        (2 : ℝ)^(Wasm.IEEE64.exponent bits-1) * 2^1021 := by
      rw [← pow_add, ← pow_add, hexp]
    calc
      _ = (((2 : ℝ)^52 + f) * ((2 : ℝ)^(e-1) * 2^top.toNat)) / (2 : ℝ)^1074 := by ring
      _ = (((2 : ℝ)^52 + f) * ((2 : ℝ)^(Wasm.IEEE64.exponent bits-1) * 2^1021)) / (2 : ℝ)^1074 := by rw [hpow]
      _ = _ := by ring

#print axioms normalizedMagnitude_spec
end Project.ProofKit.F64Normalize
