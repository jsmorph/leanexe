import Project.ExpArm.ShiftWords
import Project.ExpArm.TableRational

namespace Project.ExpArm
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem index_remainder (word : UInt64) :
    (word &&& 127).toNat = (shiftInteger word % 128).toNat := by
  rw [UInt64.toNat_and]
  change word.toNat &&& (2^7-1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  dsimp [shiftInteger]
  omega

set_option maxRecDepth 4096 in
theorem table_scale_encoding : ∀ i : Fin 128,
    table[2*i.val+1]!.toNat + i.val * 2^45 = (tableScaleWord i).toNat ∧
    1023 * 2^52 ≤ (tableScaleWord i).toNat ∧
    (tableScaleWord i).toNat < 1024 * 2^52 := by
  decide +kernel

theorem shift_add_mod (word base : UInt64) :
    ((base + (word <<< 45)).toNat : Int) =
      ((base.toNat : Int) + (word.toNat : Int)*2^45) % 2^64 := by
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft]
  simp only [UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq]
  push_cast
  omega

theorem scale_word_congruence (word : UInt64) :
    let i := (word &&& 127).toNat
    (((table[2*i+1]! + (word <<< 45)).toNat : Nat) : Int) =
      ((tableScaleWord i).toNat + (shiftInteger word / 128) * (2 : Int)^52) % 2^64 := by
  dsimp only
  let i := (word &&& 127).toNat
  have hi : i < 128 := by
    have h := UInt64.le_iff_toNat_le.mp (UInt64.and_le_right (a := word) (b := 127))
    change (word &&& 127).toNat ≤ 127 at h
    change (word &&& 127).toNat < 128
    omega
  have hb := (table_scale_encoding ⟨i, hi⟩).1
  have hir : i = word.toNat % 128 := by
    dsimp [i]
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod word.toNat 7
  change ((table[2*i+1]! + (word <<< 45)).toNat : Int) =
    ((tableScaleWord i).toNat + (shiftInteger word / 128) * (2 : Int)^52) % 2^64
  rw [shift_add_mod]
  have hb' : (table[2*i+1]!.toNat : Int) + (i : Int)*2^45 = (tableScaleWord i).toNat := by
    exact_mod_cast hb
  have hd : (word.toNat : Int) = (shiftInteger word / 128)*128 + i + 4843621399236968448 := by
    dsimp [shiftInteger]
    omega
  rw [hd]
  have heq : (table[2*i+1]!.toNat : Int) +
      (shiftInteger word / 128 * 128 + i + 4843621399236968448) * 2^45 =
      (tableScaleWord i).toNat + (shiftInteger word / 128)*2^52 +
        170419777568182590163713037172736 := by
    nlinarith only [hb']
  rw [heq]
  omega

theorem encoded_value_scale (e f : Nat) (he : 0 < e) (hu : e < 2047) (hf : f < 2^52) :
    Finite (Wasm.IEEE64.encodeFinite false e f) ∧
    0 < value (Wasm.IEEE64.encodeFinite false e f) ∧
    value (Wasm.IEEE64.encodeFinite false e f) * (2 : ℝ)^1023 =
      value (Wasm.IEEE64.encodeFinite false 1023 f) * (2 : ℝ)^e := by
  have hv (j : Nat) (hjl : 0 < j) (hju : j < 2047) :
      value (Wasm.IEEE64.encodeFinite false j f) =
        (((2^52+f)*2^(j-1) : Nat) : ℝ)/2^1074 := by
    rw [value, scaledValue_encodeFinite false j f (by omega) hf]
    simp [show j ≠ 0 by omega]
  refine ⟨finite_encodeFinite false e f hu hf, ?_, ?_⟩
  · rw [hv e he hu]
    positivity
  · rw [hv e he hu, hv 1023 (by decide) (by decide)]
    push_cast
    have hp : (2 : ℝ)^(e-1) * 2^1023 = (2 : ℝ)^1022 * 2^e := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    calc
      _ = ((2 : ℝ)^52+f) * ((2 : ℝ)^(e-1)*2^1023)/2^1074 := by ring
      _ = ((2 : ℝ)^52+f) * ((2 : ℝ)^1022*2^e)/2^1074 := by rw [hp]
      _ = _ := by ring

#print axioms scale_word_congruence
#print axioms encoded_value_scale
end Project.ExpArm
