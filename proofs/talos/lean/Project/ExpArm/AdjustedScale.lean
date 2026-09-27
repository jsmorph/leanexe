import Project.ExpArm.ScaledTable

namespace Project.ExpArm
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem word_add_mod (a b : UInt64) :
    ((a+b).toNat : Int) = ((a.toNat : Int)+b.toNat) % 2^64 := by
  rw [UInt64.toNat_add]
  push_cast
  rfl

theorem word_sub_mod (a b : UInt64) :
    ((a-b).toNat : Int) = ((a.toNat : Int)-b.toNat) % 2^64 := by
  have hb : b.toNat ≤ 2^64 := b.toNat_lt.le
  rw [UInt64.toNat_sub]
  push_cast
  omega

theorem positive_scale_value (word : UInt64)
    (he : 1 ≤ 1023+(shiftInteger word/128-1009) ∧
      1023+(shiftInteger word/128-1009) < 2047) :
    let i := (word &&& 127).toNat
    let bits := table[2*i+1]! + (word <<< 45) - ((1009 : UInt64) <<< 52)
    Finite bits ∧ 0 < value bits ∧
    value bits * (2 : ℝ)^1023 =
      value (tableScaleWord i) * (2 : ℝ)^(1023+(shiftInteger word/128-1009)).toNat := by
  have hi : (word &&& 127).toNat < 128 := by
    have h : (word &&& 127).toNat ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    omega
  apply scaled_table_value _ _ _ hi he
  rw [word_sub_mod, scale_word_congruence]
  have hc : (((1009 : UInt64) <<< 52).toNat : Int) = 1009*2^52 := by decide
  rw [hc, Int.emod_sub_emod]
  congr 1
  ring

theorem negative_scale_value (word : UInt64)
    (he : 1 ≤ 1023+(shiftInteger word/128+1022) ∧
      1023+(shiftInteger word/128+1022) < 2047) :
    let i := (word &&& 127).toNat
    let bits := table[2*i+1]! + (word <<< 45) + ((1022 : UInt64) <<< 52)
    Finite bits ∧ 0 < value bits ∧
    value bits * (2 : ℝ)^1023 =
      value (tableScaleWord i) * (2 : ℝ)^(1023+(shiftInteger word/128+1022)).toNat := by
  have hi : (word &&& 127).toNat < 128 := by
    have h : (word &&& 127).toNat ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    omega
  apply scaled_table_value _ _ _ hi he
  rw [word_add_mod, scale_word_congruence]
  have hc : (((1022 : UInt64) <<< 52).toNat : Int) = 1022*2^52 := by decide
  rw [hc, Int.emod_add_emod]
  congr 1
  ring

#print axioms positive_scale_value
#print axioms negative_scale_value
end Project.ExpArm
