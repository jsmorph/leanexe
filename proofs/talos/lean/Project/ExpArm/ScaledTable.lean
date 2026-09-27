import Project.ExpArm.ScaleWords

namespace Project.ExpArm
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem normal_word_of_congruence (bits base : UInt64) (m : Int)
    (hbase : 1023*2^52 ≤ base.toNat ∧ base.toNat < 1024*2^52)
    (he : 1 ≤ 1023+m ∧ 1023+m < 2047)
    (hbits : (bits.toNat : Int) = ((base.toNat : Int)+m*2^52) % 2^64) :
    bits = Wasm.IEEE64.encodeFinite false (1023+m).toNat (base.toNat % 2^52) := by
  have hf : base.toNat % 2^52 < 2^52 := Nat.mod_lt _ (by positivity)
  have hb : base.toNat = 1023*2^52 + base.toNat % 2^52 := by omega
  have hlow : 0 ≤ (base.toNat : Int)+m*2^52 := by omega
  have hhigh : (base.toNat : Int)+m*2^52 < 2^64 := by omega
  rw [Int.emod_eq_of_lt hlow hhigh] at hbits
  apply UInt64.toNat_inj.mp
  simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, Nat.zero_add,
    UInt64.toNat_ofNat']
  omega

theorem base_word_encoding (base : UInt64)
    (hb : 1023*2^52 ≤ base.toNat ∧ base.toNat < 1024*2^52) :
    base = Wasm.IEEE64.encodeFinite false 1023 (base.toNat % 2^52) := by
  apply normal_word_of_congruence base base 0 hb (by norm_num)
  have hlt := base.toNat_lt
  simp only [Int.zero_mul, add_zero]
  apply (Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt)).symm

theorem scaled_table_value (bits : UInt64) (i : Nat) (m : Int) (hi : i < 128)
    (he : 1 ≤ 1023+m ∧ 1023+m < 2047)
    (hbits : (bits.toNat : Int) = ((tableScaleWord i).toNat+m*2^52) % 2^64) :
    Finite bits ∧ 0 < value bits ∧
    value bits * (2 : ℝ)^1023 = value (tableScaleWord i) * (2 : ℝ)^(1023+m).toNat := by
  have hb := (table_scale_encoding ⟨i, hi⟩).2
  have hs := normal_word_of_congruence bits (tableScaleWord i) m hb he hbits
  have hf : (tableScaleWord i).toNat % 2^52 < 2^52 := Nat.mod_lt _ (by positivity)
  have hv := encoded_value_scale (1023+m).toNat ((tableScaleWord i).toNat % 2^52)
    (by omega) (by omega) hf
  rw [← base_word_encoding (tableScaleWord i) hb, ← hs] at hv
  exact hv

theorem unadjusted_scale_value (word : UInt64)
    (he : 1 ≤ 1023+shiftInteger word/128 ∧ 1023+shiftInteger word/128 < 2047) :
    let i := (word &&& 127).toNat
    let bits := table[2*i+1]! + (word <<< 45)
    Finite bits ∧ 0 < value bits ∧
    value bits * (2 : ℝ)^1023 =
      value (tableScaleWord i) * (2 : ℝ)^(1023+shiftInteger word/128).toNat := by
  have hi : (word &&& 127).toNat < 128 := by
    have h : (word &&& 127).toNat ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    omega
  exact scaled_table_value _ _ _ hi he (scale_word_congruence word)

#print axioms scaled_table_value
#print axioms unadjusted_scale_value
end Project.ExpArm
