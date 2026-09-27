import Project.ProofKit.F64OneSubtract
import Project.ProofKit.F64PowerRounding

namespace Project.ProofKit.F64OneAdd
open CodeLib.IEEE64 F64Order

set_option exponentiation.threshold 4096

theorem one_value : value 0x3FF0000000000000 = 1 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
    Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem interval_of_near (a : UInt64) (ha : Finite a)
    (hl : 1-1/(2 : ℝ)^53 < value a) (hu : value a < 2+1/(2 : ℝ)^51) :
    0x3FF0000000000000 ≤ a ∧ a ≤ 0x4000000000000000 := by
  have hp := positiveBits_of_finite_value_pos a ha (by linarith)
  have hvlo : value 0x3FEFFFFFFFFFFFFF = 1-1/(2 : ℝ)^53 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hvhi : value 0x4000000000000001 = 2+1/(2 : ℝ)^51 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hlow : 0x3FEFFFFFFFFFFFFF < a :=
    (positive_word_lt_iff _ _ (by decide) hp).mpr (by rwa [hvlo])
  have hhigh : a < 0x4000000000000001 :=
    (positive_word_lt_iff _ _ hp (by decide)).mpr (by rwa [hvhi])
  simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
    UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
  omega

theorem add_interval (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hl : 1 ≤ value a+value b) (hu : value a+value b ≤ 2+1/(2 : ℝ)^53) :
    Finite (Wasm.IEEE64.add a b) ∧
    0x3FF0000000000000 ≤ Wasm.IEEE64.add a b ∧
    Wasm.IEEE64.add a b ≤ 0x4000000000000000 ∧
    |value (Wasm.IEEE64.add a b)-(value a+value b)| ≤ 1/(2 : ℝ)^53 := by
  have h : Finite (Wasm.IEEE64.add a b) ∧
      1-1/(2 : ℝ)^53 < value (Wasm.IEEE64.add a b) ∧
      value (Wasm.IEEE64.add a b) < 2+1/(2 : ℝ)^51 ∧
      |value (Wasm.IEEE64.add a b)-(value a+value b)| ≤ 1/(2 : ℝ)^53 := by
    by_cases hlo : value a+value b < 1+1/(2 : ℝ)^53
    · have hp := F64PowerRounding.add_above_power a b ha hb 1074 (by decide) (by decide)
        (by norm_num; exact hl) (by norm_num at *; exact hlo)
      norm_num at hp
      rw [hp.2]
      refine ⟨hp.1, by norm_num, by norm_num, ?_⟩
      rw [abs_of_nonpos (by linarith)]
      linarith
    · by_cases hhi : 2 ≤ value a+value b
      · have hp := F64PowerRounding.add_above_power a b ha hb 1075 (by decide) (by decide)
          (by norm_num; exact hhi) (by norm_num at *; linarith)
        norm_num at hp
        rw [hp.2]
        refine ⟨hp.1, by norm_num, by norm_num, ?_⟩
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hp := F64AddUlp.add_real_binade a b ha hb 1 (by decide)
          (by rw [abs_of_nonneg (by linarith)]; norm_num; linarith)
        norm_num at hp
        have he := abs_le.mp hp.2
        refine ⟨hp.1, by linarith, by linarith, ?_⟩
        norm_num
        exact hp.2
  have hw := interval_of_near _ h.1 h.2.1 h.2.2.1
  exact ⟨h.1, hw.1, hw.2, h.2.2.2⟩

theorem below_one_value (a : UInt64) (ha : a < 0x3FF0000000000000) :
    value a ≤ 1-1/(2 : ℝ)^53 := by
  have hw : absBits a ≤ absBits 0x3FEFFFFFFFFFFFFF := by
    have h := UInt64.and_le_left (a := a) (b := 0x7FFFFFFFFFFFFFFF)
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    change (absBits a).toNat ≤ 0x3FEFFFFFFFFFFFFF
    change (absBits a).toNat ≤ a.toNat at h
    change a.toNat < 0x3FF0000000000000 at ha
    omega
  have h := abs_value_mono a 0x3FEFFFFFFFFFFFFF hw
  have hv : value 0x3FEFFFFFFFFFFFFF = 1-1/(2 : ℝ)^53 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.sign,
      Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  rw [hv, abs_of_pos (by norm_num : (0 : ℝ) < 1-1/2^53)] at h
  exact (le_abs_self _).trans h

theorem add_one (y : UInt64) (hy : Finite y) (hl : 0 < value y) (hu : value y ≤ 1) :
    let h := Wasm.IEEE64.add 0x3FF0000000000000 y
    Finite h ∧ 0x3FF0000000000000 ≤ h ∧ h ≤ 0x4000000000000000 ∧
      1 ≤ value h ∧ value h ≤ 1+2*value y ∧
      |value h-(1+value y)| ≤ 1/(2 : ℝ)^53 := by
  have h := add_interval 0x3FF0000000000000 y (by rfl) hy
    (by rw [one_value]; linarith) (by rw [one_value]; linarith)
  rw [one_value] at h
  have hv : 1 ≤ value (Wasm.IEEE64.add 0x3FF0000000000000 y) ∧
      value (Wasm.IEEE64.add 0x3FF0000000000000 y) ≤ 1+2*value y := by
    by_cases hc : value y < 1/(2 : ℝ)^53
    · have hp := F64PowerRounding.add_above_power 0x3FF0000000000000 y (by rfl) hy
        1074 (by decide) (by decide)
        (by rw [one_value]; norm_num; linarith)
        (by
          rw [one_value]
          have heq : ((2 : ℝ)^1074+2^(1074-53 : Nat))/2^1074 = 1+1/(2 : ℝ)^53 := by norm_num
          rw [heq]
          linarith)
      have hpv : value (Wasm.IEEE64.add 0x3FF0000000000000 y) = 1 := by simpa using hp.2
      rw [hpv]
      constructor <;> linarith
    · have he := abs_le.mp h.2.2.2
      constructor <;> linarith
  exact ⟨h.1, h.2.1, h.2.2.1, hv.1, hv.2, h.2.2.2⟩

#print axioms add_interval
#print axioms add_one
end Project.ProofKit.F64OneAdd
