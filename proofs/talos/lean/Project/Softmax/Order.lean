import Project.Softmax.Model
import Project.ProofKit.F64StrictOrder
import Mathlib.Tactic

namespace Project.Softmax
open CodeLib.IEEE64 Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem value_nonnegative {x : UInt64} (h : x < 0x8000000000000000) : 0 ≤ value x := by
  have hs : Wasm.IEEE64.sign x = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    exact UInt64.lt_iff_toNat_lt.mp h
  simp only [value, Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false, Int.cast_natCast]
  positivity

theorem value_nonpositive {x : UInt64} (h : ¬x < 0x8000000000000000) : value x ≤ 0 := by
  have hs : Wasm.IEEE64.sign x = true := by
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq]
    have hh := UInt64.lt_iff_toNat_lt.not.mp h
    norm_num [UInt64.toNat_ofNat] at hh
    omega
  simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true, Int.cast_neg, Int.cast_natCast]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

theorem same_sign_abs_mono (a b : UInt64)
    (hs : (a < 0x8000000000000000) ↔ (b < 0x8000000000000000)) (hab : a ≤ b) :
    |value a| ≤ |value b| := by
  apply abs_value_mono
  rw [UInt64.le_iff_toNat_le, absBits_toNat, absBits_toNat]
  simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at hs hab
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  change (a.toNat < 2^63 ↔ b.toNat < 2^63) at hs
  change a.toNat % 2^63 ≤ b.toNat % 2^63
  omega

theorem maximum_value (a b : UInt64) : value (maximum a b) = max (value a) (value b) := by
  unfold maximum
  by_cases ha : a < 0x8000000000000000
  · by_cases hb : b < 0x8000000000000000
    · have va := value_nonnegative ha
      have vb := value_nonnegative hb
      by_cases hab : a ≤ b
      · have h := same_sign_abs_mono a b (by simp [ha, hb]) hab
        rw [abs_of_nonneg va, abs_of_nonneg vb] at h
        simp [ha, hb, hab, max_eq_right h]
      · have h := same_sign_abs_mono b a (by simp [ha, hb])
          (by rw [UInt64.le_iff_toNat_le]; rw [UInt64.le_iff_toNat_le] at hab; omega)
        rw [abs_of_nonneg va, abs_of_nonneg vb] at h
        simp [ha, hb, hab, max_eq_left h]
    · simp [ha, hb, max_eq_left ((value_nonpositive hb).trans (value_nonnegative ha))]
  · by_cases hb : b < 0x8000000000000000
    · simp [ha, hb, max_eq_right ((value_nonpositive ha).trans (value_nonnegative hb))]
    · have va := value_nonpositive ha
      have vb := value_nonpositive hb
      by_cases hab : a ≤ b
      · have h := same_sign_abs_mono a b (by simp [ha, hb]) hab
        rw [abs_of_nonpos va, abs_of_nonpos vb] at h
        simp [ha, hb, hab, max_eq_left (by linarith : value b ≤ value a)]
      · have h := same_sign_abs_mono b a (by simp [ha, hb])
          (by rw [UInt64.le_iff_toNat_le]; rw [UInt64.le_iff_toNat_le] at hab; omega)
        rw [abs_of_nonpos va, abs_of_nonpos vb] at h
        simp [ha, hb, hab, max_eq_right (by linarith : value a ≤ value b)]

theorem maximum_choice (a b : UInt64) : maximum a b = a ∨ maximum a b = b := by
  unfold maximum
  split <;> split <;> first | (split <;> simp) | simp

theorem four_value : value 0x4010000000000000 = 4 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem bounded_iff (x : UInt64) : bounded x = true ↔ Finite x ∧ |value x| ≤ 4 := by
  have hc : absBits 0x4010000000000000 = 0x4010000000000000 := by decide
  constructor
  · intro h
    have hb : absBits x ≤ 0x4010000000000000 := by simpa [bounded, absBits] using h
    have hf : Finite x := (finiteBits_iff x).mp (by
      simp only [finiteBits, decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
      have hh := UInt64.le_iff_toNat_le.mp hb
      norm_num [UInt64.toNat_ofNat] at hh ⊢
      omega)
    have hm := abs_value_mono x 0x4010000000000000 (by rw [hc]; exact hb)
    exact ⟨hf, by simpa [four_value] using hm⟩
  · rintro ⟨_, h⟩
    suffices absBits x ≤ 0x4010000000000000 by simpa [bounded, absBits] using this
    by_contra hn
    have hh : absBits 0x4010000000000000 < absBits x := by
      rw [hc, UInt64.lt_iff_toNat_lt]
      rw [UInt64.le_iff_toNat_le] at hn
      omega
    have hm := abs_value_lt _ _ hh
    rw [four_value, show |(4:ℝ)| = 4 by norm_num] at hm
    linarith

#print axioms maximum_value
#print axioms bounded_iff
end Project.Softmax
