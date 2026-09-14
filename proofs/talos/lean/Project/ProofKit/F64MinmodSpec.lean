import Project.ProofKit.F64Minmod
import Project.ProofKit.F64AdjacentSigned
import Project.ProofKit.RealMinmod

namespace Project.ProofKit.F64Minmod
open Project.ProofKit.F64Order
open CodeLib.IEEE64

theorem value_nonnegative (word : UInt64) (h : word < 0x8000000000000000) :
    0 ≤ value word := by
  rw [F64Adjacent.unsigned_word_value word (UInt64.lt_iff_toNat_lt.mp h)]
  positivity

theorem value_nonpositive (word : UInt64) (h : ¬word < 0x8000000000000000) :
    value word ≤ 0 := by
  have hn : 2^63 ≤ word.toNat := by
    have hn : ¬word.toNat < 2^63 := UInt64.lt_iff_toNat_lt.not.mp h
    exact Nat.le_of_not_gt hn
  rw [F64Adjacent.negative_word_value word hn]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

theorem minmod_finite (a b : UInt64) (ha : CodeLib.IEEE64.Finite a)
    (hb : CodeLib.IEEE64.Finite b) : CodeLib.IEEE64.Finite (minmod a b) := by
  unfold minmod
  split_ifs <;> first | exact ha | exact hb | unfold CodeLib.IEEE64.Finite; decide

theorem minmod_value (a b : UInt64) :
    value (minmod a b) = RealMinmod.minmod (value a) (value b) := by
  have hzero : value (0 : UInt64) = 0 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  have horder : ¬absBits a ≤ absBits b → absBits b ≤ absBits a := by
    intro h
    rw [UInt64.le_iff_toNat_le] at h ⊢
    omega
  by_cases ha : a < 0x8000000000000000 <;>
    by_cases hb : b < 0x8000000000000000
  · have hva := value_nonnegative a ha
    have hvb := value_nonnegative b hb
    simp only [minmod, ha, hb, decide_true, beq_self_eq_true, ite_true]
    split_ifs with hab
    · have hv := abs_value_mono a b hab
      rw [abs_of_nonneg hva, abs_of_nonneg hvb] at hv
      simp [RealMinmod.minmod, min_eq_left hv, max_eq_right hv, hva, hvb]
    · have hv := abs_value_mono b a (horder hab)
      rw [abs_of_nonneg hvb, abs_of_nonneg hva] at hv
      simp [RealMinmod.minmod, min_eq_right hv, max_eq_left hv, hva, hvb]
  · have hva := value_nonnegative a ha
    have hvb := value_nonpositive b hb
    simp [minmod, ha, hb, hzero, RealMinmod.minmod,
      min_eq_right (hvb.trans hva), max_eq_left (hvb.trans hva), hva, hvb]
  · have hva := value_nonpositive a ha
    have hvb := value_nonnegative b hb
    simp [minmod, ha, hb, hzero, RealMinmod.minmod,
      min_eq_left (hva.trans hvb), max_eq_right (hva.trans hvb), hva, hvb]
  · have hva := value_nonpositive a ha
    have hvb := value_nonpositive b hb
    simp only [minmod, ha, hb, decide_false, beq_self_eq_true, ite_true]
    split_ifs with hab
    · have hv := abs_value_mono a b hab
      rw [abs_of_nonpos hva, abs_of_nonpos hvb] at hv
      have hba : value b ≤ value a := by linarith
      simp [RealMinmod.minmod, min_eq_right hba, max_eq_left hba, hva, hvb]
    · have hv := abs_value_mono b a (horder hab)
      rw [abs_of_nonpos hvb, abs_of_nonpos hva] at hv
      have hab : value a ≤ value b := by linarith
      simp [RealMinmod.minmod, min_eq_left hab, max_eq_right hab, hva, hvb]

#print axioms minmod_finite
#print axioms minmod_value

end Project.ProofKit.F64Minmod
