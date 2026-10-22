import Library.Numerics.Limiters.Minmod.Program
import Library.Numerics.Limiters.Minmod.Real
import Library.Numerics.Bounds.Proof

namespace Library.Numerics.Limiters.Minmod

open LeanExe.ProofKit Library.Numerics.Bounds
open CodeLib.IEEE64 (value Finite)

noncomputable abbrev real (x : Float) : ℝ := value x.toBits

/-! The rounded minmod is the exact minmod of the inputs' values. -/

theorem value_nonnegative (word : UInt64) (h : word < 0x8000000000000000) : 0 ≤ value word := by
  rw [F64Adjacent.unsigned_word_value word (UInt64.lt_iff_toNat_lt.mp h)]
  positivity

theorem value_nonpositive (word : UInt64) (h : ¬word < 0x8000000000000000) : value word ≤ 0 := by
  have hn : 2^63 ≤ word.toNat := by
    have hn : ¬word.toNat < 2^63 := UInt64.lt_iff_toNat_lt.not.mp h
    exact Nat.le_of_not_gt hn
  rw [F64Adjacent.negative_word_value word hn]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

theorem real_minmod (a b : Float) :
    real (Library.Numerics.Limiters.Minmod.minmod a b) = Library.Numerics.Limiters.Minmod.Real.minmod (real a) (real b) := by
  have hzero : value (0 : UInt64) = 0 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  have horder : ¬Library.Numerics.Bounds.absBits a.toBits ≤ Library.Numerics.Bounds.absBits b.toBits → Library.Numerics.Bounds.absBits b.toBits ≤ Library.Numerics.Bounds.absBits a.toBits := by
    intro h
    rw [UInt64.le_iff_toNat_le] at h ⊢
    omega
  have hmono : ∀ x y : UInt64, Library.Numerics.Bounds.absBits x ≤ Library.Numerics.Bounds.absBits y → |value x| ≤ |value y| :=
    fun x y h => F64Order.abs_value_mono x y h
  simp only [real, Library.Numerics.Limiters.Minmod.minmod]
  by_cases ha : a.toBits < 0x8000000000000000 <;> by_cases hb : b.toBits < 0x8000000000000000
  · have hva := value_nonnegative _ ha
    have hvb := value_nonnegative _ hb
    simp only [ha, hb, decide_true, beq_self_eq_true, ite_true]
    split_ifs with hab
    · have hv := hmono _ _ hab
      rw [abs_of_nonneg hva, abs_of_nonneg hvb] at hv
      simp [Library.Numerics.Limiters.Minmod.Real.minmod, min_eq_left hv, max_eq_right hv, hva, hvb]
    · have hv := hmono _ _ (horder hab)
      rw [abs_of_nonneg hvb, abs_of_nonneg hva] at hv
      simp [Library.Numerics.Limiters.Minmod.Real.minmod, min_eq_right hv, max_eq_left hv, hva, hvb]
  · have hva := value_nonnegative _ ha
    have hvb := value_nonpositive _ hb
    simp [ha, hb, zero_toBits, hzero, Library.Numerics.Limiters.Minmod.Real.minmod, min_eq_right (hvb.trans hva),
      max_eq_left (hvb.trans hva), hva, hvb]
  · have hva := value_nonpositive _ ha
    have hvb := value_nonnegative _ hb
    simp [ha, hb, zero_toBits, hzero, Library.Numerics.Limiters.Minmod.Real.minmod, min_eq_left (hva.trans hvb),
      max_eq_right (hva.trans hvb), hva, hvb]
  · have hva := value_nonpositive _ ha
    have hvb := value_nonpositive _ hb
    simp only [ha, hb, decide_false, beq_self_eq_true, ite_true]
    split_ifs with hab
    · have hv := hmono _ _ hab
      rw [abs_of_nonpos hva, abs_of_nonpos hvb] at hv
      have hba : value b.toBits ≤ value a.toBits := by linarith
      simp [Library.Numerics.Limiters.Minmod.Real.minmod, min_eq_right hba, max_eq_left hba, hva, hvb]
    · have hv := hmono _ _ (horder hab)
      rw [abs_of_nonpos hvb, abs_of_nonpos hva] at hv
      have hab : value a.toBits ≤ value b.toBits := by linarith
      simp [Library.Numerics.Limiters.Minmod.Real.minmod, min_eq_left hab, max_eq_right hab, hva, hvb]

/-! The slope. -/

end Library.Numerics.Limiters.Minmod
