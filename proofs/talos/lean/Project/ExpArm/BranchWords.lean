import Project.ExpArm.NormalAccuracy
import Project.ExpArm.OuterPaths
import Mathlib.Data.Nat.Bitwise

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

theorem shift_bit31 (word : UInt64) (hk : |shiftInteger word| ≤ 190000) :
    word &&& 0x80000000 = 0 ↔ 0 ≤ shiftInteger word := by
  rw [← UInt64.toNat_inj, UInt64.toNat_and]
  change word.toNat &&& 2^31 = 0 ↔ 0 ≤ shiftInteger word
  rw [Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq]
  have hb := abs_le.mp hk
  by_cases hs : 0 ≤ shiftInteger word
  · have hd : word.toNat/2^31%2 = 0 := by dsimp [shiftInteger] at *; omega
    norm_num at hd
    simp [hd, hs]
  · have hd : word.toNat/2^31%2 = 1 := by dsimp [shiftInteger] at *; omega
    norm_num at hd
    simp [hd, hs]

theorem reduction_sign_bound (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 1024) :
    |shiftInteger (reductionWord x)| ≤ 190000 := by
  have h := reductionInteger_abs x hf hx
  have hk : |(reductionInteger x : ℝ)| ≤ 190000 := by linarith
  exact_mod_cast hk

theorem positive_reduction_sign (x : UInt64) (hf : Finite x)
    (hx : 512 ≤ value x ∧ value x ≤ 1024) : reductionWord x &&& 0x80000000 = 0 := by
  have habs : |value x| ≤ 1024 := abs_le.mpr ⟨by linarith, hx.2⟩
  apply (shift_bit31 _ (reduction_sign_bound x hf habs)).mpr
  have h := abs_le.mp (integer_selection x hf habs).2.2.2.2
  have hi := inverse_log_bounds
  have hp : (0 : ℝ) ≤ (reductionInteger x : ℝ) := by nlinarith
  exact_mod_cast hp

theorem negative_reduction_sign (x : UInt64) (hf : Finite x)
    (hx : -1024 ≤ value x ∧ value x ≤ -512) : reductionWord x &&& 0x80000000 ≠ 0 := by
  have habs : |value x| ≤ 1024 := abs_le.mpr ⟨hx.1, by linarith⟩
  change ¬reductionWord x &&& 0x80000000 = 0
  rw [shift_bit31 _ (reduction_sign_bound x hf habs)]
  have h := abs_le.mp (integer_selection x hf habs).2.2.2.2
  have hi := inverse_log_bounds
  have hp : (reductionInteger x : ℝ) < 0 := by nlinarith
  have hn : reductionInteger x < 0 := by exact_mod_cast hp
  change ¬0 ≤ reductionInteger x
  omega

theorem exp_rescale_path (x : UInt64)
    (hl : 0x4080000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF)
    (hu : x &&& 0x7FFFFFFFFFFFFFFF < 0x4090000000000000) :
    exp x = rescale (pathCorrection x)
      (table[2*(reductionWord x &&& 127).toNat+1]! + (reductionWord x <<< 45)) (reductionWord x) := by
  have ht : ¬x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000 := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  have hb : ¬0x4090000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
    omega
  simp only [exp, ht, hb, hl, ite_false, ite_true, pathCorrection,
    reductionWord, reducedWord, correctionWord, mask_index_nat]

theorem exp_positive_path (x : UInt64)
    (hl : 0x4080000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF)
    (hu : x &&& 0x7FFFFFFFFFFFFFFF < 0x4090000000000000)
    (hk : reductionWord x &&& 0x80000000 = 0) : exp x = positivePath x := by
  rw [exp_rescale_path x hl hu]
  simp only [rescale, hk, beq_self_eq_true, ite_true, positivePath, positiveCore,
    adjustedPath, normalReconstruction, pathCorrection]

theorem exp_negative_path (x : UInt64)
    (hl : 0x4080000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF)
    (hu : x &&& 0x7FFFFFFFFFFFFFFF < 0x4090000000000000)
    (hk : reductionWord x &&& 0x80000000 ≠ 0) : exp x = negativePath x := by
  rw [exp_rescale_path x hl hu]
  by_cases hy : negativeCore x < 0x3FF0000000000000 <;>
    simp only [negativeCore, negativeScale, adjustedPath, normalReconstruction] at hy <;>
    simp only [rescale, beq_iff_eq, hk, ite_false, negativePath, negativeCore,
      negativeScale, adjustedPath, normalReconstruction, pathCorrection, negativeSubnormalPath,
      F64CompensatedSum.roundedSum, hy, ite_true, ite_false]

#print axioms exp_positive_path
#print axioms exp_negative_path
end Project.ExpArm
