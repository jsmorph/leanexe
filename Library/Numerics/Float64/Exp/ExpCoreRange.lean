import Library.Numerics.Float64.Exp.ExpCoreBounds

namespace Library.Numerics.Float64.Exp.ExpCoreRange
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem checked_head_bounds : ∀ j : Fin 128,
    (Wasm.IEEE64.scaledValue (ExpTableBounds.headBits j.val) : ℚ) / (2 : ℚ) ^ 1074 ≤
      255 / 128 ∧
    (j.val ≠ 0 →
      257 / 256 ≤ (Wasm.IEEE64.scaledValue (ExpTableBounds.headBits j.val) : ℚ) /
        (2 : ℚ) ^ 1074) := by
  decide +kernel

theorem head_bounds (j : Fin 128) :
    value (ExpTableBounds.headBits j.val) ≤ 255 / 128 ∧
    (j.val ≠ 0 → 257 / 256 ≤ value (ExpTableBounds.headBits j.val)) := by
  have hc := checked_head_bounds j
  constructor
  · have h : (((Wasm.IEEE64.scaledValue (ExpTableBounds.headBits j.val) : ℚ) /
        (2 : ℚ) ^ 1074 : ℚ) : ℝ) ≤ ((255 / 128 : ℚ) : ℝ) := Rat.cast_le.mpr hc.1
    simpa [value] using h
  · intro hj
    have h : ((257 / 256 : ℚ) : ℝ) ≤
        (((Wasm.IEEE64.scaledValue (ExpTableBounds.headBits j.val) : ℚ) /
          (2 : ℚ) ^ 1074 : ℚ) : ℝ) := Rat.cast_le.mpr (hc.2 hj)
    simpa [value] using h

theorem zero_entry :
    value (ExpTableBounds.headBits 0) = 1 ∧ value (ExpTableBounds.tailBits 0) = 0 := by
  have hc : (Wasm.IEEE64.scaledValue (ExpTableBounds.headBits 0) : ℚ) / (2 : ℚ) ^ 1074 = 1 ∧
      (Wasm.IEEE64.scaledValue (ExpTableBounds.tailBits 0) : ℚ) / (2 : ℚ) ^ 1074 = 0 := by
    decide +kernel
  constructor
  · have h := congrArg (fun r : ℚ => (r : ℝ)) hc.1
    simpa [value] using h
  · have h := congrArg (fun r : ℚ => (r : ℝ)) hc.2
    simpa [value] using h

theorem ideal_exponential_range (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    319 / 320 ≤ Real.exp (ExpResidualBounds.ideal x) ∧
    Real.exp (ExpResidualBounds.ideal x) ≤ 257 / 256 := by
  let a := ExpResidualBounds.ideal x
  have ha := ExpResidualBounds.ideal_bound x hxf hx
  have hal := (abs_le.mp ha).1
  have hau := (abs_le.mp ha).2
  have he := Real.abs_exp_sub_one_sub_id_le (ha.trans (by norm_num : (1 / 320 : ℝ) ≤ 1))
  have hsq : a ^ 2 ≤ (1 / 320 : ℝ) ^ 2 := by
    rw [← sq_abs]
    gcongr
  constructor
  · have h := Real.add_one_le_exp a
    linarith
  · have h := (le_abs_self (Real.exp a - 1 - a)).trans he
    nlinarith only [h, hsq, hau]

theorem target_factor (x : UInt64) (k q : Int) (j : Fin 128)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) :
    Real.exp (value x) = (2 : ℝ) ^ q *
      Real.exp ((j.val : ℝ) * Real.log 2 / 128) *
      Real.exp (ExpResidualBounds.ideal x) := by
  rw [ExpTableReconstruction.exponential_factor k q j hk, ← Real.exp_add]
  congr 1
  dsimp [ExpResidualBounds.ideal]
  rw [hkv]
  ring

theorem table_exponential_range (j : Fin 128) (hj : j.val ≠ 0) :
    1 + 1 / 4096 ≤ Real.exp ((j.val : ℝ) * Real.log 2 / 128) * (319 / 320) ∧
    Real.exp ((j.val : ℝ) * Real.log 2 / 128) * (257 / 256) ≤ 2 - 1 / 65536 := by
  obtain ⟨hl, hu⟩ := ExpTableBounds.scale_enclosure j
  have ht := (ExpTableBounds.entry_bounds j).2.2.2.2
  have hh := head_bounds j
  have hT := abs_le.mp ht
  have hslo :
      (257 / 256 : ℝ) * (1 - 1 / (2 : ℝ) ^ 53) ≤ ExpTableBounds.scale j.val := by
    exact mul_le_mul (hh.2 hj) (by linarith) (by norm_num) (by linarith [hh.2 hj])
  have hshi :
      ExpTableBounds.scale j.val ≤ (255 / 128 : ℝ) * (1 + 1 / (2 : ℝ) ^ 53) := by
    exact mul_le_mul hh.1 (by linarith) (by linarith) (by norm_num)
  have hel :
      (257 / 256 : ℝ) * (1 - 1 / (2 : ℝ) ^ 53) * (1 - 1 / (2 : ℝ) ^ 100) ≤
        Real.exp ((j.val : ℝ) * Real.log 2 / 128) :=
    (mul_le_mul_of_nonneg_right hslo (by norm_num)).trans hl
  have heu :
      Real.exp ((j.val : ℝ) * Real.log 2 / 128) ≤
        (255 / 128 : ℝ) * (1 + 1 / (2 : ℝ) ^ 53) * (1 + 1 / (2 : ℝ) ^ 100) :=
    hu.trans (mul_le_mul_of_nonneg_right hshi (by norm_num))
  constructor
  · calc
      _ ≤ ((257 / 256 : ℝ) * (1 - 1 / (2 : ℝ) ^ 53) *
          (1 - 1 / (2 : ℝ) ^ 100)) * (319 / 320) := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hel (by norm_num)
  · calc
      _ ≤ ((255 / 128 : ℝ) * (1 + 1 / (2 : ℝ) ^ 53) *
          (1 + 1 / (2 : ℝ) ^ 100)) * (257 / 256) :=
        mul_le_mul_of_nonneg_right heu (by norm_num)
      _ ≤ _ := by norm_num

theorem target_binade (x : UInt64) (k q : Int) (j : Fin 128)
    (hxf : Finite x) (hx : |value x| ≤ 768)
    (hkv : value (ExpReductionSelection.integer x) = (k : ℝ))
    (hk : k = 128 * q + j.val) (hj : j.val ≠ 0) :
    (2 : ℝ) ^ q * (1 + 1 / 4096) ≤ Real.exp (value x) ∧
    Real.exp (value x) ≤ (2 : ℝ) ^ q * (2 - 1 / 65536) := by
  have ha := ideal_exponential_range x hxf hx
  have hjb := table_exponential_range j hj
  have hP : 0 ≤ (2 : ℝ) ^ q := (zpow_pos (by norm_num) _).le
  have hE : 0 ≤ Real.exp ((j.val : ℝ) * Real.log 2 / 128) := (Real.exp_pos _).le
  rw [target_factor x k q j hkv hk]
  constructor
  · calc
      _ ≤ (2 : ℝ) ^ q *
          (Real.exp ((j.val : ℝ) * Real.log 2 / 128) * (319 / 320)) :=
        mul_le_mul_of_nonneg_left hjb.1 hP
      _ ≤ _ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha.1 hE) hP
  · calc
      _ ≤ (2 : ℝ) ^ q *
          (Real.exp ((j.val : ℝ) * Real.log 2 / 128) * (257 / 256)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha.2 hE) hP
      _ ≤ _ := mul_le_mul_of_nonneg_left hjb.2 hP

#print axioms checked_head_bounds
#print axioms head_bounds
#print axioms zero_entry
#print axioms ideal_exponential_range
#print axioms target_factor
#print axioms table_exponential_range
#print axioms target_binade

end Library.Numerics.Float64.Exp.ExpCoreRange
