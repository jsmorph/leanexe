import Project.Beck.Arithmetic
import Mathlib.Data.UInt
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

namespace Project.Beck.Determinant

open LeanExe.Examples.Beck
open scoped UInt64.CommRing

theorem omit_size (xs : Array UInt64) (j : Nat) (hj : j < xs.size) :
    (omitIndex xs j).size = xs.size - 1 := by
  simp [omitIndex, ← Array.eraseIdx_eq_eraseIdxIfInBounds hj]

theorem omit_get (k : Nat) (xs : Array UInt64) (size : xs.size = k + 1)
    (j : Fin (k + 1)) (i : Fin k) :
    (omitIndex xs j.val)[i.val]! = xs[(j.succAbove i).val]! := by
  have hj : j.val < xs.size := by omega
  have hi : i.val < (xs.eraseIdx j.val hj).size := by simp; omega
  simp only [omitIndex, ← Array.eraseIdx_eq_eraseIdxIfInBounds hj,
    getElem!_pos (xs.eraseIdx j.val hj) i.val hi, Array.getElem_eraseIdx, Fin.succAbove]
  split_ifs <;> simp_all [getElem!_pos, Fin.lt_def]
  all_goals omega

theorem signed_term (j : Nat) (a b acc : UInt64) :
    (if a != 0 then if j % 2 == 0 then acc + a * b else acc - a * b else acc) =
      acc + (-1) ^ j * a * b := by
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases ha : a = 0
  · simp [ha]
  · by_cases hj : j % 2 = 0
    · simp [ha, hj]
    · have hmod : j % 2 = 1 := by omega
      simp [ha, hmod, sub_eq_add_neg]

theorem determinant_succ (k width : Nat) (matrix rows columns : Array UInt64) :
    determinant (k + 1) width matrix rows columns =
      ((List.range columns.size).map fun j => (-1 : UInt64) ^ j *
        matrix[rows[0]!.toNat * width + columns[j]!.toNat]! *
        determinant k width matrix (omitIndex rows 0) (omitIndex columns j)).sum := by
  have loop_eq (f : Nat → UInt64 → UInt64) :
      (forIn (List.range columns.size) 0 (fun j acc => ForInStep.yield (f j acc)) : Id UInt64) =
        (List.range columns.size).foldl (fun acc j => f j acc) 0 :=
    List.forIn_pure_yield_eq_foldl (m := Id) f 0
  simp only [determinant, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp only [Id.run, bind, pure, ← apply_ite ForInStep.yield, loop_eq]
  simp only [List.sum_eq_foldl, List.foldl_map]
  congr 1
  funext acc j
  exact signed_term j _ _ acc

def minor (k width : Nat) (matrix rows columns : Array UInt64) :
    Matrix (Fin k) (Fin k) UInt64 :=
  fun i j => matrix[rows[i.val]!.toNat * width + columns[j.val]!.toNat]!

theorem determinant_eq (k width : Nat) (matrix rows columns : Array UInt64)
    (hr : rows.size = k) (hc : columns.size = k) :
    determinant k width matrix rows columns = (minor k width matrix rows columns).det := by
  induction k generalizing rows columns with
  | zero => simp [determinant, Matrix.det_isEmpty]
  | succ k ih =>
    rw [determinant_succ, Matrix.det_succ_row_zero]
    rw [hc, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
      Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih _ _ (by rw [omit_size _ _ (by omega), hr]; omega)
      (by rw [omit_size _ _ (by omega), hc]; omega)]
    congr 2
    ext i l
    have hrow : (omitIndex rows 0)[i.val]! = rows[i.succ.val]! := by
      simpa using omit_get k rows hr 0 i
    simp only [minor, Matrix.submatrix_apply, hrow, omit_get k columns hc j l]

theorem zero_one_bound {k : Nat} (A : Matrix (Fin k) (Fin k) ℤ)
    (entries : ∀ i j, A i j = 0 ∨ A i j = 1) : |A.det| ≤ k.factorial := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := (1 : ℤ))
    (A := A) (by intro i j; rcases entries i j with h | h <;> simp [h])
  simpa using h

theorem cast_value (x : UInt64) : (Arithmetic.value x : UInt64) = x := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [Arithmetic.value, UInt64.toBitVec_intCast]
  exact BitVec.ofInt_toInt

theorem value_ne_zero (x : UInt64) : Arithmetic.value x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · intro h zero
    simp [zero, Arithmetic.value] at h
  · intro h zero
    apply h
    rw [← cast_value x, zero]
    rfl

theorem value_cast (z : ℤ) (bound : Arithmetic.Fits z) :
    Arithmetic.value (z : UInt64) = z := by
  simp only [Arithmetic.value, UInt64.toBitVec_intCast, BitVec.toInt_intCast]
  exact Arithmetic.bmod_exact z bound

theorem determinant_exact (k width : Nat) (matrix rows columns : Array UInt64)
    (hr : rows.size = k) (hc : columns.size = k)
    (bound : Arithmetic.Fits ((minor k width matrix rows columns).map Arithmetic.value).det) :
    Arithmetic.value (determinant k width matrix rows columns) =
      ((minor k width matrix rows columns).map Arithmetic.value).det := by
  rw [determinant_eq k width matrix rows columns hr hc]
  have casted : (((minor k width matrix rows columns).map Arithmetic.value).det : UInt64) =
      (minor k width matrix rows columns).det := by
    rw [Int.cast_det]
    congr 1
    ext i j
    simp [cast_value]
  rw [← casted, value_cast _ bound]

theorem determinant_small_binary (k width : Nat) (matrix rows columns : Array UInt64)
    (hr : rows.size = k) (hc : columns.size = k) (hk : k ≤ 5)
    (binary : ∀ i j, minor k width matrix rows columns i j = 0 ∨
      minor k width matrix rows columns i j = 1) :
    Arithmetic.value (determinant k width matrix rows columns) =
      ((minor k width matrix rows columns).map Arithmetic.value).det ∧
      |Arithmetic.value (determinant k width matrix rows columns)| ≤ 120 := by
  have hb := zero_one_bound ((minor k width matrix rows columns).map Arithmetic.value)
    (by intro i j; rcases binary i j with h | h <;> simp [h, Arithmetic.value])
  have hf : (k.factorial : ℤ) ≤ 120 := by
    exact_mod_cast (Nat.factorial_le hk : k.factorial ≤ Nat.factorial 5)
  have bound : Arithmetic.Fits ((minor k width matrix rows columns).map Arithmetic.value).det := by
    dsimp [Arithmetic.Fits]
    rw [abs_le] at hb
    omega
  exact ⟨determinant_exact k width matrix rows columns hr hc bound,
    (determinant_exact k width matrix rows columns hr hc bound) ▸ hb.trans hf⟩

end Project.Beck.Determinant
