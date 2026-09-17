import Project.TinyGpt2.Rows
import Project.Affine.BalancedBounds

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem dotColumn4_error_wide (w : Array UInt64) (offset width : Nat) (j : Fin width)
    (x : Row) (inputBound weightBound : ℝ)
    (hx0 : 0 ≤ inputBound) (hw0 : 0 ≤ weightBound)
    (hmax : inputBound*weightBound+1 ≤ 2^40)
    (hx : ∀ i, Affine.Bounded (rowWords x i) inputBound)
    (hw : ∀ i, Affine.Bounded (matrixWords w offset 4 width i j) weightBound) :
    Approximation (dotColumn4 w offset width j.val x)
      (Real.matrixApply (decodeMatrix w offset 4 width) (decodeRow x) j)
      (4*(inputBound*weightBound+1)+5)
      ((12*(inputBound*weightBound+1)+6)*arithmeticEpsilon) := by
  rw [dotColumn4_model]
  apply Affine.dot4_error_bounded _ _ (inputBound*weightBound+1)
    (by nlinarith) hmax (fun i => (hx i).1) (fun i => (hw i).1)
  intro i
  rw [abs_mul]
  exact (mul_le_mul (hx i).2 (hw i).2 (abs_nonneg _) hx0).trans (by linarith)

theorem dotColumn8_error_wide (w : Array UInt64) (offset width : Nat) (j : Fin width)
    (x : WideRow) (inputBound weightBound : ℝ)
    (hx0 : 0 ≤ inputBound) (hw0 : 0 ≤ weightBound)
    (hmax : inputBound*weightBound+1 ≤ 2^40)
    (hx : ∀ i, Affine.Bounded (wideWords x i) inputBound)
    (hw : ∀ i, Affine.Bounded (matrixWords w offset 8 width i j) weightBound) :
    Approximation (dotColumn8 w offset width j.val x)
      (Real.matrixApply (decodeMatrix w offset 8 width) (fun i => value (wideWords x i)) j)
      (8*(inputBound*weightBound+1)+11)
      ((32*(inputBound*weightBound+1)+22)*arithmeticEpsilon) := by
  rw [dotColumn8_model]
  apply Affine.dot8_error_bounded _ _ (inputBound*weightBound+1)
    (by nlinarith) hmax (fun i => (hx i).1) (fun i => (hw i).1)
  intro i
  rw [abs_mul]
  exact (mul_le_mul (hx i).2 (hw i).2 (abs_nonneg _) hx0).trans (by linarith)

theorem add_error_wide (x y : UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hmax : bound ≤ 2^40)
    (hx : Finite x) (hy : Finite y) (hs : |value x+value y| ≤ bound) :
    Approximation (Wasm.IEEE64.add x y) (value x+value y)
      (bound+1) (bound*arithmeticEpsilon) := by
  have h := F64ArithmeticBounds.add_error x y hx hy bound hb
    (hmax.trans_lt (by norm_num)) hs
  refine ⟨h.1, ?_, by simpa only [mul_comm] using h.2⟩
  exact (F64ArithmeticBounds.magnitude_of_error _ _ _ _ h.2 hs).trans
    (by norm_num [arithmeticEpsilon] at hmax ⊢; linarith)

theorem matrix_input_error {m n : Nat} (weights : Real.Matrix m n)
    (x target : Fin m → ℝ) (bound error : ℝ)
    (he : 0 ≤ error) (hw : ∀ i j, |weights i j| ≤ bound)
    (hx : ∀ i, |x i-target i| ≤ error) (j : Fin n) :
    |Real.matrixApply weights x j-Real.matrixApply weights target j| ≤ m*bound*error := by
  have h := Affine.Real.dot_input_perturbation x target (fun i => weights i j) error hx
  have hs : (∑ i, |weights i j|) ≤ m*bound := by
    calc
      _ ≤ ∑ _ : Fin m, bound := Finset.sum_le_sum (fun i _ => hw i j)
      _ = _ := by simp
  exact h.trans (mul_le_mul_of_nonneg_right hs he)

#print axioms dotColumn4_error_wide
#print axioms dotColumn8_error_wide
#print axioms matrix_input_error
end Project.TinyGpt2
