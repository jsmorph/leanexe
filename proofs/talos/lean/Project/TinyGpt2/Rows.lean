import Project.TinyGpt2.Decoding
import Project.Affine.Numerical
import Project.LayerNorm.Bounds
import Project.Gelu.AllFinite

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem dotColumn4_model (w : Array UInt64) (offset width : Nat) (j : Fin width) (x : Row) :
    dotColumn4 w offset width j.val x =
      Affine.dot4 (rowWords x 0) (rowWords x 1) (rowWords x 2) (rowWords x 3)
        (matrixWords w offset 4 width 0 j) (matrixWords w offset 4 width 1 j)
        (matrixWords w offset 4 width 2 j) (matrixWords w offset 4 width 3 j) := by
  simp [dotColumn4, rowWords, matrixWords]

theorem dotColumn8_model (w : Array UInt64) (offset width : Nat) (j : Fin width) (x : WideRow) :
    dotColumn8 w offset width j.val x =
      Affine.dot8 (wideWords x 0) (wideWords x 1) (wideWords x 2) (wideWords x 3)
        (wideWords x 4) (wideWords x 5) (wideWords x 6) (wideWords x 7)
        (matrixWords w offset 8 width 0 j) (matrixWords w offset 8 width 1 j)
        (matrixWords w offset 8 width 2 j) (matrixWords w offset 8 width 3 j)
        (matrixWords w offset 8 width 4 j) (matrixWords w offset 8 width 5 j)
        (matrixWords w offset 8 width 6 j) (matrixWords w offset 8 width 7 j) := by
  simp [dotColumn8, wideWords, matrixWords]

theorem addRows_error (x y : Row)
    (hx : ∀ j, Affine.Bounded (rowWords x j) 64)
    (hy : ∀ j, Affine.Bounded (rowWords y j) 64) (i : Fin 4) :
    Approximation (rowWords (addRows x y) i) (decodeRow x i+decodeRow y i)
      129 (128*arithmeticEpsilon) := by
  have h := (Approximation.exact _ (hx i).1 64 (hx i).2).add
    (Approximation.exact _ (hy i).1 64 (hy i).2)
    (bound := 128) (by norm_num) (by norm_num) (by norm_num)
  have hh := h.weaken (b' := 129) (e' := 128*arithmeticEpsilon)
    (by norm_num [arithmeticEpsilon]) (by ring_nf; rfl)
  fin_cases i <;> exact hh

theorem dotColumn4_error (w : Array UInt64) (offset width : Nat) (j : Fin width) (x : Row)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 64)
    (hw : ∀ i, Affine.Bounded (matrixWords w offset 4 width i j) 16) :
    Approximation (dotColumn4 w offset width j.val x)
      (Real.matrixApply (decodeMatrix w offset 4 width) (decodeRow x) j)
      4101 (12294*arithmeticEpsilon) := by
  rw [dotColumn4_model]
  exact Affine.dot4_error (rowWords x) (fun i => matrixWords w offset 4 width i j) hx hw

theorem dotColumn8_error (w : Array UInt64) (offset width : Nat) (j : Fin width) (x : WideRow)
    (hx : ∀ i, Affine.Bounded (wideWords x i) 64)
    (hw : ∀ i, Affine.Bounded (matrixWords w offset 8 width i j) 16) :
    Approximation (dotColumn8 w offset width j.val x)
      (Real.matrixApply (decodeMatrix w offset 8 width) (fun i => value (wideWords x i)) j)
      8203 (32790*arithmeticEpsilon) := by
  rw [dotColumn8_model]
  exact Affine.dot8_error (wideWords x) (fun i => matrixWords w offset 8 width i j) hx hw

theorem norm_error (w : Array UInt64) (offset : Nat) (x : Row)
    (hx : LayerNorm.ValidRow (rowWords x))
    (hg : LayerNorm.ValidRow (rowWords (loadRow w offset)))
    (hb : LayerNorm.ValidRow (rowWords (loadRow w (offset+4)))) (i : Fin 4) :
    Finite (rowWords (norm w offset x) i) ∧
      |decodeRow (norm w offset x) i-Real.norm (decodeNorm w offset) (decodeRow x) i| ≤
        1/1000000 := by
  let g := loadRow w offset
  let b := loadRow w (offset+4)
  have h := LayerNorm.compute_numerical x.x0 x.x1 x.x2 x.x3
    g.x0 g.x1 g.x2 g.x3 b.x0 b.x1 b.x2 b.x3 ⟨hx, hg, hb⟩
  have hi := h.2 i
  fin_cases i <;> exact hi

theorem activate_error (x : Row) (hx : ∀ j, Finite (rowWords x j)) (i : Fin 4) :
    Finite (rowWords (activate x) i) ∧
      |decodeRow (activate x) i-Gelu.Real.gelu (decodeRow x i)| ≤ 1/100 := by
  have h := Gelu.evaluateAll_error (rowWords x i) (hx i)
  fin_cases i <;> exact h

theorem activate_error_bounded (x : Row) (hx : ∀ j, Finite (rowWords x j))
    (hb : ∀ j, |decodeRow x j| ≤ 3) (i : Fin 4) :
    Finite (rowWords (activate x) i) ∧
      |decodeRow (activate x) i-Gelu.Real.gelu (decodeRow x i)| ≤ 1/80000 := by
  have h := Gelu.evaluateAll_error_bounded (rowWords x i) (hx i) (hb i)
  fin_cases i <;> exact h

#print axioms norm_error
#print axioms dotColumn8_error
end Project.TinyGpt2
