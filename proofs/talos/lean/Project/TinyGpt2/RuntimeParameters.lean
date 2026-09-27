import Project.TinyGpt2.RuntimeAffine
import Project.TinyGpt2.RuntimeNormPerturbation

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

def WeightsBounded (w : Array UInt64) (bound : ℝ) : Prop :=
  ∀ i, i < Layout.size → Affine.Bounded w[i]! bound

theorem prepared_weights_bounded (bound : UInt64) (w : Array UInt64)
    (h : F64Clip.accepted Layout.size bound w = true) :
    WeightsBounded (F64Clip.prepare Layout.size bound w) (value bound) := by
  intro i hi
  have hs := ((F64Clip.accepted_iff Layout.size bound w).mp h).1
  have he := F64Clip.prepare_element Layout.size bound w h i (by omega)
  exact ⟨he.1, he.2.1⟩

theorem loaded_weights_bounded (w : Array UInt64) (bound : ℝ) (h : WeightsBounded w bound)
    (offset : Nat) (ho : offset+4 ≤ Layout.size) (i : Fin 4) :
    Affine.Bounded (rowWords (loadRow w offset) i) bound := by
  rw [loadRow_words]
  exact h _ (by omega)

theorem matrix_weights_bounded (w : Array UInt64) (bound : ℝ) (h : WeightsBounded w bound)
    (offset m n : Nat) (ho : offset+m*n ≤ Layout.size) (i : Fin m) (j : Fin n) :
    Affine.Bounded (matrixWords w offset m n i j) bound := by
  apply h
  have hi := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
  have hj := j.isLt
  nlinarith

theorem runtime_norm_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (offset : Nat) (ho : offset+8 ≤ Layout.size) (x : Row)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 200000) (i : Fin 4) :
    Affine.Bounded (rowWords (norm w offset x) i) 31 := by
  have h := norm_error_wide w offset x 200000 bound (by norm_num) (by norm_num)
    hb0 hb10 hx (loaded_weights_bounded w bound hw offset (by omega))
    (loaded_weights_bounded w bound hw (offset+4) (by omega)) i
  exact ⟨h.finite, h.magnitude.trans (by norm_num [arithmeticEpsilon]; linarith)⟩

theorem runtime_project_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (offset : Nat) (ho : offset+16 ≤ Layout.size) (x : Row)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 31) (i : Fin 4) :
    Affine.Bounded (rowWords (project4 w offset x) i) 1249 := by
  rw [project4_words]
  have h := dotColumn4_error_wide w offset 4 i x 31 bound (by norm_num) hb0
    (by norm_num; linarith) hx (fun j => matrix_weights_bounded w bound hw offset 4 4 ho j i)
  exact ⟨h.finite, h.magnitude.trans (by linarith)⟩

theorem addRows_bounded (x y : Row) (left right : ℝ)
    (hb1 : 1 ≤ left+right) (hbMax : left+right ≤ 2^40)
    (hx : ∀ i, Affine.Bounded (rowWords x i) left)
    (hy : ∀ i, Affine.Bounded (rowWords y i) right) (i : Fin 4) :
    Affine.Bounded (rowWords (addRows x y) i) (left+right+1) := by
  rw [addRows_words]
  have h := add_error_wide _ _ (left+right) hb1 hbMax (hx i).1 (hy i).1
    ((abs_add_le _ _).trans (add_le_add (hx i).2 (hy i).2))
  exact ⟨h.finite, h.magnitude⟩

#print axioms prepared_weights_bounded
#print axioms runtime_norm_bounded
#print axioms runtime_project_bounded
end Project.TinyGpt2
