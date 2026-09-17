import Project.TinyGpt2.RuntimeParameters

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem runtime_normalized_projection_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (normOffset offset : Nat) (hn : normOffset+8 ≤ Layout.size) (ho : offset+16 ≤ Layout.size)
    (x : Row) (hx : ∀ i, Affine.Bounded (rowWords x i) 200000) (j : Fin 4) :
    Affine.Bounded (rowWords (project4 w offset (norm w normOffset x)) j) (12*bound^2+1) := by
  have hnorm := norm_error_wide w normOffset x 200000 bound (by norm_num) (by norm_num)
    hb0 hb10 hx (loaded_weights_bounded w bound hw normOffset (by omega))
    (loaded_weights_bounded w bound hw (normOffset+4) (by omega))
  have hr (i : Fin 4) : Affine.Bounded (rowWords (norm w normOffset x) i) 31 :=
    ⟨(hnorm i).finite, (hnorm i).magnitude.trans (by norm_num [arithmeticEpsilon]; linarith)⟩
  have hmatrix := matrix_weights_bounded w bound hw offset 4 4 ho
  have hd := dotColumn4_error_wide w offset 4 j (norm w normOffset x) 31 bound
    (by norm_num) hb0 (by norm_num; linarith) hr (fun i => hmatrix i j)
  have hm := Real.matrixApply_magnitude (decodeMatrix w offset 4 4) (decodeRow (norm w normOffset x))
    bound (3*bound+(254*bound+2)*arithmeticEpsilon) (by unfold arithmeticEpsilon; positivity)
    (fun i k => (hmatrix i k).2) (fun i => (hnorm i).magnitude) j
  have hout := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hd.accuracy hm
  have hb2 : bound*bound ≤ 100 := (mul_le_mul hb10 hb10 hb0 (by norm_num)).trans_eq (by norm_num)
  rw [project4_words]
  exact ⟨hd.finite, hout.trans (by norm_num [arithmeticEpsilon]; nlinarith)⟩

#print axioms runtime_normalized_projection_bounded
end Project.TinyGpt2
