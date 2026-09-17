import Project.TinyGpt2.CheckpointHiddenBounds
import Project.TinyGpt2.OutputModel

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner

theorem logit_model (w : Array UInt64) (x : Row) (j : Fin 256) :
    logit w x (UInt64.ofNat j.val) =
      Affine.affine4 (rowWords x 0) (rowWords x 1) (rowWords x 2) (rowWords x 3)
        (matrixWords w 1184 4 256 0 j) (matrixWords w 1184 4 256 1 j)
        (matrixWords w 1184 4 256 2 j) (matrixWords w 1184 4 256 3 j) w[2208+j.val]! := by
  have hj : j.val < 18446744073709551616 := by omega
  simp only [logit, Layout.head, Layout.headBias, UInt64.toNat_ofNat_of_lt' hj]
  rw [dotColumn4_model]
  rfl

theorem logit_error (x : Row) (hx : ∀ i, Affine.Bounded (rowWords x i) 7) (j : Fin 256) :
    Approximation (logit words x (UInt64.ofNat j.val))
      (Real.matrixApply (decodeMatrix words 1184 4 256) (decodeRow x) j+value words[2208+j.val]!)
      117 (1/10000000000) := by
  have hw (i : Fin 4) : Affine.Bounded (matrixWords words 1184 4 256 i j) 4 := by
    have hi : 1184+i.val*256+j.val < words.size := by rw [words_size]; omega
    simpa only [Affine.Bounded, matrixWords, getElem!_pos, hi] using word_bounded _ hi
  have hi : 2208+j.val < words.size := by rw [words_size]; omega
  have hb : Affine.Bounded words[2208+j.val]! 4 := by
    simpa only [Affine.Bounded, getElem!_pos, hi] using word_bounded _ hi
  have he := Affine.affine4_error (rowWords x) (fun i => matrixWords words 1184 4 256 i j)
    words[2208+j.val]! (fun i => ⟨(hx i).1, (hx i).2.trans (by norm_num)⟩)
    (fun i => ⟨(hw i).1, (hw i).2.trans (by norm_num)⟩) ⟨hb.1, hb.2.trans (by norm_num)⟩
  have hm : |Real.matrixApply (decodeMatrix words 1184 4 256) (decodeRow x) j| ≤ 112 := by
    calc
      _ ≤ ∑ i, |decodeRow x i| * |decodeMatrix words 1184 4 256 i j| := Affine.Real.dot_magnitude _ _
      _ ≤ ∑ _ : Fin 4, (7:ℝ)*4 := Finset.sum_le_sum
        (fun i _ => mul_le_mul (hx i).2 (hw i).2 (abs_nonneg _) (by norm_num))
      _ = _ := by norm_num
  have hsum := (abs_add_le _ _).trans (add_le_add hm hb.2)
  have hout := F64ArithmeticBounds.magnitude_of_error _ _ _ _ he.accuracy hsum
  rw [logit_model]
  exact ⟨he.finite, hout.trans (by norm_num), he.accuracy⟩

theorem infer_bounded (tokens : Fin 4 → UInt64) (ht : ∀ i, (tokens i).toNat < 256)
    (j : Fin 256) :
    Affine.Bounded (infer words (tokens 0) (tokens 1) (tokens 2) (tokens 3))[j.val]! 117 := by
  have hh := hidden_bounded tokens ht 3
  have hl := logit_error _ hh j
  rw [infer_eq_logitPrefix]
  simpa [Affine.Bounded, logitPrefix, getElem!_pos, j.isLt] using And.intro hl.finite hl.magnitude

#print axioms logit_error
#print axioms infer_bounded
end Project.TinyGpt2.Checkpoint
