import Project.TinyGpt2.CheckpointCoefficients
import Project.TinyGpt2.Rows
import Project.Affine.Real

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner

theorem matrix_magnitude (w : Real.Matrix 4 4) (x : Real.Row) (a b : ℝ)
    (ha : 0 ≤ a) (hx : ∀ i, |x i| ≤ a) (hw : ∀ i j, |w i j| ≤ b) (j : Fin 4) :
    |Real.matrixApply w x j| ≤ 4*a*b := by
  calc
    _ ≤ ∑ i, |x i| * |w i j| := Affine.Real.dot_magnitude x (fun i => w i j)
    _ ≤ ∑ _ : Fin 4, a*b :=
      Finset.sum_le_sum (fun i _ => mul_le_mul (hx i) (hw i j) (abs_nonneg _) ha)
    _ = _ := by simp; ring

theorem norm1_real_magnitude (x : Real.Row) (i : Fin 4) :
    |Real.norm (decodeNorm words 2464) x i| ≤ 14/5 := by
  have hn := LayerNorm.Real.normalized_magnitude (1/100000) (by norm_num) x i
  have hp := mul_le_mul hn (norm1_scale i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  rw [← abs_mul] at hp
  change |LayerNorm.Real.normalized (1/100000) x i*(decodeNorm words 2464).scale i+
    (decodeNorm words 2464).bias i| ≤ _
  exact (abs_add_le _ _).trans ((add_le_add hp (norm1_bias i)).trans_eq (by norm_num))

theorem norm1_error (x : Row) (hx : LayerNorm.ValidRow (rowWords x)) (i : Fin 4) :
    Approximation (rowWords (norm words 2464 x) i)
      (Real.norm (decodeNorm words 2464) (decodeRow x) i) 3 (1/1000000) := by
  have hn := norm_error words 2464 x hx
    (loaded_valid 2464 (by rw [words_size]; decide))
    (loaded_valid 2468 (by rw [words_size]; decide)) i
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hn.2 (norm1_real_magnitude (decodeRow x) i)
  exact ⟨hn.1, hm.trans (by norm_num), hn.2⟩

theorem normalized_column_error (offset : Nat) (ho : offset+15 < words.size)
    (hw : ∀ i j, |decodeMatrix words offset 4 4 i j| ≤ 6/5)
    (x : Row) (hx : LayerNorm.ValidRow (rowWords x)) (j : Fin 4) :
    Approximation (dotColumn4 words offset 4 j.val (norm words 2464 x))
      (Real.matrixApply (decodeMatrix words offset 4 4)
        (Real.norm (decodeNorm words 2464) (decodeRow x)) j) 15 (1/200000) := by
  have hn := norm1_error x hx
  have hweights (i : Fin 4) : Affine.Bounded (matrixWords words offset 4 4 i j) 16 := by
    have hi : offset+i.val*4+j.val < words.size := by omega
    have hf := (word_bounded _ hi).1
    refine ⟨by simpa [matrixWords, getElem!_pos, hi] using hf, ?_⟩
    exact (hw i j).trans (by norm_num)
  have hp := dotColumn4_error words offset 4 j (norm words 2464 x)
    (fun i => ⟨(hn i).finite, (hn i).magnitude.trans (by norm_num)⟩) hweights
  have hm := matrix_magnitude (decodeMatrix words offset 4 4) (decodeRow (norm words 2464 x))
    3 (6/5) (by norm_num) (fun i => (hn i).magnitude) hw j
  have hout := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hp.accuracy hm
  have hs : (∑ i, |decodeMatrix words offset 4 4 i j|) ≤ 24/5 := by
    calc
      _ ≤ ∑ _ : Fin 4, (6/5:ℝ) := Finset.sum_le_sum (fun i _ => hw i j)
      _ = _ := by norm_num
  have hd := Affine.Real.dot_input_perturbation (decodeRow (norm words 2464 x))
    (Real.norm (decodeNorm words 2464) (decodeRow x))
    (fun i => decodeMatrix words offset 4 4 i j) (1/1000000) (fun i => (hn i).accuracy)
  have he := (abs_sub_le _ _ _).trans (add_le_add hp.accuracy hd)
  refine ⟨hp.finite, hout.trans ?_, he.trans ?_⟩
  · norm_num [arithmeticEpsilon]
  · have hh := mul_le_mul_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 1/1000000)
    norm_num [arithmeticEpsilon] at *
    linarith

#print axioms norm1_error
#print axioms normalized_column_error
end Project.TinyGpt2.Checkpoint
