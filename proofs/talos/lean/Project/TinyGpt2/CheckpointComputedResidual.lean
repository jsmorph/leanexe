import Project.TinyGpt2.CheckpointAttentionValue

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

noncomputable def computedOutputReference (n : UInt64) (x : Row) (rows : Context) : Real.Row :=
  Real.matrixApply (decodeMatrix words 1088 4 4)
    (fun j => ∑ i, value (Softmax.outputs (computedProbabilities n x rows (Real.headOf j)) i)*
      Real.matrixApply (decodeMatrix words 1072 4 4)
        (Real.norm (decodeNorm words 2464) (decodeRow (contextRows rows i))) j)

def computedResidual (n : UInt64) (x : Row) (rows : Context) : Row :=
  addRows x (addRows (project4 words 1088 (computedAttention n x rows)) (loadRow words 1104))

theorem computedOutput_magnitude (n : UInt64) (hn : 0 < n) (hn4 : n ≤ 4)
    (x : Row) (rows : Context) (hx : LayerNorm.ValidRow (rowWords x))
    (hr : ∀ i, LayerNorm.ValidRow (rowWords (contextRows rows i))) (j : Fin 4) :
    |computedOutputReference n x rows j| ≤ (1+52*arithmeticEpsilon)*(5/2) := by
  have hp := fun head => computedProbabilities_bounds n hn hn4 x rows head hx hr
  exact attention_output_magnitude (fun i => decodeRow (contextRows rows i))
    (fun head i => value (Softmax.outputs (computedProbabilities n x rows head) i))
    (1+52*arithmeticEpsilon) (fun head => (hp head).2.1) (fun head => (hp head).2.2) j

theorem computedOutput_error (n : UInt64) (hn : 0 < n) (hn4 : n ≤ 4)
    (x : Row) (rows : Context) (hx : LayerNorm.ValidRow (rowWords x))
    (hr : ∀ i, LayerNorm.ValidRow (rowWords (contextRows rows i))) (j : Fin 4) :
    Approximation (rowWords (project4 words 1088 (computedAttention n x rows)) j)
      (computedOutputReference n x rows j) 3 (1/10000) := by
  have ha := computedAttention_error n hn hn4 x rows hx hr
  have hw (i : Fin 4) : Affine.Bounded (matrixWords words 1088 4 4 i j) 16 := by
    have hi : 1088+i.val*4+j.val < words.size := by rw [words_size]; omega
    refine ⟨by simpa [matrixWords, getElem!_pos, hi] using (word_bounded _ hi).1, ?_⟩
    exact (attention_bound i j).trans (by norm_num)
  have hd := dotColumn4_error words 1088 4 j (computedAttention n x rows)
    (fun i => ⟨(ha i).finite, (ha i).magnitude.trans (by norm_num)⟩) hw
  have hp := Affine.Real.dot_input_perturbation (decodeRow (computedAttention n x rows))
    (fun k => ∑ i, value (Softmax.outputs (computedProbabilities n x rows (Real.headOf k)) i)*
      Real.matrixApply (decodeMatrix words 1072 4 4)
        (Real.norm (decodeNorm words 2464) (decodeRow (contextRows rows i))) k)
    (fun i => decodeMatrix words 1088 4 4 i j) (1/100000) (fun i => (ha i).accuracy)
  have hs : (∑ i, |decodeMatrix words 1088 4 4 i j|) ≤ 4 := by
    calc
      _ ≤ ∑ _ : Fin 4, (1:ℝ) := Finset.sum_le_sum (fun i _ => attention_bound i j)
      _ = _ := by norm_num
  have he := (abs_sub_le _ _ _).trans (add_le_add hd.accuracy hp)
  have he' : |value (dotColumn4 words 1088 4 j.val (computedAttention n x rows))-
      computedOutputReference n x rows j| ≤ 1/10000 := he.trans (by
    have h := mul_le_mul_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 1/100000)
    norm_num [arithmeticEpsilon] at *
    linarith)
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ he'
    (computedOutput_magnitude n hn hn4 x rows hx hr j)
  rw [project4_words]
  exact ⟨hd.finite, hm.trans (by norm_num [arithmeticEpsilon]), he'⟩

theorem computedResidual_error (n : UInt64) (hn : 0 < n) (hn4 : n ≤ 4)
    (x : Row) (rows : Context) (hx : LayerNorm.ValidRow (rowWords x))
    (hr : ∀ i, LayerNorm.ValidRow (rowWords (contextRows rows i)))
    (hmx : ∀ i, |decodeRow x i| ≤ 1001/1000) (j : Fin 4) :
    Approximation (rowWords (computedResidual n x rows) j)
      (decodeRow x j+(computedOutputReference n x rows j+(parameters words).attentionBias j))
      (37/10) (1/5000) := by
  have ho := computedOutput_error n hn hn4 x rows hx hr j
  have hb := loaded_valid 1104 (by rw [words_size]; decide) j
  have hbias := Approximation.exact (rowWords (loadRow words 1104) j) hb.1
    (1/10) (attention_bias_magnitude j)
  have hatt := ho.add hbias (bound := 4) (by norm_num) (by norm_num) (by norm_num)
  have hinput := Approximation.exact (rowWords x j) (hx j).1 4 (hx j).2
  have hres := hinput.add hatt (bound := 9) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  have hm : |decodeRow x j+(computedOutputReference n x rows j+
      (parameters words).attentionBias j)| ≤
      1001/1000+((1+52*arithmeticEpsilon)*(5/2)+1/10) :=
    (abs_add_le _ _).trans (add_le_add (hmx j) ((abs_add_le _ _).trans
      (add_le_add (computedOutput_magnitude n hn hn4 x rows hx hr j)
        (attention_bias_magnitude j))))
  have hout := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hres.accuracy hm
  simp only [computedResidual, addRows_words]
  exact ⟨hres.finite, hout.trans (by norm_num [arithmeticEpsilon]),
    hres.accuracy.trans (by norm_num [arithmeticEpsilon])⟩

theorem computedResidual_valid (n : UInt64) (hn : 0 < n) (hn4 : n ≤ 4)
    (x : Row) (rows : Context) (hx : LayerNorm.ValidRow (rowWords x))
    (hr : ∀ i, LayerNorm.ValidRow (rowWords (contextRows rows i)))
    (hmx : ∀ i, |decodeRow x i| ≤ 1001/1000) :
    LayerNorm.ValidRow (rowWords (computedResidual n x rows)) := by
  intro j
  have h := computedResidual_error n hn hn4 x rows hx hr hmx j
  exact ⟨h.finite, h.magnitude.trans (by norm_num)⟩

theorem embedding_residual_valid (tokens : Fin 4 → UInt64)
    (ht : ∀ i, (tokens i).toNat < 256) (position : Fin 4) :
    let rows := Context.mk (embedding words (tokens 0) 0) (embedding words (tokens 1) 1)
      (embedding words (tokens 2) 2) (embedding words (tokens 3) 3)
    LayerNorm.ValidRow (rowWords
      (computedResidual (UInt64.ofNat (position.val+1)) (contextRows rows position) rows)) := by
  intro rows
  have hv (i : Fin 4) : LayerNorm.ValidRow (rowWords (contextRows rows i)) := by
    fin_cases i <;> exact embedding_valid _ _ (ht _) (by decide)
  have hm (i j : Fin 4) : |decodeRow (contextRows rows i) j| ≤ 1001/1000 := by
    fin_cases i <;> exact (embedding_error _ _ (ht _) (by decide) j).magnitude
  exact computedResidual_valid _ (by fin_cases position <;> decide)
    (by fin_cases position <;> decide) _ rows (hv position) hv (hm position)

#print axioms computedResidual_valid
#print axioms embedding_residual_valid
end Project.TinyGpt2.Checkpoint
