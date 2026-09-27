import Project.TinyGpt2.CheckpointFeedForward

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def computedActivated (x : Row) : WideRow :=
  let e := expandRow words (norm words 2472 x)
  ⟨activate e.low, activate e.high⟩

noncomputable def expandedReference (x : Real.Row) (j : Fin 8) : ℝ :=
  Real.matrixApply (decodeMatrix words 1108 4 8) (Real.norm (decodeNorm words 2472) x) j+
    value words[1140+j.val]!

noncomputable def contractReference (x : Real.Row) (j : Fin 4) : ℝ :=
  Real.matrixApply (decodeMatrix words 1148 8 4) (fun i => Gelu.Real.gelu (expandedReference x i)) j+
    value words[1180+j.val]!

theorem computedActivated_error (x : Row) (hx : LayerNorm.ValidRow (rowWords x)) (j : Fin 8) :
    Approximation (wideWords (computedActivated x) j)
      (Gelu.Real.gelu (expandedReference (decodeRow x) j)) (31/10) (1/25000) := by
  have he := computedExpand_error x hx j
  have hg := GeluWide.evaluateAll_error _ he.finite
  have hp := GeluWide.evaluateAll_perturbed _ _ _ he.finite he.accuracy
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hg.2
    ((Gelu.Real.gelu_magnitude _).trans he.magnitude)
  simp only [computedActivated, activateWide_words]
  exact ⟨hg.1, hm.trans (by norm_num [arithmeticEpsilon]), hp.trans (by norm_num [arithmeticEpsilon])⟩

theorem contract_column_sum (j : Fin 4) : (∑ i, |decodeMatrix words 1148 8 4 i j|) ≤ 3 := by
  have h : (∑ i : Fin 8, |F64Rational.decode (matrixWords words 1148 8 4 i j)|) ≤ (3:ℚ) := by
    fin_cases j <;> decide +kernel
  have hr := Rat.cast_le (K := ℝ).mpr h
  simpa [decodeMatrix, F64Rational.decode_cast] using hr

theorem contract_bias_bound (j : Fin 4) : |value words[1180+j.val]!| ≤ 1/10 := by
  have h : |F64Rational.decode words[1180+j.val]!| ≤ 1/10 := by
    fin_cases j <;> decide +kernel
  simpa using F64Rational.magnitude _ _ h

theorem contractReference_magnitude (x : Real.Row) (j : Fin 4) :
    |contractReference x j| ≤ 91/10 := by
  have hm : |Real.matrixApply (decodeMatrix words 1148 8 4)
      (fun i => Gelu.Real.gelu (expandedReference x i)) j| ≤ 9 := by
    calc
      _ ≤ ∑ i, |Gelu.Real.gelu (expandedReference x i)| * |decodeMatrix words 1148 8 4 i j| :=
        Affine.Real.dot_magnitude _ _
      _ ≤ ∑ i, 3*|decodeMatrix words 1148 8 4 i j| := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right ((Gelu.Real.gelu_magnitude _).trans
          ((expand_real_magnitude x i).trans (by norm_num))) (abs_nonneg _))
      _ = 3*(∑ i, |decodeMatrix words 1148 8 4 i j|) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := by linarith [contract_column_sum j]
  exact (abs_add_le _ _).trans ((add_le_add hm (contract_bias_bound j)).trans_eq (by norm_num))

theorem computedContract_error (x : Row) (hx : LayerNorm.ValidRow (rowWords x)) (j : Fin 4) :
    Approximation (rowWords (contractRow words (computedActivated x)) j)
      (contractReference (decodeRow x) j) 10 (1/8000) := by
  have ha := computedActivated_error x hx
  have hw (i : Fin 8) : Affine.Bounded (matrixWords words 1148 8 4 i j) 16 := by
    have hi : 1148+i.val*4+j.val < words.size := by rw [words_size]; omega
    have h := word_bounded _ hi
    exact ⟨by simpa [matrixWords, getElem!_pos, hi] using h.1,
      (by simpa [decodeMatrix, matrixWords, getElem!_pos, hi] using h.2.trans (by norm_num : (4:ℝ) ≤ 16))⟩
  have hi : 1180+j.val < words.size := by rw [words_size]; omega
  have hb : Affine.Bounded words[1180+j.val]! 16 := by
    have h := word_bounded _ hi
    simpa [Affine.Bounded, getElem!_pos, hi] using
      And.intro h.1 (h.2.trans (by norm_num : (4:ℝ) ≤ 16))
  have hd := Affine.affine8_error (wideWords (computedActivated x))
    (fun i => matrixWords words 1148 8 4 i j) words[1180+j.val]!
    (fun i => ⟨(ha i).finite, (ha i).magnitude.trans (by norm_num)⟩) hw hb
  have hp := Affine.Real.affine_perturbation
    (fun i => value (wideWords (computedActivated x) i))
    (fun i => Gelu.Real.gelu (expandedReference (decodeRow x) i))
    (fun i => decodeMatrix words 1148 8 4 i j) (fun i => decodeMatrix words 1148 8 4 i j)
    (fun _ => 1/25000) (fun _ => 0) (value words[1180+j.val]!) (value words[1180+j.val]!) 0
    (fun i => (ha i).accuracy) (by simp) (by simp)
  simp only [mul_zero, add_zero, ← Finset.sum_mul] at hp
  have he := (abs_sub_le _ _ _).trans (add_le_add hd.accuracy hp)
  have he' : |value (rowWords (contractRow words (computedActivated x)) j)-
      contractReference (decodeRow x) j| ≤ 1/8000 := by
    rw [contractRow_words, dotColumn8_model]
    apply he.trans
    have hs := mul_le_mul_of_nonneg_right (contract_column_sum j)
      (by norm_num : (0:ℝ) ≤ 1/25000)
    linarith
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ he'
    (contractReference_magnitude (decodeRow x) j)
  refine ⟨?_, hm.trans (by norm_num), he'⟩
  rw [contractRow_words, dotColumn8_model]
  exact hd.finite

theorem computedResidual2_bound (x : Row) (hx : LayerNorm.ValidRow (rowWords x)) (j : Fin 4) :
    Affine.Bounded (rowWords (addRows x (contractRow words (computedActivated x))) j) 14 := by
  have hc := computedContract_error x hx
  have ha := addRows_error x (contractRow words (computedActivated x))
    (fun i => ⟨(hx i).1, (hx i).2.trans (by norm_num)⟩)
    (fun i => ⟨(hc i).finite, (hc i).magnitude.trans (by norm_num)⟩) j
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ (hc j).accuracy
    (contractReference_magnitude (decodeRow x) j)
  have hs := (abs_add_le _ _).trans (add_le_add (hx j).2 hm)
  have hout := F64ArithmeticBounds.magnitude_of_error _ _ _ _ ha.accuracy hs
  exact ⟨ha.finite, hout.trans (by norm_num [arithmeticEpsilon])⟩

#print axioms computedContract_error
#print axioms computedResidual2_bound
end Project.TinyGpt2.Checkpoint
