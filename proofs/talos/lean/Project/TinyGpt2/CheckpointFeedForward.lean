import Project.TinyGpt2.CheckpointProjection
import Project.TinyGpt2.CheckpointAttention
import Project.TinyGpt2.ProjectionRange

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner RealNormalization

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

def expandCentered (j : Fin 8) (i : Fin 4) : ℚ :=
  rational (2472+i.val)*rational (1108+i.val*8+j.val)-
    (∑ k : Fin 4, rational (2472+k.val)*rational (1108+k.val*8+j.val))/4

def expandBias (j : Fin 8) : ℚ :=
  (∑ i : Fin 4, rational (2476+i.val)*rational (1108+i.val*8+j.val))+rational (1140+j.val)

theorem expand_norm (j : Fin 8) : (∑ i, (expandCentered j i)^2) ≤ 25/16 := by
  fin_cases j <;> decide +kernel

theorem expand_bias_bound (j : Fin 8) : |expandBias j| ≤ 49/100 := by
  fin_cases j <;> decide +kernel

theorem expandCentered_cast (j : Fin 8) (i : Fin 4) :
    (expandCentered j i : ℝ) = Real.centeredColumn
      (fun k => (decodeNorm words 2472).scale k*decodeMatrix words 1108 4 8 k j) i := by
  simp [expandCentered, rational, Real.centeredColumn, F64Rational.decode_cast,
    decodeNorm, decodeRow, decodeMatrix, matrixWords, loadRow_words]

theorem expandBias_cast (j : Fin 8) :
    (expandBias j : ℝ) =
      (∑ i, (decodeNorm words 2472).bias i*decodeMatrix words 1108 4 8 i j)+
        value words[1140+j.val]! := by
  simp [expandBias, rational, F64Rational.decode_cast, decodeNorm, decodeRow,
    decodeMatrix, matrixWords, loadRow_words]

theorem expand_real_magnitude (x : Real.Row) (j : Fin 8) :
    |Real.matrixApply (decodeMatrix words 1108 4 8) (Real.norm (decodeNorm words 2472) x) j+
      value words[1140+j.val]!| ≤ 299/100 := by
  have hw : sumSquares (Real.centeredColumn
      (fun i => (decodeNorm words 2472).scale i*decodeMatrix words 1108 4 8 i j)) ≤ (5/4)^2 := by
    have h : ((∑ i, (expandCentered j i)^2 : ℚ):ℝ) ≤ ((25/16:ℚ):ℝ) :=
      Rat.cast_le.mpr (expand_norm j)
    norm_num [sumSquares, expandCentered_cast] at h ⊢
    exact h
  have hb : |(∑ i, (decodeNorm words 2472).bias i*decodeMatrix words 1108 4 8 i j)+
      value words[1140+j.val]!| ≤ 49/100 := by
    have h : ((|expandBias j| : ℚ):ℝ) ≤ ((49/100:ℚ):ℝ) :=
      Rat.cast_le.mpr (expand_bias_bound j)
    simpa [expandBias_cast] using h
  exact (Real.normalized_affine_bound _ x _ _ (5/4) (49/100) (by norm_num) hw hb).trans_eq
    (by norm_num)

theorem norm2_scale (i : Fin 4) : |(decodeNorm words 2472).scale i| ≤ 11/10 := by
  have h : |F64Rational.decode words[2472+i.val]!| ≤ 11/10 := by
    fin_cases i <;> decide +kernel
  simpa [decodeNorm, decodeRow, loadRow_words] using F64Rational.magnitude _ _ h

theorem norm2_bias (i : Fin 4) : |(decodeNorm words 2472).bias i| ≤ 3/25 := by
  have h : |F64Rational.decode words[2476+i.val]!| ≤ 3/25 := by
    fin_cases i <;> decide +kernel
  simpa [decodeNorm, decodeRow, loadRow_words] using F64Rational.magnitude _ _ h

theorem expand_bound (i : Fin 4) (j : Fin 8) : |decodeMatrix words 1108 4 8 i j| ≤ 1 := by
  have h : |F64Rational.decode (matrixWords words 1108 4 8 i j)| ≤ 1 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  simpa [decodeMatrix] using F64Rational.magnitude _ _ h

theorem norm2_real_magnitude (x : Real.Row) (i : Fin 4) :
    |Real.norm (decodeNorm words 2472) x i| ≤ 58/25 := by
  have hn := LayerNorm.Real.normalized_magnitude (1/100000) (by norm_num) x i
  have hp := mul_le_mul hn (norm2_scale i) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)
  rw [← abs_mul] at hp
  change |LayerNorm.Real.normalized (1/100000) x i*(decodeNorm words 2472).scale i+
    (decodeNorm words 2472).bias i| ≤ _
  exact (abs_add_le _ _).trans ((add_le_add hp (norm2_bias i)).trans_eq (by norm_num))

theorem norm2_error (x : Row) (hx : LayerNorm.ValidRow (rowWords x)) (i : Fin 4) :
    Approximation (rowWords (norm words 2472 x) i)
      (Real.norm (decodeNorm words 2472) (decodeRow x) i) (5/2) (1/1000000) := by
  have hn := norm_error words 2472 x hx
    (loaded_valid 2472 (by rw [words_size]; decide))
    (loaded_valid 2476 (by rw [words_size]; decide)) i
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hn.2 (norm2_real_magnitude (decodeRow x) i)
  exact ⟨hn.1, hm.trans (by norm_num), hn.2⟩

theorem computedExpand_error (x : Row) (hx : LayerNorm.ValidRow (rowWords x)) (j : Fin 8) :
    Approximation (wideWords (expandRow words (norm words 2472 x)) j)
      (Real.matrixApply (decodeMatrix words 1108 4 8)
        (Real.norm (decodeNorm words 2472) (decodeRow x)) j+value words[1140+j.val]!)
      3 (1/200000) := by
  have hn := norm2_error x hx
  have hw (i : Fin 4) : Affine.Bounded (matrixWords words 1108 4 8 i j) 16 := by
    have hi : 1108+i.val*8+j.val < words.size := by rw [words_size]; omega
    exact ⟨by simpa [matrixWords, getElem!_pos, hi] using (word_bounded _ hi).1,
      (expand_bound i j).trans (by norm_num)⟩
  have hd := dotColumn4_error words 1108 8 j (norm words 2472 x)
    (fun i => ⟨(hn i).finite, (hn i).magnitude.trans (by norm_num)⟩) hw
  have hm : |Real.matrixApply (decodeMatrix words 1108 4 8) (decodeRow (norm words 2472 x)) j| ≤ 10 := by
    calc
      _ ≤ ∑ i, |decodeRow (norm words 2472 x) i| * |decodeMatrix words 1108 4 8 i j| :=
        Affine.Real.dot_magnitude _ _
      _ ≤ ∑ _ : Fin 4, (5/2:ℝ)*1 := Finset.sum_le_sum
        (fun i _ => mul_le_mul (hn i).magnitude (expand_bound i j) (abs_nonneg _) (by norm_num))
      _ = _ := by norm_num
  have hmag := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hd.accuracy hm
  have hp := Affine.Real.dot_input_perturbation (decodeRow (norm words 2472 x))
    (Real.norm (decodeNorm words 2472) (decodeRow x)) (fun i => decodeMatrix words 1108 4 8 i j)
    (1/1000000) (fun i => (hn i).accuracy)
  have hs : (∑ i, |decodeMatrix words 1108 4 8 i j|) ≤ 4 := by
    calc
      _ ≤ ∑ _ : Fin 4, (1:ℝ) := Finset.sum_le_sum (fun i _ => expand_bound i j)
      _ = _ := by norm_num
  have he := (abs_sub_le _ _ _).trans (add_le_add hd.accuracy hp)
  have hd' : Approximation (dotColumn4 words 1108 8 j.val (norm words 2472 x))
      (Real.matrixApply (decodeMatrix words 1108 4 8)
        (Real.norm (decodeNorm words 2472) (decodeRow x)) j) 11
      (12294*arithmeticEpsilon+4/1000000) := by
    refine ⟨hd.finite, hmag.trans (by norm_num [arithmeticEpsilon]), he.trans ?_⟩
    have h := mul_le_mul_of_nonneg_right hs (by norm_num : (0:ℝ) ≤ 1/1000000)
    linarith
  have hi : 1140+j.val < words.size := by rw [words_size]; omega
  have hb : Affine.Bounded words[1140+j.val]! 4 := by
    simpa only [Affine.Bounded, getElem!_pos, hi] using word_bounded _ hi
  have hout := hd'.add (Approximation.exact _ hb.1 4 hb.2)
    (bound := 15) (by norm_num) (by norm_num) (by norm_num)
  have hfinal := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hout.accuracy
    (expand_real_magnitude (decodeRow x) j)
  rw [expandRow_words]
  exact ⟨hout.finite, hfinal.trans (by norm_num [arithmeticEpsilon]),
    hout.accuracy.trans (by norm_num [arithmeticEpsilon])⟩

#print axioms computedExpand_error
end Project.TinyGpt2.Checkpoint
