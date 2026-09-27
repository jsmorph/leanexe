import Project.TinyGpt2.CheckpointAttention
import Project.TinyGpt2.CheckpointEmbedding
import Project.TinyGpt2.ProjectionRange
import Project.Softmax.RealProperties

namespace Project.TinyGpt2.Checkpoint
open Project.ProofKit RealNormalization

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def outputColumn (head : Fin 2) (j i : Fin 4) : ℚ :=
  ∑ k, matrix 1072 i head k*rational (1088+(Real.coordinate head k).val*4+j.val)

def outputCentered (head : Fin 2) (j i : Fin 4) : ℚ :=
  scale i*outputColumn head j i-(∑ a, scale a*outputColumn head j a)/4

def outputBias (head : Fin 2) (j : Fin 4) : ℚ :=
  ∑ i, bias i*outputColumn head j i

def outputRadius (head : Fin 2) : ℚ := if head = 0 then 1/3 else 5/6
def outputBiasBound (head : Fin 2) : ℚ := if head = 0 then 1/100 else 3/25

theorem output_norm (head : Fin 2) (j : Fin 4) :
    (∑ i, (outputCentered head j i)^2) ≤ (outputRadius head)^2 := by
  fin_cases head <;> fin_cases j <;> decide +kernel

theorem output_bias_bound (head : Fin 2) (j : Fin 4) :
    |outputBias head j| ≤ outputBiasBound head := by
  fin_cases head <;> fin_cases j <;> decide +kernel

theorem outputColumn_cast (head : Fin 2) (j i : Fin 4) :
    (outputColumn head j i : ℝ) = Real.headOutputColumn
      (decodeMatrix words 1072 4 4) (decodeMatrix words 1088 4 4) head j i := by
  simp [outputColumn, Real.headOutputColumn, matrix, rational, F64Rational.decode_cast,
    decodeMatrix, matrixWords]

theorem outputCentered_cast (head : Fin 2) (j i : Fin 4) :
    (outputCentered head j i : ℝ) = Real.centeredColumn
      (fun a => (decodeNorm words 2464).scale a*Real.headOutputColumn
        (decodeMatrix words 1072 4 4) (decodeMatrix words 1088 4 4) head j a) i := by
  simp [outputCentered, Real.centeredColumn, outputColumn_cast, scale, rational,
    F64Rational.decode_cast, decodeNorm, decodeRow, loadRow_words]

theorem outputBias_cast (head : Fin 2) (j : Fin 4) :
    (outputBias head j : ℝ) = ∑ i, (decodeNorm words 2464).bias i*Real.headOutputColumn
      (decodeMatrix words 1072 4 4) (decodeMatrix words 1088 4 4) head j i := by
  simp [outputBias, outputColumn_cast, bias, rational, F64Rational.decode_cast,
    decodeNorm, decodeRow, loadRow_words]

theorem head_output_magnitude (x : Real.Row) (head : Fin 2) (j : Fin 4) :
    |∑ k, Real.matrixApply (decodeMatrix words 1072 4 4)
      (Real.norm (decodeNorm words 2464) x) (Real.coordinate head k)*
        decodeMatrix words 1088 4 4 (Real.coordinate head k) j| ≤
      if head = 0 then 7/10 else 9/5 := by
  rw [Real.head_output_projection]
  have hn : sumSquares (Real.centeredColumn
      (fun a => (decodeNorm words 2464).scale a*Real.headOutputColumn
        (decodeMatrix words 1072 4 4) (decodeMatrix words 1088 4 4) head j a)) ≤
        (outputRadius head : ℝ)^2 := by
    have h : ((∑ i, (outputCentered head j i)^2 : ℚ):ℝ) ≤
        (((outputRadius head)^2 : ℚ):ℝ) := Rat.cast_le.mpr (output_norm head j)
    simpa [sumSquares, outputCentered_cast] using h
  have hb : |∑ i, (decodeNorm words 2464).bias i*Real.headOutputColumn
      (decodeMatrix words 1072 4 4) (decodeMatrix words 1088 4 4) head j i| ≤
        (outputBiasBound head : ℝ) := by
    have h : ((|outputBias head j| : ℚ):ℝ) ≤ (outputBiasBound head : ℝ) :=
      Rat.cast_le.mpr (output_bias_bound head j)
    simpa [outputBias_cast] using h
  have h := Real.normalized_projection_bound _ x _ (outputRadius head) (outputBiasBound head)
    (by fin_cases head <;> norm_num [outputRadius]) hn hb
  exact h.trans (by fin_cases head <;> norm_num [outputRadius, outputBiasBound])

theorem attention_output_magnitude (rows : Fin 4 → Real.Row) (p : Fin 2 → Fin 4 → ℝ)
    (mass : ℝ) (hp : ∀ head i, 0 ≤ p head i) (hm : ∀ head, ∑ i, p head i ≤ mass)
    (j : Fin 4) :
    |Real.matrixApply (decodeMatrix words 1088 4 4)
      (fun k => ∑ i, p (Real.headOf k) i*Real.matrixApply (decodeMatrix words 1072 4 4)
        (Real.norm (decodeNorm words 2464) (rows i)) k) j| ≤ mass*(5/2) := by
  rw [Real.attention_projection_group]
  have hh (head : Fin 2) := Real.weighted_magnitude (p head)
    (fun i => ∑ k, Real.matrixApply (decodeMatrix words 1072 4 4)
      (Real.norm (decodeNorm words 2464) (rows i)) (Real.coordinate head k)*
        decodeMatrix words 1088 4 4 (Real.coordinate head k) j)
    mass (if head = 0 then 7/10 else 9/5) (hp head) (hm head)
    (by split <;> norm_num) (fun i => head_output_magnitude (rows i) head j)
  calc
    _ ≤ ∑ head, |∑ i, p head i*(∑ k, Real.matrixApply (decodeMatrix words 1072 4 4)
        (Real.norm (decodeNorm words 2464) (rows i)) (Real.coordinate head k)*
          decodeMatrix words 1088 4 4 (Real.coordinate head k) j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ head : Fin 2, mass*(if head = 0 then 7/10 else 9/5) :=
      Finset.sum_le_sum (fun head _ => hh head)
    _ = _ := by norm_num [Fin.sum_univ_two]; ring

theorem attention_bias_magnitude (j : Fin 4) :
    |(parameters words).attentionBias j| ≤ 1/10 := by
  have h : |F64Rational.decode words[1104+j.val]!| ≤ 1/10 := by
    fin_cases j <;> decide +kernel
  simpa [parameters, Layout.attentionBias, decodeRow, loadRow_words] using
    F64Rational.magnitude _ _ h

theorem real_embedding_magnitude (tokens : Real.Tokens) (i j : Fin 4) :
    |Real.embedding (parameters words) tokens i j| ≤ 1 := by
  have ht := (embedding_word_bounded (4*(tokens i).val+j.val) (by omega)).2
  have hp := (embedding_word_bounded (1024+4*i.val+j.val) (by omega)).2
  have h := (abs_add_le _ _).trans ((add_le_add ht hp).trans
    (by norm_num : (1:ℝ)/2+1/2 ≤ 1))
  simpa [Real.embedding, parameters, Layout.token, Layout.position, decodeRow,
    loadRow_words] using h

theorem real_residual1_magnitude (tokens : Real.Tokens) (i j : Fin 4) :
    |Real.residual1 (parameters words) tokens i j| ≤ 18/5 := by
  have hp (head : Fin 2) (k : Fin 4) :
      0 ≤ Real.probability (parameters words) tokens i head k :=
    Softmax.Real.probability_nonnegative _ _ _
  have hm (head : Fin 2) : ∑ k, Real.probability (parameters words) tokens i head k ≤ 1 := by
    apply le_of_eq
    exact Softmax.Real.probability_sum _ _ ⟨i, by simp [Real.visible]⟩
  have ha := attention_output_magnitude (Real.embedding (parameters words) tokens)
    (Real.probability (parameters words) tokens i) 1 hp hm j
  have he := real_embedding_magnitude tokens i j
  have hb := attention_bias_magnitude j
  change |Real.embedding (parameters words) tokens i j+
    Real.matrixApply (decodeMatrix words 1088 4 4)
      (fun k => ∑ a, Real.probability (parameters words) tokens i (Real.headOf k) a*
        Real.matrixApply (decodeMatrix words 1072 4 4)
          (Real.norm (decodeNorm words 2464) (Real.embedding (parameters words) tokens a)) k) j+
    (parameters words).attentionBias j| ≤ _
  exact (abs_add_le _ _).trans
    ((add_le_add ((abs_add_le _ _).trans (add_le_add he ha)) hb).trans (by norm_num))

#print axioms head_output_magnitude
#print axioms attention_output_magnitude
#print axioms real_residual1_magnitude
end Project.TinyGpt2.Checkpoint
