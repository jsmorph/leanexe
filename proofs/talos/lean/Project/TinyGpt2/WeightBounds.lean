import Project.TinyGpt2.Real
import Project.Softmax.RealProperties

namespace Project.TinyGpt2.Real

def NormBounded (p : NormParameters) (bound : ℝ) : Prop :=
  (∀ i, |p.scale i| ≤ bound) ∧ (∀ i, |p.bias i| ≤ bound)

structure ParametersBounded (p : Parameters) (bound : ℝ) : Prop where
  token : ∀ i j, |p.token i j| ≤ bound
  position : ∀ i j, |p.position i j| ≤ bound
  query : ∀ i j, |p.query i j| ≤ bound
  key : ∀ i j, |p.key i j| ≤ bound
  value : ∀ i j, |p.value i j| ≤ bound
  attention : ∀ i j, |p.attention i j| ≤ bound
  attentionBias : ∀ i, |p.attentionBias i| ≤ bound
  expand : ∀ i j, |p.expand i j| ≤ bound
  expandBias : ∀ i, |p.expandBias i| ≤ bound
  contract : ∀ i j, |p.contract i j| ≤ bound
  contractBias : ∀ i, |p.contractBias i| ≤ bound
  head : ∀ i j, |p.head i j| ≤ bound
  headBias : ∀ i, |p.headBias i| ≤ bound
  norm1 : NormBounded p.norm1 bound
  norm2 : NormBounded p.norm2 bound
  normFinal : NormBounded p.normFinal bound

theorem matrixApply_magnitude {m n : Nat} (w : Matrix m n) (x : Fin m → ℝ)
    (weightBound inputBound : ℝ) (hx0 : 0 ≤ inputBound)
    (hw : ∀ i j, |w i j| ≤ weightBound) (hx : ∀ i, |x i| ≤ inputBound) (j : Fin n) :
    |matrixApply w x j| ≤ m*inputBound*weightBound := by
  calc
    _ ≤ ∑ i, |x i*w i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin m, inputBound*weightBound := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hx i) (hw i j) (abs_nonneg _) hx0
    _ = _ := by simp; ring

theorem norm_magnitude (p : NormParameters) (x : Row) (bound : ℝ)
    (hp : NormBounded p bound) (j : Fin 4) : |norm p x j| ≤ 3*bound := by
  have hn := LayerNorm.Real.normalized_magnitude (1/100000) (by norm_num) x j
  have hm := mul_le_mul hn (hp.1 j) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  change |LayerNorm.Real.normalized (1/100000) x j*p.scale j+p.bias j| ≤ _
  exact ((abs_add_le _ _).trans (add_le_add (by simpa only [abs_mul] using hm) (hp.2 j))).trans_eq
    (by ring)

theorem embedding_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hp : ParametersBounded p bound) (i j : Fin 4) : |embedding p tokens i j| ≤ 2*bound := by
  exact ((abs_add_le _ _).trans (add_le_add (hp.token (tokens i) j) (hp.position i j))).trans_eq
    (by ring)

theorem normalized_projection_magnitude (p : NormParameters) (w : Matrix 4 4) (x : Row)
    (bound : ℝ) (hb : 0 ≤ bound) (hp : NormBounded p bound)
    (hw : ∀ i j, |w i j| ≤ bound) (j : Fin 4) :
    |matrixApply w (norm p x) j| ≤ 12*bound^2 := by
  have hh := matrixApply_magnitude w (norm p x) bound (3*bound) (by positivity)
    hw (norm_magnitude p x bound hp) j
  exact hh.trans_eq (by norm_num; ring)

theorem attended_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hb : 0 ≤ bound) (hp : ParametersBounded p bound) (i j : Fin 4) :
    |attended p tokens i j| ≤ 12*bound^2 := by
  apply Softmax.Real.weighted_magnitude (visible i) (score p tokens i (headOf j))
    (fun k => matrixApply p.value (normalizedEmbedding p tokens k) j) (12*bound^2)
  · intro k _
    exact normalized_projection_magnitude p.norm1 p.value _ bound hb hp.norm1 hp.value j
  · exact ⟨i, by simp [visible]⟩

theorem score_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hb : 0 ≤ bound) (hp : ParametersBounded p bound) (i j : Fin 4) (head : Fin 2) :
    |score p tokens i head j| ≤ 144*Real.sqrt 2*bound^4 := by
  have hterm (k : Fin 2) :
      |matrixApply p.query (normalizedEmbedding p tokens i) (coordinate head k)*
        matrixApply p.key (normalizedEmbedding p tokens j) (coordinate head k)| ≤ 144*bound^4 := by
    rw [abs_mul]
    have hq := normalized_projection_magnitude p.norm1 p.query (embedding p tokens i) bound hb hp.norm1 hp.query
      (coordinate head k)
    have hk := normalized_projection_magnitude p.norm1 p.key (embedding p tokens j) bound hb hp.norm1 hp.key
      (coordinate head k)
    exact (mul_le_mul hq hk (abs_nonneg _) (by positivity)).trans_eq (by ring)
  rw [score, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).mpr
  calc
    _ ≤ ∑ k : Fin 2, |matrixApply p.query (normalizedEmbedding p tokens i) (coordinate head k)*
        matrixApply p.key (normalizedEmbedding p tokens j) (coordinate head k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 2, 144*bound^4 := Finset.sum_le_sum (fun k _ => hterm k)
    _ = 288*bound^4 := by simp; ring
    _ = _ := by
      rw [show 144*Real.sqrt 2*bound^4*Real.sqrt 2 = 144*bound^4*(Real.sqrt 2)^2 by ring,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem score_spread_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hb : 0 ≤ bound) (hp : ParametersBounded p bound) (i j k : Fin 4) (head : Fin 2) :
    |score p tokens i head j-score p tokens i head k| ≤ 288*Real.sqrt 2*bound^4 := by
  exact ((abs_sub _ _).trans (add_le_add (score_magnitude p tokens bound hb hp i j head)
    (score_magnitude p tokens bound hb hp i k head))).trans_eq (by ring)

theorem residual1_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hb : 0 ≤ bound) (hp : ParametersBounded p bound) (i j : Fin 4) :
    |residual1 p tokens i j| ≤ 48*bound^3+3*bound := by
  have ha := matrixApply_magnitude p.attention (attended p tokens i) bound (12*bound^2)
    (by positivity) hp.attention (attended_magnitude p tokens bound hb hp i) j
  have hr := (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (embedding_magnitude p tokens bound hp i j) ha))
      (hp.attentionBias j))
  exact hr.trans_eq (by norm_num; ring)

theorem expanded_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hb : 0 ≤ bound) (hp : ParametersBounded p bound) (i : Fin 4) (j : Fin 8) :
    |expanded p tokens i j| ≤ 12*bound^2+bound := by
  have hm := matrixApply_magnitude p.expand (norm p.norm2 (residual1 p tokens i)) bound (3*bound)
    (by positivity) hp.expand (norm_magnitude p.norm2 _ bound hp.norm2) j
  exact ((abs_add_le _ _).trans (add_le_add hm (hp.expandBias j))).trans_eq (by norm_num; ring)

theorem activated_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hb : 0 ≤ bound) (hp : ParametersBounded p bound) (i : Fin 4) (j : Fin 8) :
    |activated p tokens i j| ≤ 12*bound^2+bound :=
  (Gelu.Real.gelu_magnitude _).trans (expanded_magnitude p tokens bound hb hp i j)

theorem residual2_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hb : 0 ≤ bound) (hp : ParametersBounded p bound) (i j : Fin 4) :
    |residual2 p tokens i j| ≤ 144*bound^3+8*bound^2+4*bound := by
  have hm := matrixApply_magnitude p.contract (activated p tokens i) bound (12*bound^2+bound)
    (by positivity) hp.contract (activated_magnitude p tokens bound hb hp i) j
  have hr := (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (residual1_magnitude p tokens bound hb hp i j) hm))
      (hp.contractBias j))
  exact hr.trans_eq (by norm_num; ring)

theorem hidden_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hp : ParametersBounded p bound) (i j : Fin 4) : |hidden p tokens i j| ≤ 3*bound :=
  norm_magnitude p.normFinal _ bound hp.normFinal j

theorem logits_magnitude (p : Parameters) (tokens : Tokens) (bound : ℝ)
    (hb : 0 ≤ bound) (hp : ParametersBounded p bound) (i : Fin 4) (j : Fin 256) :
    |logits p tokens i j| ≤ 12*bound^2+bound := by
  have hm := matrixApply_magnitude p.head (hidden p tokens i) bound (3*bound)
    (by positivity) hp.head (hidden_magnitude p tokens bound hp i) j
  exact ((abs_add_le _ _).trans (add_le_add hm (hp.headBias j))).trans_eq (by norm_num; ring)

#print axioms residual1_magnitude
#print axioms score_spread_magnitude
#print axioms residual2_magnitude
#print axioms logits_magnitude
end Project.TinyGpt2.Real
