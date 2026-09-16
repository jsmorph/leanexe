import Project.TinyGpt2.Real
import Project.Softmax.RealProperties

namespace Project.TinyGpt2.Real

theorem embedding_prefix (p : Parameters) (x y : Tokens) (i : Fin 4)
    (h : ∀ j, j ≤ i → x j = y j) (j : Fin 4) (hj : j ≤ i) :
    embedding p x j = embedding p y j := by
  unfold embedding
  rw [h j hj]

theorem normalizedEmbedding_prefix (p : Parameters) (x y : Tokens) (i : Fin 4)
    (h : ∀ j, j ≤ i → x j = y j) (j : Fin 4) (hj : j ≤ i) :
    normalizedEmbedding p x j = normalizedEmbedding p y j := by
  simp only [normalizedEmbedding, embedding_prefix p x y i h j hj]

theorem probability_prefix (p : Parameters) (x y : Tokens) (i : Fin 4)
    (h : ∀ j, j ≤ i → x j = y j) (head : Fin 2) (k : Fin 4) :
    probability p x i head k = probability p y i head k := by
  apply Softmax.Real.probability_congr_visible
  intro j hj
  have hji : j ≤ i := by simpa only [visible, decide_eq_true_eq] using hj
  simp only [score, normalizedEmbedding_prefix p x y i h i (le_refl _),
    normalizedEmbedding_prefix p x y i h j hji]

theorem attended_prefix (p : Parameters) (x y : Tokens) (i : Fin 4)
    (h : ∀ j, j ≤ i → x j = y j) : attended p x i = attended p y i := by
  funext j
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ≤ i
  · rw [probability_prefix p x y i h, normalizedEmbedding_prefix p x y i h k hk]
  · have hmask : visible i k = false := by simp [visible, hk]
    simp only [probability, Softmax.Real.probability_zero _ _ k hmask, zero_mul]

theorem residual1_prefix (p : Parameters) (x y : Tokens) (i : Fin 4)
    (h : ∀ j, j ≤ i → x j = y j) : residual1 p x i = residual1 p y i := by
  unfold residual1
  rw [embedding_prefix p x y i h i (le_refl _), attended_prefix p x y i h]

theorem logits_prefix (p : Parameters) (x y : Tokens) (i : Fin 4)
    (h : ∀ j, j ≤ i → x j = y j) : logits p x i = logits p y i := by
  unfold logits hidden residual2 activated expanded
  rw [residual1_prefix p x y i h]

#print axioms logits_prefix
end Project.TinyGpt2.Real
