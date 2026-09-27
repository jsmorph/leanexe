import Project.TinyGpt2.CheckpointProjection
import Project.TinyGpt2.CheckpointEmbedding
import Project.TinyGpt2.CheckpointAttention
import Project.TinyGpt2.ScorePerturbation
import Project.SoftmaxWide.Row

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

def computedScore (x y : Row) (head : Fin 2) : UInt64 :=
  attentionScore
    (dotColumn4 words 1040 4 (Real.coordinate head 0).val (norm words 2464 x))
    (dotColumn4 words 1040 4 (Real.coordinate head 1).val (norm words 2464 x))
    (dotColumn4 words 1056 4 (Real.coordinate head 0).val (norm words 2464 y))
    (dotColumn4 words 1056 4 (Real.coordinate head 1).val (norm words 2464 y))

theorem computedScore_error (x y : Row) (head : Fin 2)
    (hx : LayerNorm.ValidRow (rowWords x)) (hy : LayerNorm.ValidRow (rowWords y)) :
    Approximation (computedScore x y head)
      (Real.rowScore (parameters words) (decodeRow x) (decodeRow y) head) 2051 (1/3000) := by
  have hq := normalized_column_error 1040 (by rw [words_size]; decide) query_bound x hx
  have hk := normalized_column_error 1056 (by rw [words_size]; decide) key_bound y hy
  have hs := attentionScore_perturbed _ _ _ _ _ _ _ _
    (hq (Real.coordinate head 0)) (hq (Real.coordinate head 1))
    (hk (Real.coordinate head 0)) (hk (Real.coordinate head 1))
  simpa only [computedScore, Real.rowScore, parameters, Layout.norm1, Layout.query,
    Layout.key, Fin.sum_univ_two] using hs

theorem computedScore_spread (x y v : Row) (head : Fin 2)
    (hx : LayerNorm.ValidRow (rowWords x))
    (hy : LayerNorm.ValidRow (rowWords y)) (hv : LayerNorm.ValidRow (rowWords v)) :
    |value (computedScore x y head)-value (computedScore x v head)| ≤ 16 := by
  have hyc := computedScore_error x y head hx hy
  have hvc := computedScore_error x v head hx hv
  have hr := row_attention_spread (decodeRow x) (decodeRow y) (decodeRow v) head
  have hm := (abs_sub_le _ _ _).trans (add_le_add hr
    (by simpa only [abs_sub_comm] using hvc.accuracy))
  have he := (abs_sub_le _ _ _).trans (add_le_add hyc.accuracy hm)
  exact he.trans (by norm_num)

theorem computed_scores_valid (n : UInt64) (hn : 0 < n) (hn4 : n ≤ 4)
    (x : Row) (keys : Fin 4 → Row) (head : Fin 2)
    (hx : LayerNorm.ValidRow (rowWords x))
    (hk : ∀ i, LayerNorm.ValidRow (rowWords (keys i))) :
    SoftmaxWide.Valid n (computedScore x (keys 0) head) (computedScore x (keys 1) head)
      (computedScore x (keys 2) head) (computedScore x (keys 3) head) := by
  have hs (i : Fin 4) : Softmax.scores
      (computedScore x (keys 0) head) (computedScore x (keys 1) head)
      (computedScore x (keys 2) head) (computedScore x (keys 3) head) i =
      computedScore x (keys i) head := by fin_cases i <;> rfl
  refine ⟨hn, hn4, ?_, ?_⟩
  · intro i
    rw [hs]
    exact (computedScore_error x (keys i) head hx (hk i)).finite
  · intro i j _ _
    rw [hs, hs]
    exact (computedScore_spread x (keys i) (keys j) head hx (hk i) (hk j)).trans_lt (by norm_num)

theorem context_scores_valid (n : UInt64) (hn : 0 < n) (hn4 : n ≤ 4)
    (tokens : Fin 4 → UInt64) (ht : ∀ i, (tokens i).toNat < 256)
    (position : Fin 4) (head : Fin 2) :
    let rows := fun i : Fin 4 => embedding words (tokens i) (UInt64.ofNat i.val)
    SoftmaxWide.Valid n (computedScore (rows position) (rows 0) head)
      (computedScore (rows position) (rows 1) head)
      (computedScore (rows position) (rows 2) head)
      (computedScore (rows position) (rows 3) head) := by
  have hv (i : Fin 4) :
      LayerNorm.ValidRow (rowWords (embedding words (tokens i) (UInt64.ofNat i.val))) := by
    apply embedding_valid _ _ (ht i)
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    exact i.isLt
  exact computed_scores_valid n hn hn4
    (embedding words (tokens position) (UInt64.ofNat position.val))
    (fun i => embedding words (tokens i) (UInt64.ofNat i.val)) head (hv position) hv

#print axioms computedScore_spread
#print axioms computed_scores_valid
#print axioms context_scores_valid
end Project.TinyGpt2.Checkpoint
