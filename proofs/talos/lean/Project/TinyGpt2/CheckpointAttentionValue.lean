import Project.TinyGpt2.AttentionRows
import Project.TinyGpt2.CheckpointScore
import Project.TinyGpt2.CheckpointResidual

namespace Project.TinyGpt2.Checkpoint
open CodeLib.IEEE64 Project.ProofKit F64Horner

def computedProbabilities (n : UInt64) (x : Row) (rows : Context) (head : Fin 2) :
    Softmax.Result :=
  Softmax.compute n (computedScore x rows.r0 head) (computedScore x rows.r1 head)
    (computedScore x rows.r2 head) (computedScore x rows.r3 head)

def computedAttention (n : UInt64) (x : Row) (rows : Context) : Row :=
  let normalized := normContext words 2464 rows
  attentionRow n (project4 words 1040 (norm words 2464 x))
    (projectContext words 1056 normalized) (projectContext words 1072 normalized)

theorem computedAttention_words (n : UInt64) (x : Row) (rows : Context) (j : Fin 4) :
    rowWords (computedAttention n x rows) j =
      weightedValue (computedProbabilities n x rows (Real.headOf j))
        (dotColumn4 words 1072 4 j.val (norm words 2464 rows.r0))
        (dotColumn4 words 1072 4 j.val (norm words 2464 rows.r1))
        (dotColumn4 words 1072 4 j.val (norm words 2464 rows.r2))
        (dotColumn4 words 1072 4 j.val (norm words 2464 rows.r3)) := by
  simp only [computedAttention, attentionRow_words, attentionProbabilities, projectContext_rows,
    normContext_rows, project4_words,
    computedProbabilities, computedScore]
  rfl

theorem computedProbabilities_bounds (n : UInt64) (hn : 0 < n) (hn4 : n ≤ 4)
    (x : Row) (rows : Context) (head : Fin 2)
    (hx : LayerNorm.ValidRow (rowWords x))
    (hr : ∀ i, LayerNorm.ValidRow (rowWords (contextRows rows i))) :
    (∀ i, Affine.Bounded (Softmax.outputs (computedProbabilities n x rows head) i) 64) ∧
    (∀ i, 0 ≤ value (Softmax.outputs (computedProbabilities n x rows head) i)) ∧
    (∑ i, value (Softmax.outputs (computedProbabilities n x rows head) i)) ≤
      1+32*arithmeticEpsilon := by
  have hv := computed_scores_valid n hn hn4 x (contextRows rows) head hx hr
  have hp := Softmax.compute_numerical_spread _ _ _ _ _ hv
  refine ⟨probability_output_bound _ _ _ _ _ hv, fun i => (hp.2.1 i).2.1, ?_⟩
  have h := (abs_le.mp hp.2.2).2
  change (∑ i, value (Softmax.outputs (computedProbabilities n x rows head) i))-1 ≤ _ at h
  linarith

theorem computedAttention_error (n : UInt64) (hn : 0 < n) (hn4 : n ≤ 4)
    (x : Row) (rows : Context) (hx : LayerNorm.ValidRow (rowWords x))
    (hr : ∀ i, LayerNorm.ValidRow (rowWords (contextRows rows i))) (j : Fin 4) :
    Approximation (rowWords (computedAttention n x rows) j)
      (∑ i, value (Softmax.outputs (computedProbabilities n x rows (Real.headOf j)) i)*
        Real.matrixApply (decodeMatrix words 1072 4 4)
          (Real.norm (decodeNorm words 2464) (decodeRow (contextRows rows i))) j)
      16 (1/100000) := by
  let p := computedProbabilities n x rows (Real.headOf j)
  let v (i : Fin 4) := dotColumn4 words 1072 4 j.val (norm words 2464 (contextRows rows i))
  let target (i : Fin 4) := Real.matrixApply (decodeMatrix words 1072 4 4)
    (Real.norm (decodeNorm words 2464) (decodeRow (contextRows rows i))) j
  have hv (i : Fin 4) := normalized_column_error 1072 (by rw [words_size]; decide)
    value_bound (contextRows rows i) (hr i) j
  have hp := computedProbabilities_bounds n hn hn4 x rows (Real.headOf j) hx hr
  have he := weightedValue_computed_error p v hp.1
    (fun i => ⟨(hv i).finite, (hv i).magnitude.trans (by norm_num)⟩)
    target (1+32*arithmeticEpsilon) (1/200000) hp.2.1 hp.2.2 (by norm_num)
    (fun i => (hv i).accuracy)
  have ht (i : Fin 4) : |target i| ≤ 14 := by
    have h := matrix_magnitude (decodeMatrix words 1072 4 4)
      (Real.norm (decodeNorm words 2464) (decodeRow (contextRows rows i)))
      (14/5) (6/5) (by norm_num) (norm1_real_magnitude _) value_bound j
    exact h.trans (by norm_num)
  have hm := Real.weighted_magnitude (fun i => value (Softmax.outputs p i)) target
    (1+32*arithmeticEpsilon) 14 hp.2.1 hp.2.2 (by norm_num) ht
  have hout := F64ArithmeticBounds.magnitude_of_error _ _ _ _ he.2 hm
  rw [computedAttention_words]
  exact ⟨he.1, hout.trans (by norm_num [arithmeticEpsilon]),
    he.2.trans (by norm_num [arithmeticEpsilon])⟩

#print axioms computedAttention_error
end Project.TinyGpt2.Checkpoint
