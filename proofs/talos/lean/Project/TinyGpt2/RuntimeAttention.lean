import Project.TinyGpt2.RuntimeScore
import Project.TinyGpt2.AttentionRows
import Project.TinyGpt2.ProjectionRange

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem softmax_probability_bounds (n a b c d : UInt64) (h : SoftmaxWide.Valid n a b c d) :
    (∀ i, Affine.Bounded (Softmax.outputs (SoftmaxWide.compute n a b c d) i) 2) ∧
    (∀ i, 0 ≤ value (Softmax.outputs (SoftmaxWide.compute n a b c d) i)) ∧
    (∑ i, value (Softmax.outputs (SoftmaxWide.compute n a b c d) i)) ≤
      1+52*arithmeticEpsilon := by
  have he := SoftmaxWide.compute_numerical n a b c d h
  have hp := SoftmaxWide.compute_nonnegative n a b c d h
  have hm : (∑ i, value (Softmax.outputs (SoftmaxWide.compute n a b c d) i)) ≤
      1+52*arithmeticEpsilon := by linarith [(abs_le.mp he.2.2).2]
  refine ⟨?_, hp, hm⟩
  intro i
  refine ⟨he.1 i, ?_⟩
  rw [abs_of_nonneg (hp i)]
  have hi := Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  exact (hi.trans hm).trans (by norm_num [arithmeticEpsilon])

theorem weightedValue_error_wide (n a b c d : UInt64) (h : SoftmaxWide.Valid n a b c d)
    (v : Fin 4 → UInt64) (bound : ℝ) (hb1 : 1 ≤ bound) (hbMax : bound ≤ 2^30)
    (hv : ∀ i, Affine.Bounded (v i) bound) :
    Approximation (weightedValue (SoftmaxWide.compute n a b c d) (v 0) (v 1) (v 2) (v 3))
      (∑ i, Softmax.reference n (Softmax.scores a b c d) i*value (v i))
      (bound+1) ((10077*bound+6)*arithmeticEpsilon) := by
  let p := Softmax.outputs (SoftmaxWide.compute n a b c d)
  have hp := softmax_probability_bounds n a b c d h
  have hd := Affine.dot4_error_bounded p v (2*bound) (by linarith)
    (by norm_num at hbMax ⊢; linarith) (fun i => (hp.1 i).1) (fun i => (hv i).1)
    (fun i => by
      rw [abs_mul]
      exact mul_le_mul (hp.1 i).2 (hv i).2 (abs_nonneg _) (by norm_num))
  have hm := Real.weighted_magnitude (fun i => value (p i)) (fun i => value (v i))
    (1+52*arithmeticEpsilon) bound hp.2.1 hp.2.2 (by linarith) (fun i => (hv i).2)
  have hout := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hd.accuracy hm
  have he := SoftmaxWide.compute_weighted_error n a b c d h (fun i => value (v i)) bound
    (by linarith) (fun i => (hv i).2)
  refine ⟨hd.finite, hout.trans ?_, ?_⟩
  · norm_num [arithmeticEpsilon] at hbMax ⊢
    linarith
  · exact (abs_sub_le _ _ _).trans ((add_le_add hd.accuracy he).trans_eq (by ring))

def attentionScores (q : Row) (k : Context) (head : Fin 2) (i : Fin 4) : UInt64 :=
  attentionScore (rowWords q (Real.coordinate head 0)) (rowWords q (Real.coordinate head 1))
    (rowWords (contextRows k i) (Real.coordinate head 0))
    (rowWords (contextRows k i) (Real.coordinate head 1))

theorem runtime_scores_valid (n : UInt64) (hn0 : 0 < n) (hn4 : n ≤ 4)
    (q : Row) (k : Context) (head : Fin 2)
    (hq : ∀ j, Affine.Bounded (rowWords q j) 1249)
    (hk : ∀ i j, Affine.Bounded (rowWords (contextRows k i) j) 1249) :
    SoftmaxWide.Valid n (attentionScores q k head 0) (attentionScores q k head 1)
      (attentionScores q k head 2) (attentionScores q k head 3) := by
  have hs (i : Fin 4) : Affine.Bounded (attentionScores q k head i) 4000000 :=
    attentionScore_bounded _ _ _ _ (hq _) (hq _) (hk i _) (hk i _)
  have hi (i : Fin 4) : Softmax.scores (attentionScores q k head 0) (attentionScores q k head 1)
      (attentionScores q k head 2) (attentionScores q k head 3) i = attentionScores q k head i := by
    fin_cases i <;> rfl
  refine ⟨hn0, hn4, ?_, ?_⟩
  · intro i
    rw [hi]
    exact (hs i).1
  · intro i j _ _
    rw [hi, hi]
    exact ((abs_sub _ _).trans (add_le_add (hs i).2 (hs j).2)).trans_lt (by norm_num)

theorem runtime_attention_bounded (n : UInt64) (hn0 : 0 < n) (hn4 : n ≤ 4)
    (q : Row) (k v : Context)
    (hq : ∀ j, Affine.Bounded (rowWords q j) 1249)
    (hk : ∀ i j, Affine.Bounded (rowWords (contextRows k i) j) 1249)
    (hv : ∀ i j, Affine.Bounded (rowWords (contextRows v i) j) 1249) (j : Fin 4) :
    Affine.Bounded (rowWords (attentionRow n q k v) j) 1250 := by
  have hs := runtime_scores_valid n hn0 hn4 q k (Real.headOf j) hq hk
  have he := weightedValue_error_wide n _ _ _ _ hs
    (fun i => rowWords (contextRows v i) j) 1249 (by norm_num) (by norm_num) (fun i => hv i j)
  rw [attentionRow_words]
  exact ⟨he.finite, he.magnitude.trans (by norm_num)⟩

#print axioms weightedValue_error_wide
#print axioms runtime_attention_bounded
end Project.TinyGpt2
