import Project.Gpt2CachedStep.CachedAttention.ForwardError

namespace Project.Gpt2CachedStep.CachedAttention.ScoreSource
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32
open LayerNorm.Numerical (word_generate)
open ForwardError

theorem score_word (cache qkv : ByteArray) (layer position head j : Nat)
    (hh : head < 12) (hj : j < position + 1) :
    scoreWords cache qkv layer position head j = cachedScore cache qkv layer position j head := by
  unfold scoreWords NumericalSource.rowScores scores
  rw [word_generate _ _ _ (NumericalSource.row_index head (position + 1) j hh hj)]
  rw [NumericalSource.row_div head (position + 1) j hj]
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hj]

noncomputable def referenceScore (Q : Nat → ℝ) (K : Nat → Nat → ℝ) (j : Nat) : ℝ :=
  (∑ channel ∈ Finset.range 64, Q channel * K j channel) / 8

theorem score_error (cache qkv : ByteArray) (layer position head : Nat) (hh : head < 12)
    (bounds : Nat → CachedScore.Error.Bounds) (Q : Nat → ℝ) (K : Nat → Nat → ℝ)
    (queryError : Nat → ℝ) (keyError : Nat → Nat → ℝ)
    (hRange : ∀ j < position + 1, CachedScore.Error.Ranges cache qkv layer position j head (bounds j))
    (hQuery : ∀ i < 64, |value (CachedScore.Error.query qkv head i) - Q i| ≤ queryError i)
    (hKey : ∀ j < position + 1, ∀ i < 64,
      |value (CachedScore.Error.key cache qkv layer position j head i) - K j i| ≤ keyError j i)
    (bound : ℝ) (hBound : ∀ j < position + 1,
      CachedScore.Error.error qkv head (K j) queryError (keyError j) (bounds j) ≤ bound)
    (j : Fin (position + 1)) :
    |value (scoreWords cache qkv layer position head j) - referenceScore Q K j| ≤ bound := by
  rw [score_word cache qkv layer position head j hh j.isLt]
  exact (CachedScore.Error.score_error cache qkv layer position j head (bounds j)
    Q (K j) queryError (keyError j) (hRange j j.isLt) hQuery (hKey j j.isLt)).2.trans (hBound j j.isLt)

theorem attention_error (cache qkv : ByteArray) (layer position i : Nat) (hi : i < 768)
    (b : ForwardError.Bounds) (h : ForwardError.Ranges cache qkv layer position i b)
    (scoreBounds : Nat → CachedScore.Error.Bounds) (Q : Nat → ℝ) (K : Nat → Nat → ℝ)
    (queryError : Nat → ℝ) (keyError : Nat → Nat → ℝ)
    (hRange : ∀ j < position + 1, CachedScore.Error.Ranges cache qkv layer position j (i / 64) (scoreBounds j))
    (hQuery : ∀ c < 64, |value (CachedScore.Error.query qkv (i / 64) c) - Q c| ≤ queryError c)
    (hKey : ∀ j < position + 1, ∀ c < 64,
      |value (CachedScore.Error.key cache qkv layer position j (i / 64) c) - K j c| ≤ keyError j c)
    (scoreBound valueError valueBound : ℝ) (hs : 0 ≤ scoreBound) (hv : 0 ≤ valueBound)
    (hBound : ∀ j < position + 1,
      CachedScore.Error.error qkv (i / 64) (K j) queryError (keyError j) (scoreBounds j) ≤ scoreBound)
    (V : Fin (position + 1) → ℝ)
    (hValue : ∀ j : Fin (position + 1), |value (valueWords cache qkv layer position i j) - V j| ≤ valueError)
    (hMagnitude : ∀ j : Fin (position + 1), |value (valueWords cache qkv layer position i j)| ≤ valueBound) :
    CodeLib.IEEE32.Finite (word (cachedAttention cache qkv layer position) i) ∧
      |value (word (cachedAttention cache qkv layer position) i) -
        ∑ j : Fin (position + 1), Project.Softmax.Real.probability (fun _ : Fin (position + 1) => true)
          (fun j => referenceScore Q K j) j * V j| ≤
      roundingError cache qkv layer position i b + (2 * valueBound * scoreBound + valueError) := by
  apply ForwardError.component_error cache qkv layer position i hi b h _ V scoreBound valueError valueBound hs hv
  · exact score_error cache qkv layer position (i / 64) (by omega) scoreBounds Q K queryError keyError
      hRange hQuery hKey scoreBound hBound
  · exact hValue
  · exact hMagnitude

#print axioms attention_error
end Project.Gpt2CachedStep.CachedAttention.ScoreSource
