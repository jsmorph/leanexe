import Project.Gpt2CachedStep.CachedAttention.NumericalSource
import Project.Gpt2CachedStep.CachedScore.Error
import Project.Softmax.WeightedPerturbation

namespace Project.Gpt2CachedStep.CachedAttention.ForwardError
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32 NumericalSource

def scoreWords (cache qkv : ByteArray) (layer position head : Nat) : Nat → UInt32 :=
  rowScores (scores cache qkv layer position) head (position + 1)

def maximumWord (cache qkv : ByteArray) (layer position head : Nat) : UInt32 :=
  NumericalSource.rowMaximum (scores cache qkv layer position) head (position + 1)

def probabilityWords (cache qkv : ByteArray) (layer position i : Nat) : Nat → UInt32 :=
  fun j => word (probabilityValues cache qkv layer position) (i / 64 * (position + 1) + j)

def valueWords (cache qkv : ByteArray) (layer position i : Nat) : Nat → UInt32 :=
  fun j => cachedKv cache qkv layer position j (768 + i)

noncomputable def realProbability (cache qkv : ByteArray) (layer position head : Nat) (j : Fin (position + 1)) : ℝ :=
  Project.Softmax.Real.probability (fun _ : Fin (position + 1) => true)
    (fun k => value (scoreWords cache qkv layer position head k)) j

noncomputable def probabilityError (cache qkv : ByteArray) (layer position head : Nat)
    (b : SoftmaxError.Bounds) (j : Nat) : ℝ :=
  SoftmaxError.error (scoreWords cache qkv layer position head)
    (maximumWord cache qkv layer position head) b (position + 1) j

structure Bounds where
  softmax : SoftmaxError.Bounds
  mulBound : Nat → Nat
  addBound : Nat → Nat

structure Ranges (cache qkv : ByteArray) (layer position i : Nat) (b : Bounds) : Prop where
  softmax : SoftmaxError.Ranges (scoreWords cache qkv layer position (i / 64))
    (maximumWord cache qkv layer position (i / 64)) b.softmax (position + 1)
  valueFinite : ∀ j < position + 1, CodeLib.IEEE32.Finite (valueWords cache qkv layer position i j)
  mulLower : ∀ j < position + 1, 173 ≤ b.mulBound j
  mulUpper : ∀ j < position + 1, b.mulBound j ≤ 425
  mulRange : ∀ j < position + 1, Wasm.IEEE32.scaledMagnitude (probabilityWords cache qkv layer position i j) *
    Wasm.IEEE32.scaledMagnitude (valueWords cache qkv layer position i j) < 2 ^ b.mulBound j
  addUpper : ∀ j < position + 1, b.addBound j ≤ 276
  addRange : ∀ j < position + 1,
    (Wasm.IEEE32.scaledValue (mixedPrefix cache qkv (probabilityValues cache qkv layer position) layer position i j) +
      Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (probabilityWords cache qkv layer position i j)
        (valueWords cache qkv layer position i j))).natAbs < 2 ^ b.addBound j

noncomputable def roundingError (cache qkv : ByteArray) (layer position i : Nat) (b : Bounds) : ℝ :=
  ∑ j ∈ Finset.range (position + 1), (F32MultiplicationBounds.epsilon (b.mulBound j) +
    probabilityError cache qkv layer position (i / 64) b.softmax j * |value (valueWords cache qkv layer position i j)| +
      F32AdditionBounds.epsilon (b.addBound j))

theorem probability_error (cache qkv : ByteArray) (layer position i : Nat) (hi : i < 768)
    (b : Bounds) (h : Ranges cache qkv layer position i b) (j : Fin (position + 1)) :
    CodeLib.IEEE32.Finite (probabilityWords cache qkv layer position i j) ∧
      |value (probabilityWords cache qkv layer position i j) - realProbability cache qkv layer position (i / 64) j| ≤
        probabilityError cache qkv layer position (i / 64) b.softmax j := by
  have hh : i / 64 < 12 := by omega
  unfold probabilityWords probabilityValues
  rw [probability_word _ (i / 64) (position + 1) j hh j.isLt]
  exact SoftmaxError.probability_real _ _ _ _ h.softmax j

theorem mixed_compute (cache qkv : ByteArray) (layer position i count : Nat) :
    mixedPrefix cache qkv (probabilityValues cache qkv layer position) layer position i count =
      F32DotError.compute (probabilityWords cache qkv layer position i)
        (valueWords cache qkv layer position i) count := rfl

theorem rounding_error (cache qkv : ByteArray) (layer position i : Nat) (hi : i < 768)
    (b : Bounds) (h : Ranges cache qkv layer position i b) :
    CodeLib.IEEE32.Finite (word (cachedAttention cache qkv layer position) i) ∧
      |value (word (cachedAttention cache qkv layer position) i) -
        ∑ j : Fin (position + 1), realProbability cache qkv layer position (i / 64) j *
          value (valueWords cache qkv layer position i j)| ≤ roundingError cache qkv layer position i b := by
  let P : Nat → ℝ := fun j => if hj : j < position + 1 then realProbability cache qkv layer position (i / 64) ⟨j, hj⟩ else 0
  have he (j : Nat) (hj : j < position + 1) := probability_error cache qkv layer position i hi b h ⟨j, hj⟩
  have hd := F32DotError.error (probabilityWords cache qkv layer position i) (valueWords cache qkv layer position i)
    P (fun j => value (valueWords cache qkv layer position i j))
    (probabilityError cache qkv layer position (i / 64) b.softmax) (fun _ => 0)
    b.mulBound b.addBound (position + 1) (fun j hj => (he j hj).1) h.valueFinite
    (fun j hj => by simpa only [P, dif_pos hj] using (he j hj).2) (by intro j hj; simp)
    h.mulLower h.mulUpper h.mulRange h.addUpper h.addRange
  rw [attention_word cache qkv layer position i hi, mixed_compute]
  simp only [mul_zero, zero_add] at hd
  rw [← Fin.sum_univ_eq_sum_range] at hd
  simpa only [P, dif_pos (Fin.isLt _), roundingError] using hd

theorem component_error (cache qkv : ByteArray) (layer position i : Nat) (hi : i < 768)
    (b : Bounds) (h : Ranges cache qkv layer position i b)
    (S V : Fin (position + 1) → ℝ) (scoreError valueError valueBound : ℝ)
    (hs : 0 ≤ scoreError) (hv : 0 ≤ valueBound)
    (hScore : ∀ j : Fin (position + 1), |value (scoreWords cache qkv layer position (i / 64) j) - S j| ≤ scoreError)
    (hValue : ∀ j : Fin (position + 1), |value (valueWords cache qkv layer position i j) - V j| ≤ valueError)
    (hMagnitude : ∀ j : Fin (position + 1), |value (valueWords cache qkv layer position i j)| ≤ valueBound) :
    CodeLib.IEEE32.Finite (word (cachedAttention cache qkv layer position) i) ∧
      |value (word (cachedAttention cache qkv layer position) i) -
        ∑ j, Project.Softmax.Real.probability (fun _ : Fin (position + 1) => true) S j * V j| ≤
      roundingError cache qkv layer position i b + (2 * valueBound * scoreError + valueError) := by
  have hr := rounding_error cache qkv layer position i hi b h
  have hp := Project.Softmax.Real.attention_perturbation (fun _ : Fin (position + 1) => true)
    (fun j => value (scoreWords cache qkv layer position (i / 64) j)) S
    (fun j => value (valueWords cache qkv layer position i j)) V scoreError valueError valueBound
    ⟨⟨0, by omega⟩, rfl⟩ hs hv hScore hMagnitude hValue
  exact ⟨hr.1, (abs_sub_le _ _ _).trans (add_le_add hr.2 hp)⟩

#print axioms rounding_error
#print axioms component_error
end Project.Gpt2CachedStep.CachedAttention.ForwardError
