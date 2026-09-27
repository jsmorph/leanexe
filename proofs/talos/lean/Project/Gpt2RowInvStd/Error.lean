import Project.Gpt2RowMean.Source
import Project.Gpt2RowInvStd.Source
import Project.ProofKit.F32AverageError
import Project.ProofKit.F32PairError
import Project.ProofKit.F32DotError

namespace Project.Gpt2RowInvStd.Error
open Project.ProofKit LeanExe.Models.Gpt2 CodeLib.IEEE32

theorem mean_error (input : ByteArray) (row : Nat) (X ex : Nat → ℝ)
    (addBounds : Nat → Nat) (divBound : Nat)
    (hFinite : ∀ i < 768, CodeLib.IEEE32.Finite (word input (row * 768 + i)))
    (hError : ∀ i < 768, |value (word input (row * 768 + i)) - X i| ≤ ex i)
    (hAddUpper : ∀ i < 768, addBounds i ≤ 276)
    (hAddRange : ∀ i < 768,
      (Wasm.IEEE32.scaledValue (Project.Gpt2RowMean.sumPrefix input row i) +
        Wasm.IEEE32.scaledValue (word input (row * 768 + i))).natAbs < 2 ^ addBounds i)
    (hDivLower : 24 ≤ divBound) (hDivUpper : divBound ≤ 275)
    (hDivRange : Wasm.IEEE32.scaledMagnitude (Project.Gpt2RowMean.sumPrefix input row 768) * 2 ^ 149 ≤
      Wasm.IEEE32.scaledMagnitude 0x44400000 * 2 ^ divBound) :
    CodeLib.IEEE32.Finite (rowMean input row) ∧
      |value (rowMean input row) - (∑ i ∈ Finset.range 768, X i) / 768| ≤ F32AverageError.error ex addBounds divBound := by
  rw [Project.Gpt2RowMean.rowMean_eq, ← F32Div.div_eq]
  exact F32AverageError.average_error (fun i => word input (row * 768 + i)) X ex addBounds divBound
    hFinite hError hAddUpper hAddRange hDivLower hDivUpper hDivRange

def delta (input : ByteArray) (row : Nat) (mean : UInt32) (i : Nat) : UInt32 :=
  LeanExe.Float32.subBits (word input (row * 768 + i)) mean

theorem delta_dot (input : ByteArray) (row : Nat) (mean : UInt32) (count : Nat) :
    F32DotError.compute (delta input row mean) (delta input row mean) count =
      variancePrefix input row mean count := rfl

noncomputable def deltaError (ex : Nat → ℝ) (meanError : ℝ) (subBounds : Nat → Nat) (i : Nat) : ℝ :=
  F32AdditionBounds.epsilon (subBounds i) + (ex i + meanError)

theorem centered_error (input : ByteArray) (row : Nat) (mean : UInt32)
    (X ex : Nat → ℝ) (M meanError : ℝ) (subBounds : Nat → Nat)
    (hFinite : ∀ i < 768, CodeLib.IEEE32.Finite (word input (row * 768 + i)))
    (hMean : CodeLib.IEEE32.Finite mean)
    (hError : ∀ i < 768, |value (word input (row * 768 + i)) - X i| ≤ ex i)
    (hMeanError : |value mean - M| ≤ meanError)
    (hSubUpper : ∀ i < 768, subBounds i ≤ 276)
    (hSubRange : ∀ i < 768,
      (Wasm.IEEE32.scaledValue (word input (row * 768 + i)) - Wasm.IEEE32.scaledValue mean).natAbs < 2 ^ subBounds i)
    (i : Nat) (hi : i < 768) :
    CodeLib.IEEE32.Finite (delta input row mean i) ∧
      |value (delta input row mean i) - (X i - M)| ≤ deltaError ex meanError subBounds i := by
  have hSub := F32PairError.sub_roundoff _ mean (subBounds i) (hFinite i hi) hMean (hSubUpper i hi) (hSubRange i hi)
  have hOperands : |(value (word input (row * 768 + i)) - value mean) - (X i - M)| ≤ ex i + meanError := by
    have hEq : (value (word input (row * 768 + i)) - value mean) - (X i - M) =
        (value (word input (row * 768 + i)) - X i) - (value mean - M) := by ring
    rw [hEq]
    exact (abs_sub _ _).trans (add_le_add (hError i hi) hMeanError)
  exact ⟨hSub.1, (abs_sub_le _ _ _).trans (add_le_add hSub.2 hOperands)⟩

noncomputable def varianceError (input : ByteArray) (row : Nat) (mean : UInt32)
    (X : Nat → ℝ) (M : ℝ) (ed : Nat → ℝ) (mulBounds addBounds : Nat → Nat) : ℝ :=
  ∑ i ∈ Finset.range 768, (F32MultiplicationBounds.epsilon (mulBounds i) +
    (|value (delta input row mean i)| * ed i + ed i * |X i - M|) + F32AdditionBounds.epsilon (addBounds i))

theorem variance_error (input : ByteArray) (row : Nat) (mean : UInt32)
    (X : Nat → ℝ) (M : ℝ) (ed : Nat → ℝ) (mulBounds addBounds : Nat → Nat)
    (hFinite : ∀ i < 768, CodeLib.IEEE32.Finite (delta input row mean i))
    (hError : ∀ i < 768, |value (delta input row mean i) - (X i - M)| ≤ ed i)
    (hMulLower : ∀ i < 768, 173 ≤ mulBounds i) (hMulUpper : ∀ i < 768, mulBounds i ≤ 425)
    (hMulRange : ∀ i < 768,
      Wasm.IEEE32.scaledMagnitude (delta input row mean i) *
        Wasm.IEEE32.scaledMagnitude (delta input row mean i) < 2 ^ mulBounds i)
    (hAddUpper : ∀ i < 768, addBounds i ≤ 276)
    (hAddRange : ∀ i < 768,
      (Wasm.IEEE32.scaledValue (variancePrefix input row mean i) +
        Wasm.IEEE32.scaledValue (LeanExe.Float32.mulBits (delta input row mean i) (delta input row mean i))).natAbs < 2 ^ addBounds i) :
    CodeLib.IEEE32.Finite (variancePrefix input row mean 768) ∧
      |value (variancePrefix input row mean 768) - ∑ i ∈ Finset.range 768, (X i - M) ^ 2| ≤
        varianceError input row mean X M ed mulBounds addBounds := by
  have h := F32DotError.error (delta input row mean) (delta input row mean)
    (fun i => X i - M) (fun i => X i - M) ed ed mulBounds addBounds 768 hFinite hFinite
    hError hError hMulLower hMulUpper hMulRange hAddUpper hAddRange
  rw [delta_dot] at h
  simpa only [varianceError, pow_two] using h

#print axioms mean_error
#print axioms centered_error
#print axioms variance_error
end Project.Gpt2RowInvStd.Error
