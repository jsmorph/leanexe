import Project.Gpt2QuantizedGroupedRows.OutputError

namespace Project.Gpt2QuantizedGroupedRows.UniformError
open LeanExe.Models.Gpt2 Project.ProofKit ForwardError CodeLib.IEEE32

def bounds (scaleBound outputBound addBound biasBound : Nat) : OutputError.Bounds :=
  ⟨fun _ => scaleBound, fun _ => outputBound, fun _ => addBound, biasBound⟩

noncomputable def term (inputMagnitude weightMagnitude inputError weightError : ℝ) : ℝ :=
  weightMagnitude * inputError + inputMagnitude * weightError + inputError * weightError

noncomputable def groupUpper (inputMagnitude weightMagnitude inputError weightError : ℝ)
    (scaleBound outputBound : Nat) : ℝ :=
  F32MultiplicationBounds.epsilon outputBound + 1032256 * F32MultiplicationBounds.epsilon scaleBound +
    64 * term inputMagnitude weightMagnitude inputError weightError

noncomputable def upper (width : Nat) (withBias : Bool) (inputMagnitude weightMagnitude inputError weightError : ℝ)
    (scaleBound outputBound addBound biasBound : Nat) : ℝ :=
  ((width / 64 : Nat) : ℝ) * (groupUpper inputMagnitude weightMagnitude inputError weightError scaleBound outputBound +
    F32AdditionBounds.epsilon addBound) + if withBias then F32AdditionBounds.epsilon biasBound else 0

theorem group_upper (weights input : ByteArray) (weightOffset scaleOffset width row group scaleBound outputBound : Nat)
    (X W ex ew : Nat → ℝ) (inputMagnitude weightMagnitude inputError weightError : ℝ)
    (h : GroupRanges weights input weightOffset scaleOffset width 1 0 row group scaleBound outputBound X W ex ew)
    (hx : ∀ i < 64, |X (group * 64 + i)| ≤ inputMagnitude)
    (hw : ∀ i < 64, |W (group * 64 + i)| ≤ weightMagnitude)
    (hex : ∀ i < 64, 0 ≤ ex (group * 64 + i) ∧ ex (group * 64 + i) ≤ inputError)
    (hew : ∀ i < 64, 0 ≤ ew (group * 64 + i) ∧ ew (group * 64 + i) ≤ weightError) :
    groupError weights input weightOffset width 1 0 row group X W ex ew scaleBound outputBound ≤
      groupUpper inputMagnitude weightMagnitude inputError weightError scaleBound outputBound := by
  have ha := group_accumulator_bound weights (Quantized.quantizeRows input 64 (1 * (width / 64))).values
    (weightOffset + row * width + group * 64) (0 * width + group * 64) 64 (by decide) h.inputValid h.weightValid
  have har : |(LeanExe.Signed32.decode (accumulator weights input weightOffset width 1 0 row group) : ℝ)| ≤ 1032256 := by
    exact_mod_cast ha
  have hs : (∑ i ∈ Finset.range 64, (|W (group * 64 + i)| * ex (group * 64 + i) +
      |X (group * 64 + i)| * ew (group * 64 + i) + ex (group * 64 + i) * ew (group * 64 + i))) ≤
      64 * term inputMagnitude weightMagnitude inputError weightError := by
    calc
      _ ≤ ∑ _i ∈ Finset.range 64, term inputMagnitude weightMagnitude inputError weightError := by
        apply Finset.sum_le_sum
        intro i hi
        have hi := Finset.mem_range.mp hi
        have hX := hx i hi
        have hW := hw i hi
        have hE := hex i hi
        have hD := hew i hi
        have hW0 := (abs_nonneg (W (group * 64 + i))).trans hW
        have hX0 := (abs_nonneg (X (group * 64 + i))).trans hX
        exact add_le_add (add_le_add (mul_le_mul hW hE.2 hE.1 hW0)
          (mul_le_mul hX hD.2 hD.1 hX0)) (mul_le_mul hE.2 hD.2 hD.1 (hE.1.trans hE.2))
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_right har
    (show 0 ≤ F32MultiplicationBounds.epsilon scaleBound from by unfold F32MultiplicationBounds.epsilon; positivity)
  exact add_le_add (add_le_add le_rfl hm) hs

theorem error_upper (weights input : ByteArray) (weightOffset scaleOffset biasOffset width row : Nat)
    (withBias : Bool) (X W ex ew : Nat → ℝ) (inputMagnitude weightMagnitude inputError weightError : ℝ)
    (scaleBound outputBound addBound biasBound : Nat)
    (h : OutputError.Ranges weights input weightOffset scaleOffset biasOffset width row withBias X W ex ew
      (bounds scaleBound outputBound addBound biasBound))
    (hx : ∀ i < width, |X i| ≤ inputMagnitude) (hw : ∀ i < width, |W i| ≤ weightMagnitude)
    (hex : ∀ i < width, 0 ≤ ex i ∧ ex i ≤ inputError)
    (hew : ∀ i < width, 0 ≤ ew i ∧ ew i ≤ weightError) :
    OutputError.error weights input weightOffset width row withBias X W ex ew
      (bounds scaleBound outputBound addBound biasBound) ≤
      upper width withBias inputMagnitude weightMagnitude inputError weightError scaleBound outputBound addBound biasBound := by
  unfold OutputError.error upper
  apply add_le_add _ le_rfl
  calc
    _ ≤ ∑ _g ∈ Finset.range (width / 64),
        (groupUpper inputMagnitude weightMagnitude inputError weightError scaleBound outputBound +
          F32AdditionBounds.epsilon addBound) := by
      apply Finset.sum_le_sum
      intro g hg
      have hg := Finset.mem_range.mp hg
      exact add_le_add (group_upper weights input weightOffset scaleOffset width row g scaleBound outputBound
        X W ex ew inputMagnitude weightMagnitude inputError weightError (h.groups g hg)
        (fun i hi => hx _ (by omega)) (fun i hi => hw _ (by omega))
        (fun i hi => hex _ (by omega)) (fun i hi => hew _ (by omega))) le_rfl
    _ = _ := by simp; ring

#print axioms group_upper
#print axioms error_upper
end Project.Gpt2QuantizedGroupedRows.UniformError
