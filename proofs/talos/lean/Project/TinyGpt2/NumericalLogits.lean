import Project.TinyGpt2.NumericalFeedForward
import Project.TinyGpt2.RuntimeLogits

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

def FinalFloors (w : Array UInt64) (tokens : Real.Tokens) (lower : ℝ) : Prop :=
  ∀ i, lower ≤ LayerNorm.Real.deviation (1/100000) (decodeRow (inputSecondResidual w tokens i)) ∧
    lower ≤ LayerNorm.Real.deviation (1/100000) (Real.residual2 (parameters w) tokens i)

theorem final_floors (w : Array UInt64) (tokens : Real.Tokens) :
    FinalFloors w tokens (Real.sqrt (1/100000)) :=
  fun _ => ⟨LayerNorm.Real.deviation_lower _ _, LayerNorm.Real.deviation_lower _ _⟩

theorem hidden_input_stages (w : Array UInt64) (tokens : Real.Tokens) (position : Fin 4) :
    hidden w (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2) (tokenWords tokens 3)
      (UInt64.ofNat position.val) = norm w Layout.normFinal (inputSecondResidual w tokens position) := by
  rw [hidden_runtime_stages]
  rfl

theorem inputHidden_accuracy (w : Array UInt64) (bound lower1 lower2 lowerFinal : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (tokens : Real.Tokens)
    (hl1 : 0 < lower1) (hl2 : 0 < lower2) (hlFinal : 0 < lowerFinal)
    (hf1 : EmbeddingFloors w tokens lower1) (hf2 : ResidualFloors w tokens lower2)
    (hfFinal : FinalFloors w tokens lowerFinal) (position j : Fin 4) :
    |decodeRow (hidden w (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2)
      (tokenWords tokens 3) (UInt64.ofNat position.val)) j-Real.hidden (parameters w) tokens position j| ≤
      ErrorBudget.hidden bound lower1 lower2 lowerFinal := by
  have he := inputSecondResidual_accuracy w bound lower1 lower2 hb0 hb10 hw tokens hl1 hl2 hf1 hf2 position
  have h := norm_error_wide_perturbed w Layout.normFinal (inputSecondResidual w tokens position)
    (Real.residual2 (parameters w) tokens position) 200000 bound (ErrorBudget.residual2 bound lower1 lower2) lowerFinal
    (by norm_num) (by norm_num) hb0 hb10 ((abs_nonneg _).trans (he 0)) hlFinal
    (inputSecondResidual_bounded w bound hb0 hb10 hw tokens position)
    (loaded_weights_bounded w bound hw Layout.normFinal (by decide))
    (loaded_weights_bounded w bound hw (Layout.normFinal+4) (by decide))
    (hfFinal position).1 (hfFinal position).2 he j
  rw [hidden_input_stages]
  exact h.accuracy

theorem inputLogit_accuracy (w : Array UInt64) (bound lower1 lower2 lowerFinal : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (tokens : Real.Tokens)
    (hl1 : 0 < lower1) (hl2 : 0 < lower2) (hlFinal : 0 < lowerFinal)
    (hf1 : EmbeddingFloors w tokens lower1) (hf2 : ResidualFloors w tokens lower2)
    (hfFinal : FinalFloors w tokens lowerFinal) (position : Fin 4) (j : Fin 256) :
    |value (logit w (hidden w (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2)
      (tokenWords tokens 3) (UInt64.ofNat position.val)) (UInt64.ofNat j.val))-
      Real.logits (parameters w) tokens position j| ≤ ErrorBudget.logits bound lower1 lower2 lowerFinal := by
  have he := inputHidden_accuracy w bound lower1 lower2 lowerFinal hb0 hb10 hw tokens
    hl1 hl2 hlFinal hf1 hf2 hfFinal position
  have hx := runtime_hidden_bounded w bound hb0 hb10 hw (tokenWords tokens) (tokenWords_valid tokens) position
  have hd := dotColumn4_error_perturbed w Layout.head 256 j _ _ 31 bound _
    (by norm_num) hb0 ((abs_nonneg _).trans (he 0)) (by norm_num; linarith) hx
    (matrix_weights_bounded w bound hw Layout.head 4 256 (by decide)) he
  have hm : |value (dotColumn4 w Layout.head 256 j.val
      (hidden w (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2) (tokenWords tokens 3)
        (UInt64.ofNat position.val)))| ≤ 1249 := hd.magnitude.trans (by linarith)
  have hb := hw (Layout.headBias+j.val) (by simp only [Layout.headBias, Layout.size]; omega)
  have hs := (abs_add_le _ _).trans ((add_le_add hm (hb.2.trans hb10)).trans
    (by norm_num : (1249:ℝ)+10 ≤ 1259))
  have h := add_accuracy _ _ _ _ 1259 _ 0 (by norm_num) (by norm_num) hd.finite hb.1 hs
    hd.accuracy (by simp : |value w[Layout.headBias+j.val]!-value w[Layout.headBias+j.val]!| ≤ 0)
  have hj : j.val < UInt64.size := by change j.val < 18446744073709551616; omega
  simpa only [logit, UInt64.toNat_ofNat_of_lt' hj, Real.logits, parameters,
    ErrorBudget.logits, ErrorBudget.column4, add_zero] using h

theorem infer_accuracy (w : Array UInt64) (bound lower1 lower2 lowerFinal : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (tokens : Real.Tokens)
    (hl1 : 0 < lower1) (hl2 : 0 < lower2) (hlFinal : 0 < lowerFinal)
    (hf1 : EmbeddingFloors w tokens lower1) (hf2 : ResidualFloors w tokens lower2)
    (hfFinal : FinalFloors w tokens lowerFinal) (j : Fin 256) :
    |value (infer w (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2) (tokenWords tokens 3))[j.val]!-
      Real.logits (parameters w) tokens 3 j| ≤ ErrorBudget.logits bound lower1 lower2 lowerFinal := by
  have h := inputLogit_accuracy w bound lower1 lower2 lowerFinal hb0 hb10 hw tokens
    hl1 hl2 hlFinal hf1 hf2 hfFinal 3 j
  rw [infer_eq_logitPrefix]
  simpa [logitPrefix, getElem!_pos, j.isLt] using h

theorem infer_accuracy_uniform (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (tokens : Real.Tokens) (j : Fin 256) :
    |value (infer w (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2) (tokenWords tokens 3))[j.val]!-
      Real.logits (parameters w) tokens 3 j| ≤
        ErrorBudget.logits bound (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) := by
  have hp : (0:ℝ) < Real.sqrt (1/100000) := Real.sqrt_pos.mpr (by norm_num)
  exact infer_accuracy w bound _ _ _ hb0 hb10 hw tokens hp hp hp
    (embedding_floors w tokens) (residual_floors w tokens) (final_floors w tokens) j

theorem clipped_infer_accuracy (bound : UInt64) (w : Array UInt64)
    (h : F64Clip.accepted Layout.size bound w = true) (tokens : Real.Tokens) (j : Fin 256) :
    let clipped := F64Clip.prepare Layout.size bound w
    |value (infer clipped (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2) (tokenWords tokens 3))[j.val]!-
      Real.logits (parameters clipped) tokens 3 j| ≤
        ErrorBudget.logits (value bound) (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) (Real.sqrt (1/100000)) := by
  have hb := ((F64Clip.accepted_iff Layout.size bound w).mp h).2.1
  exact infer_accuracy_uniform _ (value bound) hb.2.1 hb.2.2 (prepared_weights_bounded bound w h) tokens j

#print axioms infer_accuracy
#print axioms clipped_infer_accuracy
end Project.TinyGpt2
