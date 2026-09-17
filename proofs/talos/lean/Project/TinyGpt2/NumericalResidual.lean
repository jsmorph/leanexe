import Project.TinyGpt2.NumericalAttention

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

def inputResidual (w : Array UInt64) (tokens : Real.Tokens) (position : Fin 4) : Row :=
  residualRow w (UInt64.ofNat (position.val+1)) (inputRow w tokens position)
    (embeddedContext w (tokenWords tokens))

def ResidualFloors (w : Array UInt64) (tokens : Real.Tokens) (lower : ℝ) : Prop :=
  ∀ i, lower ≤ LayerNorm.Real.deviation (1/100000) (decodeRow (inputResidual w tokens i)) ∧
    lower ≤ LayerNorm.Real.deviation (1/100000) (Real.residual1 (parameters w) tokens i)

theorem residual_floors (w : Array UInt64) (tokens : Real.Tokens) :
    ResidualFloors w tokens (Real.sqrt (1/100000)) :=
  fun _ => ⟨LayerNorm.Real.deviation_lower _ _, LayerNorm.Real.deviation_lower _ _⟩

theorem inputAttention_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (position j : Fin 4) :
    Affine.Bounded (rowWords (inputAttention w tokens position) j) 1250 := by
  have hm := (projectionMagnitude_range bound hb0 hb10).2.trans (by norm_num : (1201:ℝ) ≤ 1249)
  have hc (offset : Nat) (ho : offset+16 ≤ Layout.size) (i k : Fin 4) :
      Affine.Bounded (rowWords (contextRows (projectedContext w tokens offset) i) k) 1249 := by
    rw [projectedContext_rows]
    exact (projected_input_bounded w bound hb0 hb10 hw tokens offset ho i k).weaken hm
  exact runtime_attention_bounded _ (by fin_cases position <;> decide) (by fin_cases position <;> decide)
    _ _ _ (fun k => (projected_input_bounded w bound hb0 hb10 hw tokens Layout.query (by decide) position k).weaken hm)
    (hc Layout.key (by decide)) (hc Layout.value (by decide)) j

theorem inputResidual_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (position j : Fin 4) :
    Affine.Bounded (rowWords (inputResidual w tokens position) j) 60000 :=
  runtime_residual_bounded w bound hb0 hb10 hw _ (by fin_cases position <;> decide)
    (by fin_cases position <;> decide) _ _ (inputRow_bounded w bound hb10 hw tokens position)
    (inputRow_bounded w bound hb10 hw tokens) j

theorem inputResidual_accuracy (w : Array UInt64) (bound lower : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl : 0 < lower) (hf : EmbeddingFloors w tokens lower) (position j : Fin 4) :
    |decodeRow (inputResidual w tokens position) j-Real.residual1 (parameters w) tokens position j| ≤
      ErrorBudget.residual1 bound lower := by
  have ha := inputAttention_accuracy w bound lower hb0 hb10 hw tokens hl hf position
  have hd := dotColumn4_error_perturbed w Layout.attention 4 j (inputAttention w tokens position)
    (Real.attended (parameters w) tokens position) 1250 bound (ErrorBudget.attention bound lower)
    (by norm_num) hb0 ((abs_nonneg _).trans (ha 0)) (by norm_num; linarith)
    (inputAttention_bounded w bound hb0 hb10 hw tokens position)
    (matrix_weights_bounded w bound hw Layout.attention 4 4 (by decide)) ha
  have hdm : |value (dotColumn4 w Layout.attention 4 j.val (inputAttention w tokens position))| ≤ 50009 :=
    hd.magnitude.trans (by linarith)
  have hb := loaded_weights_bounded w bound hw Layout.attentionBias (by decide) j
  have hsum := (abs_add_le _ _).trans ((add_le_add hdm (hb.2.trans hb10)).trans
    (by norm_num : (50009:ℝ)+10 ≤ 50019))
  have hatt := add_error_wide _ _ 50019 (by norm_num) (by norm_num) hd.finite hb.1 hsum
  have hatte := add_accuracy _ _ _ _ 50019 _ 0 (by norm_num) (by norm_num) hd.finite hb.1 hsum
    hd.accuracy (by simp : |value (rowWords (loadRow w Layout.attentionBias) j)-
      value (rowWords (loadRow w Layout.attentionBias) j)| ≤ 0)
  have he := inputRow_accuracy w bound hb0 hb10 hw tokens position j
  have heb := inputRow_bounded w bound hb10 hw tokens position j
  have htotal := (abs_add_le _ _).trans ((add_le_add heb.2 hatt.magnitude).trans
    (by norm_num : (21:ℝ)+(50019+1) ≤ 50041))
  have hout := add_accuracy _ _ _ _ 50041 _ _ (by norm_num) (by norm_num) heb.1 hatt.finite htotal he hatte
  simpa only [inputResidual, residualRow, inputAttention, inputQuery, projectedContext, inputRow,
    decodeRow, addRows_words, project4_words, Real.residual1, parameters, add_assoc, add_zero,
    ErrorBudget.residual1, ErrorBudget.column4] using hout

theorem normalized_residual_accuracy (w : Array UInt64) (bound lower1 lower2 : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl1 : 0 < lower1) (hl2 : 0 < lower2)
    (hf1 : EmbeddingFloors w tokens lower1) (hf2 : ResidualFloors w tokens lower2) (position j : Fin 4) :
    |decodeRow (norm w Layout.norm2 (inputResidual w tokens position)) j-
      Real.norm (parameters w).norm2 (Real.residual1 (parameters w) tokens position) j| ≤
      ErrorBudget.normalization 60000 bound (ErrorBudget.residual1 bound lower1) lower2 := by
  have he := inputResidual_accuracy w bound lower1 hb0 hb10 hw tokens hl1 hf1 position
  have h := norm_error_wide_perturbed w Layout.norm2 (inputResidual w tokens position)
    (Real.residual1 (parameters w) tokens position) 60000 bound (ErrorBudget.residual1 bound lower1) lower2
    (by norm_num) (by norm_num) hb0 hb10 ((abs_nonneg _).trans (he 0)) hl2
    (inputResidual_bounded w bound hb0 hb10 hw tokens position)
    (loaded_weights_bounded w bound hw Layout.norm2 (by decide))
    (loaded_weights_bounded w bound hw (Layout.norm2+4) (by decide)) (hf2 position).1 (hf2 position).2 he j
  exact h.accuracy

#print axioms inputResidual_accuracy
#print axioms normalized_residual_accuracy
end Project.TinyGpt2
