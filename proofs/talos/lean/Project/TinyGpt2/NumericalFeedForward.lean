import Project.TinyGpt2.NumericalResidual
import Project.TinyGpt2.RuntimeFeedForward

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

def inputSecondResidual (w : Array UInt64) (tokens : Real.Tokens) (position : Fin 4) : Row :=
  let x := inputResidual w tokens position
  addRows x (contractRow w (activatedRow w x))

theorem inputExpanded_accuracy (w : Array UInt64) (bound lower1 lower2 : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl1 : 0 < lower1) (hl2 : 0 < lower2)
    (hf1 : EmbeddingFloors w tokens lower1) (hf2 : ResidualFloors w tokens lower2)
    (position : Fin 4) (j : Fin 8) :
    |value (wideWords (expandRow w (norm w Layout.norm2 (inputResidual w tokens position))) j)-
      Real.expanded (parameters w) tokens position j| ≤ ErrorBudget.expanded bound lower1 lower2 := by
  have he := normalized_residual_accuracy w bound lower1 lower2 hb0 hb10 hw tokens hl1 hl2 hf1 hf2 position
  have hn := runtime_norm_bounded w bound hb0 hb10 hw Layout.norm2 (by decide) _
    (fun i => (inputResidual_bounded w bound hb0 hb10 hw tokens position i).weaken (by norm_num))
  have hd := dotColumn4_error_perturbed w 1108 8 j _ _ 31 bound _
    (by norm_num) hb0 ((abs_nonneg _).trans (he 0)) (by norm_num; linarith) hn
    (matrix_weights_bounded w bound hw 1108 4 8 (by decide)) he
  have hm : |value (dotColumn4 w 1108 8 j.val (norm w Layout.norm2 (inputResidual w tokens position)))| ≤ 1249 :=
    hd.magnitude.trans (by linarith)
  have hb := hw (1140+j.val) (by simp only [Layout.size]; omega)
  have hs := (abs_add_le _ _).trans ((add_le_add hm (hb.2.trans hb10)).trans
    (by norm_num : (1249:ℝ)+10 ≤ 1259))
  have h := add_accuracy _ _ _ _ 1259 _ 0 (by norm_num) (by norm_num) hd.finite hb.1 hs
    hd.accuracy (by simp : |value w[1140+j.val]!-value w[1140+j.val]!| ≤ 0)
  simpa only [expandRow_words, Real.expanded, parameters, Layout.expand, Layout.expandBias,
    ErrorBudget.expanded, ErrorBudget.column4, add_zero] using h

theorem inputActivated_accuracy (w : Array UInt64) (bound lower1 lower2 : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl1 : 0 < lower1) (hl2 : 0 < lower2)
    (hf1 : EmbeddingFloors w tokens lower1) (hf2 : ResidualFloors w tokens lower2)
    (position : Fin 4) (j : Fin 8) :
    |value (wideWords (activatedRow w (inputResidual w tokens position)) j)-
      Real.activated (parameters w) tokens position j| ≤ ErrorBudget.activated bound lower1 lower2 := by
  have he := inputExpanded_accuracy w bound lower1 lower2 hb0 hb10 hw tokens hl1 hl2 hf1 hf2 position j
  have hx := runtime_expanded_bounded w bound hb0 hb10 hw _
    (fun i => (inputResidual_bounded w bound hb0 hb10 hw tokens position i).weaken (by norm_num)) j
  have h := GeluWide.evaluateAll_perturbed _ _ _ hx.1 he
  simpa only [activatedRow, activateWide_words, Real.activated, ErrorBudget.activated] using h

theorem inputContracted_accuracy (w : Array UInt64) (bound lower1 lower2 : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl1 : 0 < lower1) (hl2 : 0 < lower2)
    (hf1 : EmbeddingFloors w tokens lower1) (hf2 : ResidualFloors w tokens lower2) (position j : Fin 4) :
    |decodeRow (contractRow w (activatedRow w (inputResidual w tokens position))) j-
      (Real.matrixApply (parameters w).contract (Real.activated (parameters w) tokens position) j+
        (parameters w).contractBias j)| ≤ ErrorBudget.contracted bound lower1 lower2 := by
  have he := inputActivated_accuracy w bound lower1 lower2 hb0 hb10 hw tokens hl1 hl2 hf1 hf2 position
  have hx := runtime_activated_bounded w bound hb0 hb10 hw _
    (fun i => (inputResidual_bounded w bound hb0 hb10 hw tokens position i).weaken (by norm_num))
  have hd := dotColumn8_error_perturbed w 1148 4 j _ _ 1261 bound _
    (by norm_num) hb0 ((abs_nonneg _).trans (he 0)) (by norm_num; linarith) hx
    (matrix_weights_bounded w bound hw 1148 8 4 (by decide)) he
  have hm : |value (dotColumn8 w 1148 4 j.val (activatedRow w (inputResidual w tokens position)))| ≤ 100899 :=
    hd.magnitude.trans (by linarith)
  have hb := hw (1180+j.val) (by simp only [Layout.size]; omega)
  have hs := (abs_add_le _ _).trans ((add_le_add hm (hb.2.trans hb10)).trans
    (by norm_num : (100899:ℝ)+10 ≤ 100909))
  have h := add_accuracy _ _ _ _ 100909 _ 0 (by norm_num) (by norm_num) hd.finite hb.1 hs
    hd.accuracy (by simp : |value w[1180+j.val]!-value w[1180+j.val]!| ≤ 0)
  simpa only [decodeRow, contractRow_words, parameters, Layout.contract, Layout.contractBias, loadRow_words,
    ErrorBudget.contracted, ErrorBudget.column8, add_zero] using h

theorem inputSecondResidual_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (position j : Fin 4) :
    Affine.Bounded (rowWords (inputSecondResidual w tokens position) j) 200000 := by
  have hr := inputResidual_bounded w bound hb0 hb10 hw tokens position
  have ha := runtime_activated_bounded w bound hb0 hb10 hw _ (fun i => (hr i).weaken (by norm_num))
  have hc := runtime_contracted_bounded w bound hb0 hb10 hw _ ha
  exact (addRows_bounded _ _ 60000 100910 (by norm_num) (by norm_num) hr hc j).weaken (by norm_num)

theorem inputSecondResidual_accuracy (w : Array UInt64) (bound lower1 lower2 : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl1 : 0 < lower1) (hl2 : 0 < lower2)
    (hf1 : EmbeddingFloors w tokens lower1) (hf2 : ResidualFloors w tokens lower2) (position j : Fin 4) :
    |decodeRow (inputSecondResidual w tokens position) j-Real.residual2 (parameters w) tokens position j| ≤
      ErrorBudget.residual2 bound lower1 lower2 := by
  have hr := inputResidual_bounded w bound hb0 hb10 hw tokens position
  have ha := runtime_activated_bounded w bound hb0 hb10 hw _ (fun i => (hr i).weaken (by norm_num))
  have hc := runtime_contracted_bounded w bound hb0 hb10 hw _ ha
  have hre := inputResidual_accuracy w bound lower1 hb0 hb10 hw tokens hl1 hf1 position j
  have hce := inputContracted_accuracy w bound lower1 lower2 hb0 hb10 hw tokens hl1 hl2 hf1 hf2 position j
  have h := add_accuracy _ _ _ _ 160910 _ _ (by norm_num) (by norm_num) (hr j).1 (hc j).1
    ((abs_add_le _ _).trans ((add_le_add (hr j).2 (hc j).2).trans (by norm_num))) hre hce
  simpa only [decodeRow, inputSecondResidual, addRows_words, Real.residual2, add_assoc, ErrorBudget.residual2] using h

#print axioms inputActivated_accuracy
#print axioms inputSecondResidual_accuracy
end Project.TinyGpt2
