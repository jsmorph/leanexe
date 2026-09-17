import Project.TinyGpt2.NumericalInputs

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

def projectedContext (w : Array UInt64) (tokens : Real.Tokens) (offset : Nat) : Context :=
  projectContext w offset (normContext w Layout.norm1 (embeddedContext w (tokenWords tokens)))

def inputQuery (w : Array UInt64) (tokens : Real.Tokens) (position : Fin 4) : Row :=
  project4 w Layout.query (norm w Layout.norm1 (inputRow w tokens position))

def inputAttention (w : Array UInt64) (tokens : Real.Tokens) (position : Fin 4) : Row :=
  attentionRow (UInt64.ofNat (position.val+1)) (inputQuery w tokens position)
    (projectedContext w tokens Layout.key) (projectedContext w tokens Layout.value)

theorem projectedContext_rows (w : Array UInt64) (tokens : Real.Tokens) (offset : Nat) (i : Fin 4) :
    contextRows (projectedContext w tokens offset) i =
      project4 w offset (norm w Layout.norm1 (inputRow w tokens i)) := by
  rw [projectedContext, projectContext_rows, normContext_rows]
  rfl

theorem projectionMagnitude_range (bound : ℝ) (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) :
    1 ≤ ErrorBudget.projectionMagnitude bound ∧ ErrorBudget.projectionMagnitude bound ≤ 1201 := by
  have hb2 : bound*bound ≤ 100 := (mul_le_mul hb10 hb10 hb0 (by norm_num)).trans_eq (by norm_num)
  unfold ErrorBudget.projectionMagnitude
  constructor <;> nlinarith [sq_nonneg bound]

theorem inputScore_accuracy (w : Array UInt64) (bound lower : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl : 0 < lower) (hf : EmbeddingFloors w tokens lower)
    (position : Fin 4) (head : Fin 2) (i : Fin 4) :
    |value (attentionScores (inputQuery w tokens position) (projectedContext w tokens Layout.key) head i)-
      Real.score (parameters w) tokens position head i| ≤ ErrorBudget.score bound lower := by
  have hqe := projected_input_accuracy w bound lower hb0 hb10 hw tokens hl hf Layout.query (by decide) position
  have hke := projected_input_accuracy w bound lower hb0 hb10 hw tokens hl hf Layout.key (by decide) i
  have hqb := projected_input_bounded w bound hb0 hb10 hw tokens Layout.query (by decide) position
  have hkb := projected_input_bounded w bound hb0 hb10 hw tokens Layout.key (by decide) i
  have hp := parameters_bounded w bound (fun j hj => (hw j hj).2)
  have hqr := Real.normalized_projection_magnitude _ _ (Real.embedding (parameters w) tokens position)
    bound hb0 hp.norm1 hp.query
  have hm := projectionMagnitude_range bound hb0 hb10
  have hm2 : (ErrorBudget.projectionMagnitude bound)^2 ≤ (1201:ℝ)^2 :=
    pow_le_pow_left₀ (by linarith) hm.2 2
  have h := attentionScore_accuracy _ _ _ _ _ _ _ _ (ErrorBudget.projectionMagnitude bound)
    (12*bound^2) (ErrorBudget.projection bound lower) (by nlinarith [sq_nonneg (ErrorBudget.projectionMagnitude bound-1)])
    (hm2.trans (by norm_num)) ((abs_nonneg _).trans (hqe 0))
    (hqb (Real.coordinate head 0)) (hqb (Real.coordinate head 1))
    (hkb (Real.coordinate head 0)) (hkb (Real.coordinate head 1))
    (hqr (Real.coordinate head 0)) (hqr (Real.coordinate head 1))
    (hqe (Real.coordinate head 0)) (hqe (Real.coordinate head 1))
    (hke (Real.coordinate head 0)) (hke (Real.coordinate head 1))
  simpa only [attentionScores, inputQuery, projectedContext_rows, Real.score,
    Fin.sum_univ_two, Real.normalizedEmbedding, parameters, ErrorBudget.score] using h

theorem visible_token_prefix (position : Fin 4) :
    Softmax.visible (UInt64.ofNat (position.val+1)) = Real.visible position := by
  funext i
  fin_cases position <;> fin_cases i <;> decide

theorem inputAttention_accuracy (w : Array UInt64) (bound lower : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl : 0 < lower) (hf : EmbeddingFloors w tokens lower)
    (position j : Fin 4) :
    |decodeRow (inputAttention w tokens position) j-Real.attended (parameters w) tokens position j| ≤
      ErrorBudget.attention bound lower := by
  let q := inputQuery w tokens position
  let k := projectedContext w tokens Layout.key
  let v := projectedContext w tokens Layout.value
  let s := attentionScores q k (Real.headOf j)
  have hm := projectionMagnitude_range bound hb0 hb10
  have hq := projected_input_bounded w bound hb0 hb10 hw tokens Layout.query (by decide) position
  have hk (i a : Fin 4) : Affine.Bounded (rowWords (contextRows k i) a)
      (ErrorBudget.projectionMagnitude bound) := by
    rw [projectedContext_rows]
    exact projected_input_bounded w bound hb0 hb10 hw tokens Layout.key (by decide) i a
  have hv (i : Fin 4) : Affine.Bounded (rowWords (contextRows v i) j)
      (ErrorBudget.projectionMagnitude bound) := by
    rw [projectedContext_rows]
    exact projected_input_bounded w bound hb0 hb10 hw tokens Layout.value (by decide) i j
  have hs := runtime_scores_valid (UInt64.ofNat (position.val+1))
    (by fin_cases position <;> decide) (by fin_cases position <;> decide) q k (Real.headOf j)
    (fun a => (hq a).weaken (hm.2.trans (by norm_num)))
    (fun i a => (hk i a).weaken (hm.2.trans (by norm_num)))
  have hse (i : Fin 4) : |value (Softmax.scores (s 0) (s 1) (s 2) (s 3) i)-
      Real.score (parameters w) tokens position (Real.headOf j) i| ≤ ErrorBudget.score bound lower := by
    have he := inputScore_accuracy w bound lower hb0 hb10 hw tokens hl hf position (Real.headOf j)
    fin_cases i <;> exact he _
  have hve (i : Fin 4) : |value (rowWords (contextRows v i) j)-
      Real.matrixApply (parameters w).value (Real.normalizedEmbedding (parameters w) tokens i) j| ≤
        ErrorBudget.projection bound lower := by
    rw [projectedContext_rows]
    exact projected_input_accuracy w bound lower hb0 hb10 hw tokens hl hf Layout.value (by decide) i j
  have he := weightedValue_accuracy _ (s 0) (s 1) (s 2) (s 3) hs
    (fun i => rowWords (contextRows v i) j) (Real.score (parameters w) tokens position (Real.headOf j))
    (fun i => Real.matrixApply (parameters w).value (Real.normalizedEmbedding (parameters w) tokens i) j)
    (ErrorBudget.projectionMagnitude bound) (ErrorBudget.score bound lower) (ErrorBudget.projection bound lower)
    hm.1 (hm.2.trans (by norm_num)) ((abs_nonneg _).trans (hse 0)) hv hse hve
  simpa only [decodeRow, inputAttention, attentionRow_words, attentionProbabilities, s,
    attentionScores, q, k, v, Real.attended, Real.probability, visible_token_prefix,
    ErrorBudget.attention] using he

#print axioms inputScore_accuracy
#print axioms inputAttention_accuracy
end Project.TinyGpt2
