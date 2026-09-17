import Project.TinyGpt2.RuntimeResidual
import Project.TinyGpt2.RuntimeProjection
import Project.TinyGpt2.RuntimeErrorRules
import Project.TinyGpt2.ErrorBudget

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

def tokenWords (tokens : Real.Tokens) (i : Fin 4) : UInt64 := UInt64.ofNat (tokens i).val

theorem tokenWords_toNat (tokens : Real.Tokens) (i : Fin 4) :
    (tokenWords tokens i).toNat = (tokens i).val :=
  UInt64.toNat_ofNat_of_lt' (by change (tokens i).val < 18446744073709551616; omega)

theorem tokenWords_valid (tokens : Real.Tokens) (i : Fin 4) : (tokenWords tokens i).toNat < 256 := by
  rw [tokenWords_toNat]
  exact (tokens i).isLt

def inputRow (w : Array UInt64) (tokens : Real.Tokens) (i : Fin 4) : Row :=
  contextRows (embeddedContext w (tokenWords tokens)) i

def EmbeddingFloors (w : Array UInt64) (tokens : Real.Tokens) (lower : ℝ) : Prop :=
  ∀ i, lower ≤ LayerNorm.Real.deviation (1/100000) (decodeRow (inputRow w tokens i)) ∧
    lower ≤ LayerNorm.Real.deviation (1/100000) (Real.embedding (parameters w) tokens i)

theorem embedding_floors (w : Array UInt64) (tokens : Real.Tokens) :
    EmbeddingFloors w tokens (Real.sqrt (1/100000)) :=
  fun _ => ⟨LayerNorm.Real.deviation_lower _ _, LayerNorm.Real.deviation_lower _ _⟩

theorem inputRow_bounded (w : Array UInt64) (bound : ℝ) (hb10 : bound ≤ 10)
    (hw : WeightsBounded w bound) (tokens : Real.Tokens) (i j : Fin 4) :
    Affine.Bounded (rowWords (inputRow w tokens i) j) 21 := by
  rw [inputRow, embeddedContext_rows]
  exact runtime_embedding_bounded w bound hb10 hw _ _ (tokenWords_valid tokens i)
    (by fin_cases i <;> decide) j

theorem inputRow_accuracy (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (i j : Fin 4) :
    |decodeRow (inputRow w tokens i) j-Real.embedding (parameters w) tokens i j| ≤
      ErrorBudget.embedding bound := by
  let a := loadRow w (Layout.token+4*(tokens i).val)
  let b := loadRow w (Layout.position+4*i.val)
  have ha : Affine.Bounded (rowWords a j) bound := loaded_weights_bounded w bound hw _
    (by simp only [Layout.token, Layout.size]; omega) j
  have hb : Affine.Bounded (rowWords b j) bound := loaded_weights_bounded w bound hw _
    (by simp only [Layout.position, Layout.size]; omega) j
  have hs : |value (rowWords a j)+value (rowWords b j)| ≤ 2*bound+1 :=
    (abs_add_le _ _).trans ((add_le_add ha.2 hb.2).trans (by linarith))
  have he := add_error_wide _ _ (2*bound+1) (by linarith) (by norm_num; linarith) ha.1 hb.1 hs
  have hi : i.val < 18446744073709551616 := by omega
  simpa only [inputRow, embeddedContext_rows, embedding, tokenWords_toNat,
    UInt64.toNat_ofNat_of_lt' hi, decodeRow, addRows_words, Real.embedding, parameters,
    ErrorBudget.embedding, a, b] using he.accuracy

theorem normalized_input_accuracy (w : Array UInt64) (bound lower : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl : 0 < lower) (hf : EmbeddingFloors w tokens lower) (i j : Fin 4) :
    |decodeRow (norm w Layout.norm1 (inputRow w tokens i)) j-
      Real.normalizedEmbedding (parameters w) tokens i j| ≤
      ErrorBudget.normalizedEmbedding bound lower := by
  have he := inputRow_accuracy w bound hb0 hb10 hw tokens i
  have h := norm_error_wide_perturbed w Layout.norm1 (inputRow w tokens i)
    (Real.embedding (parameters w) tokens i) 21 bound (ErrorBudget.embedding bound) lower
    (by norm_num) (by norm_num) hb0 hb10 ((abs_nonneg _).trans (he 0)) hl
    (inputRow_bounded w bound hb10 hw tokens i)
    (loaded_weights_bounded w bound hw Layout.norm1 (by decide))
    (loaded_weights_bounded w bound hw (Layout.norm1+4) (by decide))
    (hf i).1 (hf i).2 he j
  exact h.accuracy

theorem projected_input_accuracy (w : Array UInt64) (bound lower : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (hl : 0 < lower) (hf : EmbeddingFloors w tokens lower)
    (offset : Nat) (ho : offset+16 ≤ Layout.size) (i j : Fin 4) :
    |decodeRow (project4 w offset (norm w Layout.norm1 (inputRow w tokens i))) j-
      Real.matrixApply (decodeMatrix w offset 4 4) (Real.normalizedEmbedding (parameters w) tokens i) j| ≤
      ErrorBudget.projection bound lower := by
  have he := normalized_input_accuracy w bound lower hb0 hb10 hw tokens hl hf i
  have hn := runtime_norm_bounded w bound hb0 hb10 hw Layout.norm1 (by decide) _
    (fun j => (inputRow_bounded w bound hb10 hw tokens i j).weaken (by norm_num))
  have h := dotColumn4_error_perturbed w offset 4 j _ _ 31 bound
    (ErrorBudget.normalizedEmbedding bound lower) (by norm_num) hb0 ((abs_nonneg _).trans (he 0))
    (by norm_num; linarith) hn (matrix_weights_bounded w bound hw offset 4 4 ho) he
  simpa only [decodeRow, project4_words, ErrorBudget.projection, ErrorBudget.column4] using h.accuracy

theorem projected_input_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Real.Tokens) (offset : Nat) (ho : offset+16 ≤ Layout.size) (i j : Fin 4) :
    Affine.Bounded (rowWords (project4 w offset (norm w Layout.norm1 (inputRow w tokens i))) j)
      (ErrorBudget.projectionMagnitude bound) :=
  runtime_normalized_projection_bounded w bound hb0 hb10 hw Layout.norm1 offset (by decide) ho _
    (fun k => (inputRow_bounded w bound hb10 hw tokens i k).weaken (by norm_num)) j

#print axioms inputRow_accuracy
#print axioms projected_input_accuracy
end Project.TinyGpt2
