import Project.TinyGpt2.Decoding
import Project.TinyGpt2.WeightBounds
import Project.F64Clip.Array

namespace Project.TinyGpt2
open CodeLib.IEEE64

theorem parameters_bounded (w : Array UInt64) (bound : ℝ)
    (hw : ∀ i, i < Layout.size → |value w[i]!| ≤ bound) :
    Real.ParametersBounded (parameters w) bound := by
  have hrow (offset : Nat) (ho : offset+4 ≤ Layout.size) (j : Fin 4) :
      |decodeRow (loadRow w offset) j| ≤ bound := by
    simp only [decodeRow, loadRow_words]
    exact hw _ (by omega)
  have hnorm (offset : Nat) (ho : offset+8 ≤ Layout.size) :
      Real.NormBounded (decodeNorm w offset) bound :=
    ⟨hrow offset (by omega), hrow (offset+4) (by omega)⟩
  refine {
    token := ?_, position := ?_, query := ?_, key := ?_, value := ?_,
    attention := ?_, attentionBias := ?_, expand := ?_, expandBias := ?_,
    contract := ?_, contractBias := ?_, head := ?_, headBias := ?_,
    norm1 := hnorm Layout.norm1 (by decide),
    norm2 := hnorm Layout.norm2 (by decide),
    normFinal := hnorm Layout.normFinal (by decide) }
  all_goals
    intros
    simp only [parameters, decodeRow, loadRow_words, decodeMatrix, matrixWords]
    apply hw
    simp only [Layout.size, Layout.token, Layout.position, Layout.query, Layout.key,
      Layout.value, Layout.attention, Layout.attentionBias, Layout.expand, Layout.expandBias,
      Layout.contract, Layout.contractBias, Layout.head, Layout.headBias]
    omega

theorem clipped_parameters_bounded (bound : UInt64) (w : Array UInt64)
    (h : F64Clip.accepted Layout.size bound w = true) :
    Real.ParametersBounded (parameters (F64Clip.prepare Layout.size bound w)) (value bound) := by
  apply parameters_bounded
  intro i hi
  have hw := ((F64Clip.accepted_iff Layout.size bound w).mp h).1
  exact (F64Clip.prepare_element Layout.size bound w h i (by omega)).2.1

theorem clipped_real_logits_magnitude (bound : UInt64) (w : Array UInt64)
    (h : F64Clip.accepted Layout.size bound w = true) (tokens : Real.Tokens)
    (i : Fin 4) (j : Fin 256) :
    |Real.logits (parameters (F64Clip.prepare Layout.size bound w)) tokens i j| ≤
      12*(value bound)^2+value bound := by
  have hb := ((F64Clip.accepted_iff Layout.size bound w).mp h).2.1.2.1
  exact Real.logits_magnitude _ tokens (value bound) hb (clipped_parameters_bounded bound w h) i j

#print axioms clipped_parameters_bounded
#print axioms clipped_real_logits_magnitude
end Project.TinyGpt2
