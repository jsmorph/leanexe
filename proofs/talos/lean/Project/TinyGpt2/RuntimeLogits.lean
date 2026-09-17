import Project.TinyGpt2.RuntimeResidual
import Project.TinyGpt2.RuntimeFeedForward
import Project.TinyGpt2.OutputModel

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem runtime_hidden_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Fin 4 → UInt64) (ht : ∀ i, (tokens i).toNat < 256) (position j : Fin 4) :
    Affine.Bounded (rowWords
      (hidden w (tokens 0) (tokens 1) (tokens 2) (tokens 3) (UInt64.ofNat position.val)) j) 31 := by
  have hr (i k : Fin 4) :
      Affine.Bounded (rowWords (contextRows (embeddedContext w tokens) i) k) 21 := by
    rw [embeddedContext_rows]
    exact runtime_embedding_bounded w bound hb10 hw _ _ (ht i) (by fin_cases i <;> decide) k
  rw [hidden_runtime_stages]
  exact runtime_final_bounded w bound hb0 hb10 hw _
    (runtime_residual_bounded w bound hb0 hb10 hw _
      (by fin_cases position <;> decide) (by fin_cases position <;> decide)
      _ _ (hr position) hr) j

theorem runtime_logit_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (x : Row)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 31) (j : Fin 256) :
    Affine.Bounded (logit w x (UInt64.ofNat j.val)) 1260 := by
  have hd := dotColumn4_error_wide w Layout.head 256 j x 31 bound
    (by norm_num) hb0 (by norm_num; linarith) hx
    (fun i => matrix_weights_bounded w bound hw Layout.head 4 256 (by decide) i j)
  have hm : |value (dotColumn4 w Layout.head 256 j.val x)| ≤ 1249 := hd.magnitude.trans (by linarith)
  have hb := hw (Layout.headBias+j.val) (by simp only [Layout.headBias, Layout.size]; omega)
  have he := add_error_wide _ _ 1259 (by norm_num) (by norm_num) hd.finite hb.1
    ((abs_add_le _ _).trans ((add_le_add hm (hb.2.trans hb10)).trans (by norm_num)))
  simp only [logit, UInt64.toNat_ofNat_of_lt' (show j.val < 18446744073709551616 by omega)]
  exact ⟨he.finite, he.magnitude.trans (by norm_num)⟩

theorem runtime_infer_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (tokens : Fin 4 → UInt64) (ht : ∀ i, (tokens i).toNat < 256) (j : Fin 256) :
    Affine.Bounded (infer w (tokens 0) (tokens 1) (tokens 2) (tokens 3))[j.val]! 1260 := by
  have hh := runtime_hidden_bounded w bound hb0 hb10 hw tokens ht 3
  have hl := runtime_logit_bounded w bound hb0 hb10 hw _ hh j
  rw [infer_eq_logitPrefix]
  simpa [logitPrefix, getElem!_pos, j.isLt] using hl

theorem clipped_infer_bounded (bound : UInt64) (w : Array UInt64)
    (h : F64Clip.accepted Layout.size bound w = true)
    (tokens : Fin 4 → UInt64) (ht : ∀ i, (tokens i).toNat < 256) (j : Fin 256) :
    Affine.Bounded
      (infer (F64Clip.prepare Layout.size bound w) (tokens 0) (tokens 1) (tokens 2) (tokens 3))[j.val]!
      1260 := by
  have hb := ((F64Clip.accepted_iff Layout.size bound w).mp h).2.1
  exact runtime_infer_bounded _ (value bound) hb.2.1 hb.2.2
    (prepared_weights_bounded bound w h) tokens ht j

#print axioms runtime_infer_bounded
#print axioms clipped_infer_bounded
end Project.TinyGpt2
