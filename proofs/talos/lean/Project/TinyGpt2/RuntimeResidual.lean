import Project.TinyGpt2.RuntimeParameters
import Project.TinyGpt2.RuntimeAttention
import Project.TinyGpt2.RuntimeStages

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem runtime_embedding_bounded (w : Array UInt64) (bound : ℝ)
    (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (token position : UInt64)
    (ht : token.toNat < 256) (hp : position.toNat < 4) (j : Fin 4) :
    Affine.Bounded (rowWords (embedding w token position) j) 21 := by
  have hrow (offset : Nat) (ho : offset+4 ≤ Layout.size) (i : Fin 4) :
      Affine.Bounded (rowWords (loadRow w offset) i) 10 := by
    have h := loaded_weights_bounded w bound hw offset ho i
    exact ⟨h.1, h.2.trans hb10⟩
  have htRow := hrow (Layout.token+4*token.toNat) (by
    simp only [Layout.token, Layout.size]; omega)
  have hpRow := hrow (Layout.position+4*position.toNat) (by
    simp only [Layout.position, Layout.size]; omega)
  exact (addRows_bounded _ _ 10 10 (by norm_num) (by norm_num) htRow hpRow j).weaken (by norm_num)

theorem runtime_residual_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound)
    (n : UInt64) (hn0 : 0 < n) (hn4 : n ≤ 4) (x : Row) (rows : Context)
    (hx : ∀ j, Affine.Bounded (rowWords x j) 21)
    (hr : ∀ i j, Affine.Bounded (rowWords (contextRows rows i) j) 21) (j : Fin 4) :
    Affine.Bounded (rowWords (residualRow w n x rows) j) 60000 := by
  have hnorm (y : Row) (hy : ∀ i, Affine.Bounded (rowWords y i) 21) (i : Fin 4) :
      Affine.Bounded (rowWords (norm w Layout.norm1 y) i) 31 :=
    runtime_norm_bounded w bound hb0 hb10 hw Layout.norm1 (by decide) y
      (fun k => ⟨(hy k).1, (hy k).2.trans (by norm_num)⟩) i
  have hq := runtime_project_bounded w bound hb0 hb10 hw Layout.query (by decide)
    (norm w Layout.norm1 x) (hnorm x hx)
  have hproject (offset : Nat) (ho : offset+16 ≤ Layout.size) (i k : Fin 4) :
      Affine.Bounded (rowWords
        (contextRows (projectContext w offset (normContext w Layout.norm1 rows)) i) k) 1249 := by
    rw [projectContext_rows, normContext_rows]
    exact runtime_project_bounded w bound hb0 hb10 hw offset ho _ (hnorm _ (hr i)) k
  let attended := attentionRow n (project4 w Layout.query (norm w Layout.norm1 x))
    (projectContext w Layout.key (normContext w Layout.norm1 rows))
    (projectContext w Layout.value (normContext w Layout.norm1 rows))
  have ha : ∀ i, Affine.Bounded (rowWords attended i) 1250 :=
    runtime_attention_bounded n hn0 hn4 _ _ _ hq
      (hproject Layout.key (by decide)) (hproject Layout.value (by decide))
  have hproj (i : Fin 4) :
      Affine.Bounded (rowWords (project4 w Layout.attention attended) i) 50009 := by
    rw [project4_words]
    have h := dotColumn4_error_wide w Layout.attention 4 i attended 1250 bound
      (by norm_num) hb0 (by norm_num; linarith) ha
      (fun k => matrix_weights_bounded w bound hw Layout.attention 4 4 (by decide) k i)
    exact ⟨h.finite, h.magnitude.trans (by linarith)⟩
  have hbias (i : Fin 4) :
      Affine.Bounded (rowWords (loadRow w Layout.attentionBias) i) 10 := by
    have h := loaded_weights_bounded w bound hw Layout.attentionBias (by decide) i
    exact ⟨h.1, h.2.trans hb10⟩
  have hatt := addRows_bounded _ _ 50009 10 (by norm_num) (by norm_num) hproj hbias
  have h := addRows_bounded x _ 21 50020 (by norm_num) (by norm_num) hx
    (fun i => (hatt i).weaken (by norm_num)) j
  exact ⟨h.1, h.2.trans (by norm_num)⟩

#print axioms runtime_embedding_bounded
#print axioms runtime_residual_bounded
end Project.TinyGpt2
