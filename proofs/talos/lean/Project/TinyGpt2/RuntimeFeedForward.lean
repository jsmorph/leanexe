import Project.TinyGpt2.RuntimeParameters
import Project.TinyGpt2.RuntimeStages

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem runtime_expanded_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (x : Row)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 200000) (j : Fin 8) :
    Affine.Bounded (wideWords (expandRow w (norm w Layout.norm2 x)) j) 1260 := by
  have hn := runtime_norm_bounded w bound hb0 hb10 hw Layout.norm2 (by decide) x hx
  have hd := dotColumn4_error_wide w 1108 8 j (norm w Layout.norm2 x) 31 bound
    (by norm_num) hb0 (by norm_num; linarith) hn
    (fun i => matrix_weights_bounded w bound hw 1108 4 8 (by decide) i j)
  have hm : |value (dotColumn4 w 1108 8 j.val (norm w Layout.norm2 x))| ≤ 1249 :=
    hd.magnitude.trans (by linarith)
  have hb := hw (1140+j.val) (by simp only [Layout.size]; omega)
  have he := add_error_wide _ _ 1259 (by norm_num) (by norm_num) hd.finite hb.1
    ((abs_add_le _ _).trans ((add_le_add hm (hb.2.trans hb10)).trans (by norm_num)))
  rw [expandRow_words]
  exact ⟨he.finite, he.magnitude.trans (by norm_num)⟩

theorem runtime_activated_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (x : Row)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 200000) (j : Fin 8) :
    Affine.Bounded (wideWords (activatedRow w x) j) 1261 := by
  have hx := runtime_expanded_bounded w bound hb0 hb10 hw x hx j
  have he := GeluWide.evaluateAll_error _ hx.1
  have hm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ he.2
    ((Gelu.Real.gelu_magnitude _).trans hx.2)
  simp only [activatedRow, activateWide_words]
  exact ⟨he.1, hm.trans (by norm_num [arithmeticEpsilon])⟩

theorem runtime_contracted_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (x : WideRow)
    (hx : ∀ i, Affine.Bounded (wideWords x i) 1261) (j : Fin 4) :
    Affine.Bounded (rowWords (contractRow w x) j) 100910 := by
  have hd := dotColumn8_error_wide w 1148 4 j x 1261 bound
    (by norm_num) hb0 (by norm_num; linarith) hx
    (fun i => matrix_weights_bounded w bound hw 1148 8 4 (by decide) i j)
  have hm : |value (dotColumn8 w 1148 4 j.val x)| ≤ 100899 := hd.magnitude.trans (by linarith)
  have hb := hw (1180+j.val) (by simp only [Layout.size]; omega)
  have he := add_error_wide _ _ 100909 (by norm_num) (by norm_num) hd.finite hb.1
    ((abs_add_le _ _).trans ((add_le_add hm (hb.2.trans hb10)).trans (by norm_num)))
  rw [contractRow_words]
  exact ⟨he.finite, he.magnitude.trans (by norm_num)⟩

theorem runtime_final_bounded (w : Array UInt64) (bound : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded w bound) (x : Row)
    (hx : ∀ i, Affine.Bounded (rowWords x i) 60000) (j : Fin 4) :
    Affine.Bounded
      (rowWords (norm w Layout.normFinal (addRows x (contractRow w (activatedRow w x)))) j) 31 := by
  have ha := runtime_activated_bounded w bound hb0 hb10 hw x
    (fun i => (hx i).weaken (by norm_num))
  have hc := runtime_contracted_bounded w bound hb0 hb10 hw _ ha
  have hs := addRows_bounded x _ 60000 100910 (by norm_num) (by norm_num) hx hc
  exact runtime_norm_bounded w bound hb0 hb10 hw Layout.normFinal (by decide) _
    (fun i => (hs i).weaken (by norm_num)) j

#print axioms runtime_activated_bounded
#print axioms runtime_final_bounded
end Project.TinyGpt2
