import Project.TinyGpt2.Rows
import Project.TinyGpt2.ClippedParameters
import Project.LayerNorm.Wide

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem norm_error_wide (w : Array UInt64) (offset : Nat) (x : Row) (bound gain : ℝ)
    (hb1 : 1 ≤ bound) (hRange : 504*bound^2+1 < (2:ℝ)^1022)
    (hg0 : 0 ≤ gain) (hgMax : gain ≤ 10)
    (hx : ∀ i, Affine.Bounded (rowWords x i) bound)
    (hg : ∀ i, Affine.Bounded (rowWords (loadRow w offset) i) gain)
    (hb : ∀ i, Affine.Bounded (rowWords (loadRow w (offset+4)) i) gain) (i : Fin 4) :
    Approximation (rowWords (norm w offset x) i)
      (Real.norm (decodeNorm w offset) (decodeRow x) i)
      (3*gain+(254*gain+2)*arithmeticEpsilon)
      ((16000*gain*bound+254*gain+2)*arithmeticEpsilon) := by
  have h := LayerNorm.component_error_wide (rowWords x) (rowWords (loadRow w offset) i)
    (rowWords (loadRow w (offset+4)) i) bound gain hb1 hRange hg0 hgMax
    (fun j => (hx j).1) (fun j => (hx j).2) (hg i).1 (hb i).1 (hg i).2 (hb i).2 i
  fin_cases i <;> exact ⟨h.1, h.2.1, h.2.2⟩

theorem clipped_loaded_bounded (bound : UInt64) (w : Array UInt64)
    (h : F64Clip.accepted Layout.size bound w = true)
    (offset : Nat) (ho : offset+4 ≤ Layout.size) (i : Fin 4) :
    Affine.Bounded (rowWords (loadRow (F64Clip.prepare Layout.size bound w) offset) i) (value bound) := by
  rw [loadRow_words]
  have hw := ((F64Clip.accepted_iff Layout.size bound w).mp h).1
  have hc := F64Clip.prepare_element Layout.size bound w h (offset+i.val) (by omega)
  exact ⟨hc.1, hc.2.1⟩

theorem clipped_norm_error (bound : UInt64) (w : Array UInt64)
    (h : F64Clip.accepted Layout.size bound w = true)
    (offset : Nat) (ho : offset+8 ≤ Layout.size) (x : Row) (inputBound : ℝ)
    (hx1 : 1 ≤ inputBound) (hRange : 504*inputBound^2+1 < (2:ℝ)^1022)
    (hx : ∀ i, Affine.Bounded (rowWords x i) inputBound) (i : Fin 4) :
    let weights := F64Clip.prepare Layout.size bound w
    Approximation (rowWords (norm weights offset x) i)
      (Real.norm (decodeNorm weights offset) (decodeRow x) i)
      (3*value bound+(254*value bound+2)*arithmeticEpsilon)
      ((16000*value bound*inputBound+254*value bound+2)*arithmeticEpsilon) := by
  have hb := ((F64Clip.accepted_iff Layout.size bound w).mp h).2.1
  exact norm_error_wide _ offset x inputBound (value bound) hx1 hRange hb.2.1 hb.2.2 hx
    (clipped_loaded_bounded bound w h offset (by omega))
    (clipped_loaded_bounded bound w h (offset+4) (by omega)) i

#print axioms norm_error_wide
#print axioms clipped_norm_error
end Project.TinyGpt2
