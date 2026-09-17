import Project.TinyGpt2.RuntimeNorm

namespace Project.TinyGpt2
open CodeLib.IEEE64 Project.ProofKit F64Horner

theorem norm_error_wide_perturbed (w : Array UInt64) (offset : Nat) (x : Row)
    (target : Real.Row) (bound gain error lower : ℝ)
    (hb1 : 1 ≤ bound) (hRange : 504*bound^2+1 < (2:ℝ)^1022)
    (hg0 : 0 ≤ gain) (hgMax : gain ≤ 10) (he : 0 ≤ error) (hl : 0 < lower)
    (hx : ∀ i, Affine.Bounded (rowWords x i) bound)
    (hg : ∀ i, Affine.Bounded (rowWords (loadRow w offset) i) gain)
    (hb : ∀ i, Affine.Bounded (rowWords (loadRow w (offset+4)) i) gain)
    (hdx : lower ≤ LayerNorm.Real.deviation (1/100000) (decodeRow x))
    (hdt : lower ≤ LayerNorm.Real.deviation (1/100000) target)
    (herror : ∀ i, |decodeRow x i-target i| ≤ error) (i : Fin 4) :
    Approximation (rowWords (norm w offset x) i)
      (Real.norm (decodeNorm w offset) target i)
      (3*gain+(254*gain+2)*arithmeticEpsilon)
      ((16000*gain*bound+254*gain+2)*arithmeticEpsilon+gain*(2*error/lower)) := by
  have hn := norm_error_wide w offset x bound gain hb1 hRange hg0 hgMax hx hg hb
  have hp := LayerNorm.Real.implementation_perturbation (1/100000) error lower gain 0 0
    ((16000*gain*bound+254*gain+2)*arithmeticEpsilon)
    (by norm_num) he hl target (decodeRow x)
    (decodeNorm w offset).scale (decodeNorm w offset).scale
    (decodeNorm w offset).bias (decodeNorm w offset).bias
    (decodeRow (norm w offset x)) hdt hdx
    (fun j => by simpa only [abs_sub_comm] using herror j)
    (fun j => (hg j).2) (by simp) (by simp) (fun j => (hn j).accuracy) i
  exact ⟨(hn i).finite, (hn i).magnitude,
    by simpa only [mul_zero, add_zero, Real.norm, decodeRow] using hp⟩

#print axioms norm_error_wide_perturbed
end Project.TinyGpt2
