import Project.SpectralKL.ScalarMoments

namespace Project.SpectralKL.Scalar
open CodeLib.IEEE64 LeanExe.Examples.SpectralKL
open MeasureTheory intervalIntegral
open Project.ProofKit
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

/-- The scalar instance of the regularized sample moment functional. -/
noncomputable def regularizedIntegral (p q : Array UInt64) (eta : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..1, (1-r)*(exactMean p-exactMean q)^2 /
    (r*(exactSecond p+eta)+(1-r)*(exactSecond q+eta))

theorem regularizedIntegral_eq (p q : Array UInt64) (eta : ℝ)
    (hq : 0 < exactSecond q+eta) :
    regularizedIntegral p q eta = (exactMean p-exactMean q)^2/(exactSecond q+eta)*
      kernel ((exactSecond p+eta)/(exactSecond q+eta)) := by
  have hb : exactSecond q+eta ≠ 0 := by linarith
  have hf : (fun r : ℝ => (1-r)*(exactMean p-exactMean q)^2 /
      (r*(exactSecond p+eta)+(1-r)*(exactSecond q+eta))) =
      (fun r => (exactMean p-exactMean q)^2/(exactSecond q+eta)*
        ((1-r)/(1+r*((exactSecond p+eta)/(exactSecond q+eta)-1)))) := by
    funext r
    have hd : r*(exactSecond p+eta)+(1-r)*(exactSecond q+eta) =
        (exactSecond q+eta)*(1+r*((exactSecond p+eta)/(exactSecond q+eta)-1)) := by
      field_simp; ring
    rw [hd]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  unfold regularizedIntegral
  rw [hf, intervalIntegral.integral_const_mul]
  rfl

noncomputable def sampleIntegral (p q : Array UInt64) : ℝ := regularizedIntegral p q 1

def ValidRidge (eta : UInt64) : Prop :=
  0x3FF0000000000000 ≤ eta ∧ eta ≤ 0x4070000000000000

theorem valid_ridge (eta : UInt64) (h : ValidRidge eta) :
    Finite eta ∧ 1 ≤ value eta ∧ value eta ≤ 256 := by
  have hlo := UInt64.le_iff_toNat_le.mp h.1
  have hhi := UInt64.le_iff_toNat_le.mp h.2
  have hp : F64Order.positiveBits eta = true := by
    simp only [F64Order.positiveBits, Bool.and_eq_true, decide_eq_true_eq,
      UInt64.lt_iff_toNat_lt]
    constructor <;> norm_num [UInt64.toNat_ofNat] at hlo hhi ⊢ <;> omega
  have hs := F64Order.positiveBits_spec eta hp
  have ha := F64Order.absBits_of_positive eta hp
  have hb : F64Order.absBits 0x3FF0000000000000 ≤ F64Order.absBits eta := by
    rw [ha]; exact h.1
  have hc : F64Order.absBits eta ≤ F64Order.absBits 0x4070000000000000 := by
    rw [ha]; exact h.2
  have h256 : value 0x4070000000000000 = 256 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have lower := F64Order.abs_value_mono _ _ hb
  have upper := F64Order.abs_value_mono _ _ hc
  simp only [value_one,h256,abs_of_pos hs.2] at lower upper
  exact ⟨hs.1,by simpa using lower,by simpa using upper⟩

/-- Nonempty binary64 observations, at most 2^20 per group, each in [-1/2,1/2].
The word comparison includes both signed zeros and excludes NaNs and infinities. -/
def ValidSamples (s : Array UInt64) : Prop :=
  0 < s.size ∧ s.size ≤ 1048576 ∧
    ∀ x ∈ s, (x &&& 0x7FFFFFFFFFFFFFFF) ≤ 0x3FE0000000000000

theorem valid_stats_success (s : Array UInt64) (hs : ValidSamples s) :
    (scalarStats s).status = 0 := by
  have hb : samplesBounded s 0x4030000000000000 = true := by
    apply (samplesBounded_spec s _).mpr
    intro x hx
    exact UInt64.le_iff_toNat_le.mpr
      ((UInt64.le_iff_toNat_le.mp (hs.2.2 x hx)).trans (by decide))
  simp [scalarStats, Array.isEmpty, Nat.ne_of_gt hs.1, Nat.not_lt.mpr hs.2.1, hb]

theorem valid_score_error (p q : Array UInt64) (eta : UInt64)
    (hp : ValidSamples p) (hq : ValidSamples q) (he : ValidRidge eta) :
    Finite (scalarScore (scalarStats p).mean (scalarStats q).mean
      (scalarStats p).second (scalarStats q).second eta) ∧
    |value (scalarScore (scalarStats p).mean (scalarStats q).mean
      (scalarStats p).second (scalarStats q).second eta) -
      regularizedIntegral p q (value eta)| ≤ 1/1000000 := by
  have fp := fun x hx => Executable.guard_domain x (hp.2.2 x hx)
  have fq := fun x hx => Executable.guard_domain x (hq.2.2 x hx)
  have ep := stats_error p (valid_stats_success p hp) fp
  have eq := stats_error q (valid_stats_success q hq) fq
  have bp := exact_moments p hp.1 (fun x hx => (fp x hx).2)
  have bq := exact_moments q hq.1 (fun x hx => (fq x hx).2)
  have er := valid_ridge eta he
  rw [regularizedIntegral_eq p q (value eta) (by linarith [bq.2.1,er.2.1])]
  exact score_error _ _ _ _ _ _ _ _ _ ep.1 eq.1 ep.2 eq.2 bp.1 bq.1 bp.2 bq.2 er

/-- Total numerical correctness for every admitted input and ridge in [1,256].
The conclusion includes success, finiteness, and accuracy of the computed score. -/
theorem fromBoundedSamples_correct (p q : Array UInt64) (eta : UInt64)
    (hp : ValidSamples p) (hq : ValidSamples q) (he : ValidRidge eta) :
    (fromBoundedSamples p q eta).status = 0 ∧
    Finite (fromBoundedSamples p q eta).bits ∧
      |value (fromBoundedSamples p q eta).bits-regularizedIntegral p q (value eta)| ≤ 1/1000000 := by
  have bp := (samplesBounded_spec p _).mpr hp.2.2
  have bq := (samplesBounded_spec q _).mpr hq.2.2
  have hlo : ¬ eta < 0x3FF0000000000000 := by
    rw [UInt64.lt_iff_toNat_lt]; exact Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp he.1)
  have hhi : ¬ 0x4070000000000000 < eta := by
    rw [UInt64.lt_iff_toNat_lt]; exact Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp he.2)
  simp only [fromBoundedSamples, hlo, hhi, decide_false, bp, bq, Bool.not_true,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, valid_stats_success p hp,
    valid_stats_success q hq, bne_self_eq_false]
  exact ⟨True.intro,valid_score_error p q eta hp hq he⟩

/-- The executable input guards establish the hypotheses of total correctness. -/
theorem fromBoundedSamples_error (p q : Array UInt64) (eta : UInt64)
    (h : (fromBoundedSamples p q eta).status = 0) :
    Finite (fromBoundedSamples p q eta).bits ∧
      |value (fromBoundedSamples p q eta).bits-regularizedIntegral p q (value eta)| ≤ 1/1000000 := by
  have valid : ValidSamples p ∧ ValidSamples q ∧ ValidRidge eta := by
    unfold fromBoundedSamples at h
    split at h
    · exact False.elim ((by decide : (1:UInt64) ≠ 0) h)
    · rename_i hg
      have bp : samplesBounded p 0x3FE0000000000000 = true := by
        cases he : samplesBounded p 0x3FE0000000000000 <;> simp_all
      have bq : samplesBounded q 0x3FE0000000000000 = true := by
        cases he : samplesBounded q 0x3FE0000000000000 <;> simp_all
      have er : ValidRidge eta := by
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or,
          UInt64.lt_iff_toNat_lt, not_lt] at hg
        exact ⟨UInt64.le_iff_toNat_le.mpr hg.1.1.1, UInt64.le_iff_toNat_le.mpr hg.1.1.2⟩
      dsimp only at h
      split at h
      · exact False.elim ((by decide : (1:UInt64) ≠ 0) h)
      · rename_i hs
        simp only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] at hs
        have hp := stats_success_data p hs.1
        have hq := stats_success_data q hs.2
        exact ⟨⟨hp.1,hp.2.1,(samplesBounded_spec p _).mp bp⟩,
          ⟨hq.1,hq.2.1,(samplesBounded_spec q _).mp bq⟩,er⟩
  exact (fromBoundedSamples_correct p q eta valid.1 valid.2.1 valid.2.2).2

theorem fromUnitSamples_correct (p q : Array UInt64)
    (hp : ValidSamples p) (hq : ValidSamples q) :
    (fromUnitSamples p q).status = 0 ∧
    Finite (fromUnitSamples p q).bits ∧
      |value (fromUnitSamples p q).bits-sampleIntegral p q| ≤ 1/1000000 := by
  simpa only [fromUnitSamples,sampleIntegral,value_one] using
    fromBoundedSamples_correct p q 0x3FF0000000000000 hp hq (by constructor <;> decide)

theorem fromUnitSamples_error (p q : Array UInt64)
    (h : (fromUnitSamples p q).status = 0) :
    Finite (fromUnitSamples p q).bits ∧
      |value (fromUnitSamples p q).bits-sampleIntegral p q| ≤ 1/1000000 := by
  simpa only [fromUnitSamples,sampleIntegral,value_one] using
    fromBoundedSamples_error p q 0x3FF0000000000000 h

#print axioms fromBoundedSamples_correct
#print axioms fromBoundedSamples_error
#print axioms fromUnitSamples_correct
#print axioms fromUnitSamples_error
end Project.SpectralKL.Scalar
