import Project.ProofKit.F64AdmissibilityTiny

namespace Project.ProofKit.F64NormalizeTiny
open Project.ProofKit.F64Order
open Project.ProofKit.F64Normalize (exponentBits)
open Project.ProofKit.F64Admissibility (normalizable)

theorem momentumNormalizable_of_top (bits top : UInt64) (ht : 1021 ≤ top) :
    momentumNormalizable bits top = true := by
  by_cases he : (0 : UInt64) < exponentBits bits
  · by_cases hg : top < exponentBits bits + 1021
    · apply Bool.or_eq_true_iff.mpr
      left
      simp only [normalizable, he, hg, decide_true, Bool.and_self, Bool.or_true]
    · apply Bool.or_eq_true_iff.mpr
      right
      apply decide_eq_true
      apply UInt64.le_iff_toNat_le.mpr
      change ¬ top.toNat < (exponentBits bits + 1021).toNat at hg
      omega
  · have hz : exponentBits bits = 0 := by
      apply UInt64.toNat_inj.mp
      change ¬ (0 : UInt64).toNat < (exponentBits bits).toNat at he
      simp only [UInt64.toNat_zero] at he ⊢
      omega
    apply Bool.or_eq_true_iff.mpr
    right
    simp only [tiny, hz, UInt64.zero_add, decide_eq_true_eq]
    exact ht

#print axioms momentumNormalizable_of_top
end Project.ProofKit.F64NormalizeTiny

namespace Project.ProofKit.F64AdmissibilityTiny
open Project.ProofKit.F64Order
open Project.ProofKit.F64Admissibility (topExponent normalizable)

theorem checked_of_margin_and_top (rho mx my energy : UInt64)
    (hr : positiveBits rho = true) (hx : finiteBits mx = true)
    (hy : finiteBits my = true) (he : positiveBits energy = true)
    (ht : 1021 ≤ topExponent rho mx my energy)
    (nr : normalizable rho (topExponent rho mx my energy) = true)
    (ne : normalizable energy (topExponent rho mx my energy) = true)
    (hm : 13 * CodeLib.IEEE64.arithmeticEpsilon < exactResidual rho mx my energy) :
    checked rho mx my energy = true :=
  checked_of_margin rho mx my energy hr hx hy he nr
    (F64NormalizeTiny.momentumNormalizable_of_top mx _ ht)
    (F64NormalizeTiny.momentumNormalizable_of_top my _ ht) ne hm

#print axioms checked_of_margin_and_top
end Project.ProofKit.F64AdmissibilityTiny
