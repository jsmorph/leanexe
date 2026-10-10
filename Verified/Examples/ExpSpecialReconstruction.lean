import Verified.Examples.ExpSpecialScale
import Verified.Examples.ExpCoreBounds

namespace Verified.Examples.ExpSpecialReconstruction
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def reconstruction (adjust : UInt64 → UInt64) (x : UInt64) : UInt64 :=
  ExpReconstructionBounds.reconstruction (adjust (ExpCoreState.shiftedBits x))
    (ExpResidualBounds.residual x) (ExpCoreState.tailBits x)

def floatReconstruction (adjust : UInt64 → UInt64) (x : Float) : Float :=
  ExpReconstructionBounds.floatReconstruction
    (Float.ofBits (adjust (ExpCoreBounds.floatShifted x).toBits))
    (ExpResidualBounds.floatResidual x)
    (Float.ofBits Exp.expTable[(ExpScaleBits.index (ExpCoreBounds.floatShifted x).toBits).toNat]!)

theorem reconstruction_bits (adjust : UInt64 → UInt64) (x : Float)
    (hsf : Finite (adjust (ExpCoreState.shiftedBits x.toBits)))
    (htf : Finite (ExpCoreState.tailBits x.toBits)) :
    (floatReconstruction adjust x).toBits = reconstruction adjust x.toBits := by
  rw [floatReconstruction, ExpReconstructionBounds.reconstruction_bits,
    ExpCoreBounds.floatShifted_bits, ExpResidualBounds.residual_bits]
  change ExpReconstructionBounds.reconstruction
    (Float.ofBits (adjust (ExpCoreState.shiftedBits x.toBits))).toBits
    (ExpResidualBounds.residual x.toBits)
    (Float.ofBits (ExpCoreState.tailBits x.toBits)).toBits = reconstruction adjust x.toBits
  simp only [F64Bits.toBits_ofBits, not_nan_of_finite hsf, not_nan_of_finite htf,
    Bool.false_eq_true, ite_false]
  rfl

theorem positive_error (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768)
    (hxpos : 512 ≤ value x) :
    Finite (reconstruction ExpSpecialScale.positiveScale x) ∧
      |value (reconstruction ExpSpecialScale.positiveScale x) -
        (2 : ℝ) ^ (-1009 : Int) * Real.exp (value x)| ≤
        (7 / 5) * unitRoundoff64 *
          value (ExpSpecialScale.positiveScale (ExpCoreState.shiftedBits x)) := by
  obtain ⟨k, q, j, hkv, hk, ht, hki, hj, hkn⟩ := ExpCoreState.prefix_state x hxf hx
  have hqb := ExpSpecialScale.quotient_bounds k q j hk hkn
  have hqlo := ExpSpecialScale.positive_quotient x k q j hxf hx hxpos hkv hk
  have hs := ExpSpecialScale.positive_scale_value (ExpCoreState.shiftedBits x)
    k q j hki hk hj hqlo (hqb.2.trans (by norm_num))
  dsimp only [reconstruction]
  rw [ht]
  exact ExpTableReconstruction.table_reconstruction_scaled_error x
    (ExpSpecialScale.positiveScale (ExpCoreState.shiftedBits x)) k q (-1009) j
    hxf hx hkv hk hs.1 (by simpa only [sub_eq_add_neg] using hs.2.1)
    hs.2.2.1 hs.2.2.2

theorem negative_error (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768)
    (hxneg : value x ≤ -512) :
    Finite (reconstruction ExpSpecialScale.negativeScale x) ∧
      |value (reconstruction ExpSpecialScale.negativeScale x) -
        (2 : ℝ) ^ (1022 : Int) * Real.exp (value x)| ≤
        (7 / 5) * unitRoundoff64 *
          value (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x)) := by
  obtain ⟨k, q, j, hkv, hk, ht, hki, hj, hkn⟩ := ExpCoreState.prefix_state x hxf hx
  have hqb := ExpSpecialScale.quotient_bounds k q j hk hkn
  have hqhi := ExpSpecialScale.negative_quotient x k q j hxf hx hxneg hkv hk
  have hs := ExpSpecialScale.negative_scale_value (ExpCoreState.shiftedBits x)
    k q j hki hk hj ((by norm_num : (-2022 : Int) ≤ -1153).trans hqb.1) hqhi
  dsimp only [reconstruction]
  rw [ht]
  exact ExpTableReconstruction.table_reconstruction_scaled_error x
    (ExpSpecialScale.negativeScale (ExpCoreState.shiftedBits x)) k q 1022 j
    hxf hx hkv hk hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

theorem positive_float_error (x : Float) (hxf : Finite x.toBits)
    (hx : |value x.toBits| ≤ 768) (hxpos : 512 ≤ value x.toBits) :
    Finite (floatReconstruction ExpSpecialScale.positiveScale x).toBits ∧
      |value (floatReconstruction ExpSpecialScale.positiveScale x).toBits -
        (2 : ℝ) ^ (-1009 : Int) * Real.exp (value x.toBits)| ≤
        (7 / 5) * unitRoundoff64 *
          value (ExpSpecialScale.positiveScale (ExpCoreState.shiftedBits x.toBits)) := by
  obtain ⟨k, q, j, hkv, hk, ht, hki, hj, hkn⟩ :=
    ExpCoreState.prefix_state x.toBits hxf hx
  have hqb := ExpSpecialScale.quotient_bounds k q j hk hkn
  have hqlo := ExpSpecialScale.positive_quotient x.toBits k q j hxf hx hxpos hkv hk
  have hs := ExpSpecialScale.positive_scale_value (ExpCoreState.shiftedBits x.toBits)
    k q j hki hk hj hqlo (hqb.2.trans (by norm_num))
  have htf : Finite (ExpCoreState.tailBits x.toBits) := by
    rw [ht]
    exact (ExpTableBounds.entry_bounds j).2.1
  rw [reconstruction_bits _ x hs.1 htf]
  exact positive_error x.toBits hxf hx hxpos

#print axioms reconstruction_bits
#print axioms positive_error
#print axioms negative_error
#print axioms positive_float_error

end Verified.Examples.ExpSpecialReconstruction
