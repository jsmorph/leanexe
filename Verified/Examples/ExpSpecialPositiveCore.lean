import Verified.Examples.ExpSpecialReconstruction
import Verified.Examples.ExpBranches

namespace Verified.Examples.ExpSpecialPositiveCore
open CodeLib.IEEE64
open LeanExe.ProofKit

private theorem positive_special_case (tmp : Float) (sbits ki : UInt64)
    (hg : (ki &&& 0x80000000 == 0) = true) :
    Exp.specialCase tmp sbits ki =
      Float.ofBits 0x7F00000000000000 *
        (Float.ofBits (sbits - ((1009 : UInt64) <<< (52 : UInt64))) +
          Float.ofBits (sbits - ((1009 : UInt64) <<< (52 : UInt64))) * tmp) := by
  unfold Exp.specialCase
  exact ite_eq_left hg

#print axioms positive_special_case

theorem core_positive_eq (x : Float)
    (hg : ((ExpCoreBounds.floatShifted x).toBits &&& 0x80000000 == 0) = true) :
    Exp.expCore Exp.expTable x true =
      Float.ofBits 0x7F00000000000000 *
        ExpSpecialReconstruction.floatReconstruction ExpSpecialScale.positiveScale x := by
  dsimp only [ExpCoreBounds.floatShifted] at hg
  dsimp only [Exp.expCore]
  simp only [ite_true]
  rw [positive_special_case _ _ _ hg]
  simp only [ExpSpecialReconstruction.floatReconstruction,
    ExpReconstructionBounds.floatReconstruction, ExpSpecialScale.positiveScale,
    ExpCoreBounds.floatShifted, ExpResidualBounds.floatResidual, ExpReductionSelection.floatInteger,
    ExpEvaluationBounds.floatEvaluation, ExpScaleBits.scaleBits, ExpScaleBits.index]

#print axioms core_positive_eq

theorem positive_core_eq (x : Float) (hxf : Finite x.toBits)
    (hx : |value x.toBits| ≤ 768) (hxpos : 512 ≤ value x.toBits) :
    Exp.expCore Exp.expTable x true =
      Float.ofBits 0x7F00000000000000 *
        ExpSpecialReconstruction.floatReconstruction ExpSpecialScale.positiveScale x := by
  obtain ⟨k, q, j, hkv, hk, _, hki, _, hkn⟩ :=
    ExpCoreState.prefix_state x.toBits hxf hx
  have hqlo := ExpSpecialScale.positive_quotient x.toBits k q j hxf hx hxpos hkv hk
  have hq0 : 0 ≤ q := le_trans (by norm_num : (0 : Int) ≤ 9) hqlo
  have hk0 : 0 ≤ k := by
    rw [hk]
    exact add_nonneg (mul_nonneg (by norm_num) hq0) (Int.natCast_nonneg j.val)
  have hknonneg : ¬ k < 0 := not_lt_of_ge hk0
  have hguard : ExpCoreState.shiftedBits x.toBits &&& 0x80000000 = 0 := by
    simpa only [ite_eq_right hknonneg] using
      ExpSpecialScale.sign_guard (ExpCoreState.shiftedBits x.toBits) k hki
        (hkn.trans (by norm_num))
  apply core_positive_eq
  rw [ExpCoreBounds.floatShifted_bits, hguard]
  rfl

#print axioms positive_core_eq

theorem exp_positive_eq (x : Float) (hxf : Finite x.toBits)
    (hx : |value x.toBits| ≤ 768) (hxpos : 512 ≤ value x.toBits) :
    Exp.exp x = Float.ofBits 0x7F00000000000000 *
      ExpSpecialReconstruction.floatReconstruction ExpSpecialScale.positiveScale x := by
  have hxlo : 512 ≤ |value x.toBits| := hxpos.trans (le_abs_self _)
  rw [Exp.exp, ExpBranches.special_selected _ x
    (ExpBranches.special_exponent x.toBits hxlo (hx.trans_lt (by norm_num)))]
  exact positive_core_eq x hxf hx hxpos

#print axioms exp_positive_eq

end Verified.Examples.ExpSpecialPositiveCore
