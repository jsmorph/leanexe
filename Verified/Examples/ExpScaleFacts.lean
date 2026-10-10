import Verified.Examples.ExpTableBounds
import Verified.Examples.ExpReductionSelection

namespace Verified.Examples.ExpScaleFacts
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem checked_head_fields : ∀ j : Fin 128,
    Wasm.IEEE64.sign (ExpTableBounds.headBits j.val) = false ∧
    Wasm.IEEE64.exponent (ExpTableBounds.headBits j.val) = 1023 ∧
    Exp.expTable[2 * j.val + 1]!.toNat + j.val * 2 ^ 45 =
      (ExpTableBounds.headBits j.val).toNat := by decide +kernel

theorem integer_small (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 512) :
    ∃ k : Int, Finite (ExpReductionSelection.integer x) ∧
      Wasm.IEEE64.scaledValue (ExpReductionSelection.integer x) = k * 2 ^ 1074 ∧
      k.natAbs ≤ 98305 := by
  obtain ⟨k, hkf, hkv, _, hke⟩ := ExpReductionSelection.integer_selection x hxf (hx.trans (by norm_num))
  have hm : |value 0x40671547652B82FE * value x| ≤ 98304 := by
    rw [abs_mul, abs_of_pos ExpReductionBounds.inverse_bounds.1]
    calc
      _ ≤ 192 * 512 := mul_le_mul ExpReductionBounds.inverse_upper_bound hx (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hkm := F64ArithmeticBounds.magnitude_of_error _ _ _ _ hke hm
  have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hkr : (k.natAbs : ℝ) ≤ 98305 := by
    rw [← habs]
    exact hkm.trans (by norm_num)
  have hkn : k.natAbs ≤ 98305 := by exact_mod_cast hkr
  exact ⟨k, hkf, hkv, hkn⟩

#print axioms checked_head_fields
#print axioms integer_small

end Verified.Examples.ExpScaleFacts
