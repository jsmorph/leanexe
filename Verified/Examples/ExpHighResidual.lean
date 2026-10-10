import Verified.Examples.ExpHighSubtraction
import Verified.Examples.ExpHighPartBounds
import Verified.Examples.ExpReductionSelection

namespace Verified.Examples.ExpHighResidual
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def highProduct (x : UInt64) : UInt64 :=
  Wasm.IEEE64.mul (ExpReductionSelection.integer x) 0xBF762E42FEFA0000

def highResidual (x : UInt64) : UInt64 := Wasm.IEEE64.add x (highProduct x)

theorem negative_high_scaled_value :
    Wasm.IEEE64.scaledValue 0xBF762E42FEFA0000 =
      -(47632711549 : Int) * 2 ^ 1031 := by decide +kernel

theorem negative_high_value :
    value 0xBF762E42FEFA0000 = -value 0x3F762E42FEFA0000 := by
  rw [value, value, negative_high_scaled_value, ExpReductionExact.high_scaled_value]
  push_cast
  ring

theorem high_product_grid (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    ∃ k : Int, value (ExpReductionSelection.integer x) = (k : ℝ) ∧
      Finite (highProduct x) ∧
      value (highProduct x) = (k : ℝ) * value 0xBF762E42FEFA0000 ∧
      Wasm.IEEE64.scaledValue (highProduct x) =
        (-(47632711549 : Int) * k) * 2 ^ 1031 ∧ k.natAbs ≤ 147457 := by
  obtain ⟨k, hv, hpf, hpv, hkn, _⟩ := ExpReductionSelection.selected_high_product x hxf hx
  change Finite (highProduct x) at hpf
  change value (highProduct x) = (k : ℝ) * value 0xBF762E42FEFA0000 at hpv
  have hr : value (highProduct x) =
      (((-(47632711549 : Int) * k) * 2 ^ 1031 : Int) : ℝ) / (2 : ℝ) ^ 1074 := by
    rw [hpv, value, negative_high_scaled_value]
    push_cast
    ring
  rw [value] at hr
  have hcast :
      (Wasm.IEEE64.scaledValue (highProduct x) : ℝ) =
        (((-(47632711549 : Int) * k) * 2 ^ 1031 : Int) : ℝ) :=
    (div_left_inj' (by positivity : (2 : ℝ) ^ 1074 ≠ 0)).mp hr
  have hs : Wasm.IEEE64.scaledValue (highProduct x) =
      (-(47632711549 : Int) * k) * 2 ^ 1031 := by exact_mod_cast hcast
  exact ⟨k, hv, hpf, hpv, hs, hkn⟩

theorem high_residual_exact (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 768) :
    Finite (highResidual x) ∧
      value (highResidual x) =
        value x - value (ExpReductionSelection.integer x) * value 0x3F762E42FEFA0000 := by
  obtain ⟨k, hv, hpf, hpv, hps, _⟩ := high_product_grid x hxf hx
  have hm := ExpReductionSelection.selection_mixed_error x hxf hx
  rw [hv] at hm
  have hrel := ExpHighPartBounds.high_residual_relative (value x) k hm
  have hr : |value x + value (highProduct x)| ≤ |value x| := by
    rw [hpv, negative_high_value]
    simpa only [mul_neg, sub_eq_add_neg] using hrel
  have hp := ExpHighSubtraction.add_high_grid_exact x (highProduct x) hxf hpf
    (ExpHighSubtraction.input_exponent_bound x hx) (-(47632711549 : Int) * k) hps hr
  refine ⟨hp.1, ?_⟩
  change value (Wasm.IEEE64.add x (highProduct x)) = _
  rw [hp.2, hpv, negative_high_value, hv, mul_neg, sub_eq_add_neg]

#print axioms negative_high_scaled_value
#print axioms negative_high_value
#print axioms high_product_grid
#print axioms high_residual_exact

end Verified.Examples.ExpHighResidual
