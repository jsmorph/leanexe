import Project.Gelu.Numerical
import Project.Gelu.Perturbation
import Project.ProofKit.F64Bounded

namespace Project.Gelu
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem three_value : value 0x4008000000000000 = 3 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem inDomain_iff (x : UInt64) : inDomain x = true ↔ Finite x ∧ |value x| ≤ 3 := by
  have h := F64Order.absBits_le_iff x 0x4008000000000000
    (by unfold CodeLib.IEEE64.Finite; decide)
  simpa only [inDomain, decide_eq_true_eq,
    show F64Order.absBits 0x4008000000000000 = 0x4008000000000000 by decide,
    three_value, abs_of_pos (by norm_num : (0:ℝ)<3)] using h

def NumericalResult (x : UInt64) (r : ExpSmall.Result) : Prop :=
  r.status = 0 ∧ Finite r.bits ∧ |value r.bits - Real.gelu (value x)| ≤ 1/100

theorem gelu_numerical (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 3) :
    NumericalResult x (gelu x) := by
  have hd := (inDomain_iff x).mpr ⟨hf, hx⟩
  have he := evaluate_error x hf hx
  simpa only [NumericalResult, gelu, hd, Bool.true_eq, ite_true, true_and] using he

theorem gelu_perturbed (x : UInt64) (r error : ℝ) (hf : Finite x)
    (hx : |value x| ≤ 3) (hr : |r| ≤ 3) (he : |value x-r| ≤ error) :
    |value (gelu x).bits - Real.gelu r| ≤ 1/100 + 4*error := by
  have h := (gelu_numerical x hf hx).2.2
  have hp := Real.gelu_lipschitz (value x) r hx hr
  exact (abs_sub_le _ _ _).trans (add_le_add h (hp.trans (by linarith)))

#print axioms gelu_numerical
#print axioms gelu_perturbed
end Project.Gelu
