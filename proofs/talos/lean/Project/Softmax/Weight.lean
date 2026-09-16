import Project.Softmax.Order
import Project.ExpWide.Numerical

namespace Project.Softmax
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem subtract_max_spread (x m : UInt64) (hx : Finite x) (hm : Finite m)
    (hab : |value x-value m| ≤ 8) (ho : value x ≤ value m) :
    Finite (Wasm.IEEE64.sub x m) ∧ -8 ≤ value (Wasm.IEEE64.sub x m) ∧
    value (Wasm.IEEE64.sub x m) ≤ 0 ∧
    |value (Wasm.IEEE64.sub x m) - (value x-value m)| ≤ 8*arithmeticEpsilon := by
  have hs := F64AddBounds.sub_real_relative x m hx hm (hab.trans_lt (by norm_num))
  have he : |value (Wasm.IEEE64.sub x m) - (value x-value m)| ≤ 8*unitRoundoff64 :=
    hs.2.trans (by nlinarith [show 0 ≤ unitRoundoff64 by norm_num [unitRoundoff64]])
  have heps : 0 < unitRoundoff64 ∧ unitRoundoff64 < 1 ∧
      unitRoundoff64 < arithmeticEpsilon := by norm_num [unitRoundoff64, arithmeticEpsilon]
  have hmag := F64ArithmeticBounds.magnitude_of_error _ _ _ _ he hab
  have hsmall : |value (Wasm.IEEE64.sub x m)| ≤ 8 :=
    F64UnitInterval.abs_le_eight_of_lt_successor _ (by linarith)
  have hr := (abs_le.mp hs.2).2
  rw [abs_of_nonpos (sub_nonpos.mpr ho)] at hr
  refine ⟨hs.1, (abs_le.mp hsmall).1, ?_, he.trans (by linarith)⟩
  nlinarith [mul_nonneg (show 0 ≤ 1-unitRoundoff64 by linarith) (sub_nonneg.mpr ho)]

theorem shifted_weight_spread (x m : UInt64) (hx : Finite x) (hm : Finite m)
    (hab : |value x-value m| ≤ 8) (ho : value x ≤ value m) :
    Finite (ExpWide.evaluate (Wasm.IEEE64.sub x m)) ∧
    1/100000 ≤ value (ExpWide.evaluate (Wasm.IEEE64.sub x m)) ∧
    |value (ExpWide.evaluate (Wasm.IEEE64.sub x m)) - Real.exp (value x-value m)| ≤ 1/399 := by
  have hs := subtract_max_spread x m hx hm hab ho
  have he := ExpWide.evaluate_error _ hs.1 hs.2.1 hs.2.2.1
  have hp := ExpWide.perturbed_exp (value x-value m) (value (Wasm.IEEE64.sub x m))
    (8*arithmeticEpsilon) (sub_nonpos.mpr ho) hs.2.2.2 (by norm_num [arithmeticEpsilon])
  refine ⟨he.1, he.2.1, (abs_sub_le _ _ _).trans ((add_le_add he.2.2 hp).trans ?_)⟩
  norm_num [arithmeticEpsilon]

theorem subtract_max (x m : UInt64) (hx : Finite x) (hm : Finite m)
    (bx : |value x| ≤ 4) (bm : |value m| ≤ 4) (ho : value x ≤ value m) :
    Finite (Wasm.IEEE64.sub x m) ∧ -8 ≤ value (Wasm.IEEE64.sub x m) ∧
    value (Wasm.IEEE64.sub x m) ≤ 0 ∧
    |value (Wasm.IEEE64.sub x m)-(value x-value m)| ≤ 8*arithmeticEpsilon :=
  subtract_max_spread x m hx hm ((abs_sub _ _).trans (by linarith)) ho

theorem shifted_weight (x m : UInt64) (hx : Finite x) (hm : Finite m)
    (bx : |value x| ≤ 4) (bm : |value m| ≤ 4) (ho : value x ≤ value m) :
    Finite (ExpWide.evaluate (Wasm.IEEE64.sub x m)) ∧
    1/100000 ≤ value (ExpWide.evaluate (Wasm.IEEE64.sub x m)) ∧
    |value (ExpWide.evaluate (Wasm.IEEE64.sub x m))-Real.exp (value x-value m)| ≤ 1/399 :=
  shifted_weight_spread x m hx hm ((abs_sub _ _).trans (by linarith)) ho

#print axioms subtract_max
#print axioms shifted_weight
end Project.Softmax
