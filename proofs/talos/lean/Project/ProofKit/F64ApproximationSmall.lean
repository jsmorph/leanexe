import Project.ProofKit.F64Approximation
import Project.ProofKit.F64AddBounds
import Project.ProofKit.F64MulBounds
import Project.ProofKit.RealProductError

namespace Project.ProofKit.F64Horner
open CodeLib.IEEE64

theorem Approximation.add_relative {a b : UInt64} {p q ba bb ea eb bound : ℝ}
    (ha : Approximation a p ba ea) (hb : Approximation b q bb eb)
    (hmax : bound < (2 : ℝ)^1023) (hsum : ba+bb ≤ bound) :
    Approximation (Wasm.IEEE64.add a b) (p+q) (bound + unitRoundoff64*bound)
      (unitRoundoff64*bound + ea + eb) := by
  have he : |value a+value b| ≤ bound :=
    (abs_add_le _ _).trans ((add_le_add ha.magnitude hb.magnitude).trans hsum)
  have hm := F64AddBounds.add_real_relative a b ha.finite hb.finite (he.trans_lt hmax)
  have hr : |value (Wasm.IEEE64.add a b)-(value a+value b)| ≤ unitRoundoff64*bound :=
    hm.2.trans (mul_le_mul_of_nonneg_left he (by norm_num [unitRoundoff64]))
  have hd : |value a+value b-(p+q)| ≤ ea+eb := by
    rw [show value a+value b-(p+q) = (value a-p)+(value b-q) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha.accuracy hb.accuracy)
  refine ⟨hm.1, F64ArithmeticBounds.magnitude_of_error _ _ _ bound hr he, ?_⟩
  exact (abs_sub_le _ _ _).trans ((add_le_add hr hd).trans_eq (by ring))

theorem Approximation.mul_mixed {a b : UInt64} {p q ba bb ea eb bound qb : ℝ}
    (ha : Approximation a p ba ea) (hb : Approximation b q bb eb)
    (hq : |q| ≤ qb) (hmax : bound < (2 : ℝ)^1022) (hprod : ba*bb ≤ bound) :
    Approximation (Wasm.IEEE64.mul a b) (p*q)
      (bound + (unitRoundoff64*bound + multiplicationUnderflowEpsilon))
      (unitRoundoff64*bound + multiplicationUnderflowEpsilon + ba*eb + ea*qb) := by
  have he : |value a*value b| ≤ bound := by
    rw [abs_mul]
    exact (mul_le_mul ha.magnitude hb.magnitude (abs_nonneg _)
      ((abs_nonneg _).trans ha.magnitude)).trans hprod
  have hm := F64MulBounds.mul_real_mixed a b ha.finite hb.finite (he.trans_lt hmax)
  have hr : |value (Wasm.IEEE64.mul a b)-value a*value b| ≤
      unitRoundoff64*bound + multiplicationUnderflowEpsilon :=
    hm.2.trans (add_le_add
      (mul_le_mul_of_nonneg_left he (by norm_num [unitRoundoff64])) le_rfl)
  have hd := RealProductError.product_error _ _ _ _ _ _ _ _
    ha.accuracy hb.accuracy ha.magnitude hq
  refine ⟨hm.1, F64ArithmeticBounds.magnitude_of_error _ _ _ bound hr he, ?_⟩
  exact (abs_sub_le _ _ _).trans ((add_le_add hr hd).trans_eq (by ring))

#print axioms Approximation.add_relative
#print axioms Approximation.mul_mixed
end Project.ProofKit.F64Horner
