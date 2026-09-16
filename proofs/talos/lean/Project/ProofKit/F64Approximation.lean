import Project.ProofKit.F64Horner

namespace Project.ProofKit.F64Horner
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem Approximation.weaken {w : UInt64} {r b e b' e' : ℝ}
    (h : Approximation w r b e) (hb : b ≤ b') (he : e ≤ e') :
    Approximation w r b' e' := ⟨h.finite, h.magnitude.trans hb, h.accuracy.trans he⟩

theorem Approximation.exact (w : UInt64) (hf : Finite w) (b : ℝ) (hb : |value w| ≤ b) :
    Approximation w (value w) b 0 := ⟨hf, hb, by simp⟩

theorem Approximation.mul {a b : UInt64} {p q ba bb ea eb bound qb : ℝ}
    (ha : Approximation a p ba ea) (hb : Approximation b q bb eb)
    (hq : |q| ≤ qb) (hbound : 1 ≤ bound) (hmax : bound < (2:ℝ)^1022)
    (hprod : ba*bb ≤ bound) :
    Approximation (Wasm.IEEE64.mul a b) (p*q) (bound + arithmeticEpsilon*bound)
      (arithmeticEpsilon*bound + ba*eb + qb*ea) := by
  have hba : 0 ≤ ba := (abs_nonneg _).trans ha.magnitude
  have hbb : 0 ≤ bb := (abs_nonneg _).trans hb.magnitude
  have he : |value a * value b| ≤ bound := by
    rw [abs_mul]
    exact (mul_le_mul ha.magnitude hb.magnitude (abs_nonneg _) hba).trans hprod
  have hm := F64ArithmeticBounds.mul_error a b ha.finite hb.finite bound hbound hmax he
  have h1 : |value a * (value b-q)| ≤ ba*eb := by
    rw [abs_mul]
    exact mul_le_mul ha.magnitude hb.accuracy (abs_nonneg _) hba
  have h2 : |q * (value a-p)| ≤ qb*ea := by
    rw [abs_mul]
    exact mul_le_mul hq ha.accuracy (abs_nonneg _) ((abs_nonneg _).trans hq)
  have hid : value a*value b-p*q = value a*(value b-q)+q*(value a-p) := by ring
  have hd : |value a*value b-p*q| ≤ ba*eb+qb*ea := by
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  refine ⟨hm.1, F64ArithmeticBounds.magnitude_of_error _ _ _ bound hm.2 he, ?_⟩
  exact (abs_sub_le _ _ _).trans ((add_le_add hm.2 hd).trans_eq (by ring))

theorem Approximation.add {a b : UInt64} {p q ba bb ea eb bound : ℝ}
    (ha : Approximation a p ba ea) (hb : Approximation b q bb eb)
    (hbound : 1 ≤ bound) (hmax : bound < (2:ℝ)^1023) (hsum : ba+bb ≤ bound) :
    Approximation (Wasm.IEEE64.add a b) (p+q) (bound + arithmeticEpsilon*bound)
      (arithmeticEpsilon*bound + ea + eb) := by
  have he : |value a+value b| ≤ bound :=
    (abs_add_le _ _).trans ((add_le_add ha.magnitude hb.magnitude).trans hsum)
  have hm := F64ArithmeticBounds.add_error a b ha.finite hb.finite bound hbound hmax he
  have hd : |value a+value b-(p+q)| ≤ ea+eb := by
    rw [show value a+value b-(p+q) = (value a-p)+(value b-q) by ring]
    exact (abs_add_le _ _).trans (add_le_add ha.accuracy hb.accuracy)
  refine ⟨hm.1, F64ArithmeticBounds.magnitude_of_error _ _ _ bound hm.2 he, ?_⟩
  exact (abs_sub_le _ _ _).trans ((add_le_add hm.2 hd).trans_eq (by ring))

#print axioms Approximation.mul
#print axioms Approximation.add
end Project.ProofKit.F64Horner
