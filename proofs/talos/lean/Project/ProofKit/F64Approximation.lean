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

theorem Approximation.div_pos {a b : UInt64} {p q ba bb ea eb bound ratioBound lower : ℝ}
    (ha : Approximation a p ba ea) (hb : Approximation b q bb eb)
    (hl : 0 < lower) (hd : lower ≤ value b) (hq : 0 < q) (hr : |p/q| ≤ ratioBound)
    (hbound : 1 ≤ bound) (hmax : bound < (2:ℝ)^1022) (hba : ba ≤ bound*lower) :
    Approximation (Wasm.IEEE64.div a b) (p/q) (bound+arithmeticEpsilon*bound)
      (arithmeticEpsilon*bound+(ea+ratioBound*eb)/lower) := by
  have dp : 0 < value b := hl.trans_le hd
  have rn : 0 ≤ ratioBound := (abs_nonneg _).trans hr
  have ean : 0 ≤ ea := (abs_nonneg _).trans ha.accuracy
  have ebn : 0 ≤ eb := (abs_nonneg _).trans hb.accuracy
  have hid : value a/value b-p/q = ((value a-p)+(p/q)*(q-value b))/value b := by
    field_simp
    ring
  have he : |value a/value b-p/q| ≤ (ea+ratioBound*eb)/lower := by
    rw [hid, abs_div, abs_of_pos dp]
    have hterm : |(p/q)*(q-value b)| ≤ ratioBound*eb := by
      rw [abs_mul, abs_sub_comm q]
      exact mul_le_mul hr hb.accuracy (abs_nonneg _) rn
    have hn := (abs_add_le _ _).trans (add_le_add ha.accuracy hterm)
    exact (div_le_div_of_nonneg_right hn dp.le).trans
      (div_le_div_of_nonneg_left (add_nonneg ean (mul_nonneg rn ebn)) hl hd)
  have hmag : |value a/value b| ≤ bound := by
    rw [abs_div, abs_of_pos dp]
    apply (div_le_iff₀ dp).mpr
    exact ha.magnitude.trans (hba.trans
      (mul_le_mul_of_nonneg_left hd (by linarith)))
  have hnz : Wasm.IEEE64.scaledMagnitude b ≠ 0 := by
    intro hh
    simp [value, Wasm.IEEE64.scaledValue, hh] at dp
  have ho := F64ArithmeticBounds.div_error a b ha.finite hb.finite hnz bound hbound hmax hmag
  refine ⟨ho.1, F64ArithmeticBounds.magnitude_of_error _ _ _ bound ho.2 hmag, ?_⟩
  exact (abs_sub_le _ _ _).trans (add_le_add ho.2 he)

theorem Approximation.div_ge_one {a b : UInt64} {p q ba bb ea eb bound pb : ℝ}
    (ha : Approximation a p ba ea) (hb : Approximation b q bb eb)
    (hd : 1 ≤ value b) (hq : 1 ≤ q) (hp : |p| ≤ pb)
    (hbound : 1 ≤ bound) (hmax : bound < (2:ℝ)^1022) (hba : ba ≤ bound) :
    Approximation (Wasm.IEEE64.div a b) (p/q) (bound+arithmeticEpsilon*bound)
      (arithmeticEpsilon*bound+ea+pb*eb) := by
  have qp : 0 < q := by linarith
  have hratio : |p/q| ≤ pb := by
    rw [abs_div, abs_of_pos qp]
    apply (div_le_iff₀ qp).mpr
    exact hp.trans (by nlinarith [mul_le_mul_of_nonneg_left hq ((abs_nonneg _).trans hp)])
  simpa only [div_one, mul_one, add_assoc] using
    ha.div_pos hb (by norm_num : (0:ℝ) < 1) hd qp hratio hbound hmax (by simpa using hba)

#print axioms Approximation.div_pos
#print axioms Approximation.div_ge_one
end Project.ProofKit.F64Horner
