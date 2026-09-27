import Project.Beck.DigitDiv
import Project.Beck.IntegerMul

namespace Project.Beck.IntegerDiv

open LeanExe.Examples.BeckExact IntegerAdd

theorem natAbs_value (a : Integer) : (value a).natAbs = DigitValue.value a.digits := by
  cases sign : a.negative <;> simp [value, sign]

theorem divideExact_correct (a b : Integer) (ha : Valid a) (hb : Valid b)
    (nonzero : value b ≠ 0) (divides : value b ∣ value a) :
    ∃ result, Integer.divideExact a b = some result ∧ Valid result ∧
      value result * value b = value a ∧ value result = value a / value b := by
  have positive : 0 < DigitValue.value b.digits := by
    rw [← natAbs_value]
    exact Int.natAbs_pos.mpr nonzero
  have magnitudeDivides : DigitValue.value b.digits ∣ DigitValue.value a.digits := by
    simpa [natAbs_value] using Int.natAbs_dvd_natAbs.mpr divides
  obtain ⟨quotient, remainder, source, quotientValid, remainderValid, remainderBound, equation⟩ :=
    DigitDiv.divRem_correct a.digits b.digits ha.1 hb.1 positive
  have remainderZero : DigitValue.value remainder = 0 := by
    have modulo := Nat.mod_eq_zero_of_dvd magnitudeDivides
    rw [equation] at modulo
    simpa [Nat.add_mod, Nat.mod_eq_of_lt remainderBound] using modulo
  have lengthZero := (length_zero_iff remainder).mpr remainderZero
  have product : (DigitValue.value quotient : ℤ) * (DigitValue.value b.digits : ℤ) =
      (DigitValue.value a.digits : ℤ) := by
    exact_mod_cast (by simpa [remainderZero] using equation.symm :
      DigitValue.value quotient * DigitValue.value b.digits = DigitValue.value a.digits)
  let result := Integer.make (a.negative != b.negative) quotient
  have sourceResult : Integer.divideExact a b = some result := by
    simp [Integer.divideExact, source, lengthZero, result]
  have resultProduct : value result * value b = value a := by
    dsimp only [result]
    rw [make_value]
    cases signA : a.negative <;> cases signB : b.negative <;>
      simp [value, signA, signB, product]
  refine ⟨result, sourceResult, make_valid _ _ quotientValid, resultProduct, ?_⟩
  rw [← resultProduct, Int.mul_ediv_cancel _ nonzero]

#print axioms divideExact_correct

end Project.Beck.IntegerDiv
