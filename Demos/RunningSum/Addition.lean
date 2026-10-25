import Demos.RunningSum.MagnitudeCombine
import Demos.RunningSum.Compare

namespace Demos.RunningSum

theorem add_correct (a b : Decimal) (ha : a.Valid) (hb : b.Valid)
    (bound : max a.digits.size b.digits.size + 3 < UInt64.size) :
    (add a b).Valid ∧ (add a b).Fits ∧
      (add a b).value = a.value + b.value ∧
      (add a b).digits.size ≤ max a.digits.size b.digits.size + 1 := by
  have aBound : a.digits.size < UInt64.size := by omega
  have bBound : b.digits.size < UInt64.size := by omega
  have arithmeticBound : max a.digits.size b.digits.size + 1 < UInt64.size := by omega
  unfold add
  simp only [magnitudeLess_correct a.digits b.digits ha hb aBound bBound,
    beq_iff_eq, decide_eq_true_eq]
  split_ifs with sign less
  · obtain ⟨normal, value, size⟩ := combine_add a.digits b.digits ha.1 hb.1 arithmeticBound
    refine ⟨normal, ?_, ?_, size⟩
    · change (combineMagnitude a.digits b.digits false).size + 2 < UInt64.size
      omega
    · cases hsa : a.negative <;> cases hsb : b.negative <;>
        simp_all [Decimal.value, Nat.cast_add]
      omega
  · obtain ⟨normal, value, size⟩ := combine_sub b.digits a.digits hb.1 ha.1
      (by simpa only [max_comm] using arithmeticBound) (by omega)
    have resultSize : (combineMagnitude b.digits a.digits true).size ≤
        max a.digits.size b.digits.size + 1 := by simpa only [max_comm] using size
    refine ⟨normal, ?_, ?_, resultSize⟩
    · change (combineMagnitude b.digits a.digits true).size + 2 < UInt64.size
      omega
    · cases hsa : a.negative <;> cases hsb : b.negative <;>
        simp_all [Decimal.value] <;> omega
  · obtain ⟨normal, value, size⟩ := combine_sub a.digits b.digits ha.1 hb.1 arithmeticBound (by omega)
    refine ⟨normal, ?_, ?_, size⟩
    · change (combineMagnitude a.digits b.digits true).size + 2 < UInt64.size
      omega
    · cases hsa : a.negative <;> cases hsb : b.negative <;>
        simp_all [Decimal.value] <;> omega

theorem add_valid (a b : Decimal) (ha : a.Valid) (hb : b.Valid)
    (bound : max a.digits.size b.digits.size + 3 < UInt64.size) : (add a b).Valid :=
  (add_correct a b ha hb bound).1

theorem add_fits (a b : Decimal) (ha : a.Valid) (hb : b.Valid)
    (bound : max a.digits.size b.digits.size + 3 < UInt64.size) : (add a b).Fits :=
  (add_correct a b ha hb bound).2.1

theorem add_value (a b : Decimal) (ha : a.Valid) (hb : b.Valid)
    (bound : max a.digits.size b.digits.size + 3 < UInt64.size) :
    (add a b).value = a.value + b.value := (add_correct a b ha hb bound).2.2.1

theorem add_size_le (a b : Decimal) (ha : a.Valid) (hb : b.Valid)
    (bound : max a.digits.size b.digits.size + 3 < UInt64.size) :
    (add a b).digits.size ≤ max a.digits.size b.digits.size + 1 :=
  (add_correct a b ha hb bound).2.2.2

end Demos.RunningSum
