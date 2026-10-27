import Demos.RunningSum.Spec
import Demos.RunningSum.Magnitude

namespace Demos.RunningSum

def naturalEncoding (value : Nat) : List UInt8 :=
  if value = 0 then [48]
  else (Nat.digits 10 value).reverse.map fun digit => UInt8.ofNat (digit + 48)

def integerEncoding (value : Int) : List UInt8 :=
  (if value < 0 then [45] else []) ++ naturalEncoding value.natAbs ++ [10]

def DecimalOutput (value : Int) (bytes : LeanExe.Bytes) : Prop :=
  bytes.data.data.toList = integerEncoding value

theorem render_size (number : Decimal) (fits : number.Fits) :
    (render number).data.size =
      if number.digits.size = 0 then 2
      else number.digits.size + (if number.negative then 1 else 0) + 1 := by
  have bound : number.digits.size + 2 < UInt64.size := fits
  have sizeNat : number.digits.size.toUInt64.toNat = number.digits.size :=
    UInt64.toNat_ofNat_of_lt' (by omega)
  have bound64 : number.digits.size + 2 < 18446744073709551616 := bound
  have sizeZero : number.digits.size.toUInt64 = 0 ↔ number.digits.size = 0 := by
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      simpa [sizeNat] using this
    · intro h
      simp [h]
  by_cases empty : number.digits.size = 0
  · simp [render, empty, ByteArray.size]
  · simp only [render, beq_iff_eq, sizeZero, empty, ↓reduceIte,
      LeanExe.Bytes.data_size_build]
    cases number.negative <;> simp [UInt64.toNat_add, sizeNat] <;> omega

theorem render_nonempty (number : Decimal) (fits : number.Fits) :
    0 < (render number).data.size := by
  rw [render_size number fits]
  split <;> omega

theorem render_size_le (number : Decimal) (fits : number.Fits) :
    (render number).data.size ≤ number.digits.size + 2 := by
  rw [render_size number fits]
  split
  · omega
  · cases number.negative <;> simp

theorem render_size_lt (number : Decimal) (fits : number.Fits) :
    (render number).data.size < UInt64.size :=
  lt_of_le_of_lt (render_size_le number fits) fits

theorem render_data (number : Decimal) (fits : number.Fits) :
    (render number).data.data =
      (if number.digits.size = 0 then #[48, 10]
       else (if number.negative then #[45] else #[]) ++ number.digits ++ #[10]).map
        UInt64.toUInt8 := by
  have bound : number.digits.size + 2 < UInt64.size := fits
  have sizeNat : number.digits.size.toUInt64.toNat = number.digits.size :=
    UInt64.toNat_ofNat_of_lt' (by omega)
  have sizeZero : number.digits.size.toUInt64 = 0 ↔ number.digits.size = 0 := by
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      simpa [sizeNat] using this
    · intro h
      simp [h]
  by_cases empty : number.digits.size = 0
  · simp [render, empty]
  · have nonzero : number.digits.size.toUInt64 ≠ 0 := by simpa [sizeZero] using empty
    have bound64 : number.digits.size + 2 < 18446744073709551616 := bound
    simp only [empty, ↓reduceIte]
    cases negative : number.negative
    · simp only [Bool.false_eq_true, ↓reduceIte, Array.empty_append]
      apply Array.ext
      · simp only [Array.size_map, Array.size_append, Array.size_singleton]
        change (render number).data.size = number.digits.size + 1
        simpa only [empty, ↓reduceIte, negative, Bool.false_eq_true, Nat.add_zero]
          using render_size number fits
      · intro i hi hj
        have iNat : (UInt64.ofNat i).toNat = i :=
          UInt64.toNat_ofNat_of_lt' (by
            have size := render_size number fits
            simp only [empty, ↓reduceIte, negative, Bool.false_eq_true,
              Nat.add_zero] at size
            change i < (render number).data.size at hi
            omega)
        have equal : UInt64.ofNat i = number.digits.size.toUInt64 ↔
            i = number.digits.size := by
          constructor
          · intro h
            have := congrArg UInt64.toNat h
            simpa [iNat, sizeNat] using this
          · intro h
            simp [h]
        have noSign : ((0 : UInt64) == 1) = false := by decide
        simp only [render, beq_iff_eq, nonzero, ↓reduceIte, negative,
          Bool.false_eq_true, UInt64.add_zero, UInt64.sub_zero, noSign, Bool.false_and,
          LeanExe.Bytes.build, Array.getElem_ofFn, equal, iNat,
          Array.getElem_map, Array.getElem_append]
        by_cases last : i = number.digits.size
        · subst i
          simp only [ite_true, lt_self_iff_false, ↓reduceDIte, Nat.sub_self,
            Array.getElem_singleton]
        · have inside : i < number.digits.size := by
            simp only [Array.size_map, Array.size_append, Array.size_singleton] at hj
            omega
          simp only [last, ↓reduceIte, inside, ↓reduceDIte,
            getElem!_pos number.digits i inside]
    · simp only [↓reduceIte]
      apply Array.ext
      · simp only [Array.size_map, Array.size_append, Array.size_singleton]
        change (render number).data.size = 1 + number.digits.size + 1
        have size := render_size number fits
        simpa only [empty, ↓reduceIte, negative, Nat.add_comm] using size
      · intro i hi hj
        have iBound : i < number.digits.size + 2 := by
          change i < (render number).data.size at hi
          rw [render_size number fits] at hi
          simpa [empty, negative, Nat.add_assoc] using hi
        have iNat : (UInt64.ofNat i).toNat = i :=
          UInt64.toNat_ofNat_of_lt' (by omega)
        have lengthNat : (number.digits.size.toUInt64 + 1).toNat =
            number.digits.size + 1 := by
          simp only [UInt64.toNat_add, sizeNat, UInt64.reduceToNat]
          omega
        have equal : UInt64.ofNat i = number.digits.size.toUInt64 + 1 ↔
            i = number.digits.size + 1 := by
          constructor
          · intro h
            have := congrArg UInt64.toNat h
            simpa [iNat, lengthNat] using this
          · intro h
            apply UInt64.toNat.inj
            rw [iNat, lengthNat, h]
        have zero : UInt64.ofNat i = 0 ↔ i = 0 := by
          constructor
          · intro h
            have := congrArg UInt64.toNat h
            simpa [iNat] using this
          · rintro rfl
            rfl
        have yesSign : ((1 : UInt64) == 1) = true := by decide
        simp only [render, beq_iff_eq, nonzero, ↓reduceIte, negative, yesSign,
          Bool.true_and, LeanExe.Bytes.build, Array.getElem_ofFn, equal, zero,
          Array.getElem_map, Array.getElem_append, Array.size_append,
          Array.size_singleton]
        by_cases last : i = number.digits.size + 1
        · subst i
          simp only [ite_true, show ¬number.digits.size + 1 < 1 + number.digits.size by omega,
            ↓reduceDIte, show number.digits.size + 1 - (1 + number.digits.size) = 0 by omega,
            Array.getElem_singleton]
        · by_cases first : i = 0
          · subst i
            simp only [last, ↓reduceIte, show 0 < 1 + number.digits.size by omega,
              show 0 < (1 : Nat) by omega, ↓reduceDIte, Array.getElem_singleton]
          · have subNat : (UInt64.ofNat i - 1).toNat = i - 1 := by
              rw [UInt64.toNat_sub_of_le]
              · simp [iNat]
              · simp only [UInt64.le_iff_toNat_le, iNat, UInt64.reduceToNat]
                omega
            have inside : i - 1 < number.digits.size := by omega
            simp only [last, first, ↓reduceIte,
              subNat, show i < 1 + number.digits.size by omega,
              show ¬i < 1 by omega, ↓reduceDIte,
              getElem!_pos number.digits (i - 1) inside]

theorem normal_natDigits (digits : Array UInt64) (normal : NormalDigits digits) :
    Nat.digits 10 (magnitude digits) = digits.toList.reverse.map digitValue := by
  rw [magnitude, ← Magnitude.ofDigits_reverse]
  apply Nat.digits_ofDigits 10 (by decide)
  · intro d hd
    obtain ⟨byte, member, rfl⟩ := List.mem_map.mp hd
    have member' : byte ∈ digits := by simpa using member
    obtain ⟨i, hi, same⟩ := Array.mem_iff_getElem.mp member'
    have bounds := normal.1 i hi
    rw [← same, ← getElem!_pos digits i hi]
    unfold digitValue
    omega
  · intro nonempty
    rw [List.getLast_map, List.getLast_reverse, List.head_eq_getElem,
      Array.getElem_toList]
    have sizePositive : 0 < digits.size := by
      by_contra h
      have empty := Array.eq_empty_of_size_eq_zero (show digits.size = 0 by omega)
      simp [empty] at nonempty
    have bounds := normal.1 0 sizePositive
    have leading := normal.2.resolve_left (by omega)
    rw [← getElem!_pos digits 0 sizePositive]
    unfold digitValue
    omega

theorem normal_magnitude_eq_zero_iff (digits : Array UInt64) (normal : NormalDigits digits) :
    magnitude digits = 0 ↔ digits.size = 0 := by
  constructor
  · intro zero
    have same := normal_natDigits digits normal
    rw [zero, Nat.digits_zero] at same
    have empty : digits = #[] := by simpa using same.symm
    simp [empty]
  · intro empty
    have same := Array.eq_empty_of_size_eq_zero empty
    simp [same, magnitude, digitsValue]

theorem naturalEncoding_magnitude (digits : Array UInt64) (normal : NormalDigits digits)
    (nonempty : digits.size ≠ 0) :
    naturalEncoding (magnitude digits) = digits.toList.map UInt64.toUInt8 := by
  have nonzero := (normal_magnitude_eq_zero_iff digits normal).not.mpr nonempty
  rw [naturalEncoding, ite_eq_right nonzero, normal_natDigits digits normal,
    ← List.map_reverse, List.reverse_reverse, List.map_map]
  apply List.map_congr_left
  intro byte member
  obtain ⟨i, hi, same⟩ := Array.mem_iff_getElem.mp (by simpa using member)
  have bounds := normal.1 i hi
  rw [← same, ← getElem!_pos digits i hi]
  change UInt8.ofNat (digitValue digits[i]! + 48) = UInt8.ofNat digits[i]!.toNat
  congr 1
  unfold digitValue
  omega

theorem render_correct (number : Decimal) (valid : number.Valid) (fits : number.Fits) :
    DecimalOutput number.value (render number) := by
  unfold DecimalOutput
  rw [render_data number fits]
  by_cases empty : number.digits.size = 0
  · have same := Array.eq_empty_of_size_eq_zero empty
    simp [same, Decimal.value, magnitude, digitsValue, integerEncoding, naturalEncoding]
  · have nonzero := (normal_magnitude_eq_zero_iff number.digits valid).not.mpr empty
    have encoded := naturalEncoding_magnitude number.digits valid empty
    cases negative : number.negative
    · simp [empty, negative, Decimal.value, integerEncoding, encoded]
    · have positive : 0 < magnitude number.digits := by omega
      simp [empty, negative, Decimal.value, integerEncoding, encoded, positive]

theorem decimalOutput_unique (value : Int) (a b : LeanExe.Bytes)
    (ha : DecimalOutput value a) (hb : DecimalOutput value b) : a = b := by
  cases a with
  | mk a =>
      cases b with
      | mk b =>
          congr 1
          apply ByteArray.ext
          apply Array.toList_inj.mp
          exact ha.trans hb.symm

@[simp] theorem integerEncoding_zero : integerEncoding 0 = [48, 10] := by
  decide

theorem render_zero (number : Decimal) (valid : number.Valid) (fits : number.Fits)
    (zero : number.value = 0) : render number = bytes![48, 10] := by
  apply decimalOutput_unique 0
  · simpa only [zero] using render_correct number valid fits
  · exact integerEncoding_zero.symm

end Demos.RunningSum
