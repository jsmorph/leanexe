import Project.Beck.LimbArithmetic
import Mathlib.Data.Nat.Digits.Defs

namespace Project.Beck.DigitValue

open LeanExe.Examples.BeckExact

def value (digits : Array UInt64) : ℕ := Nat.ofDigits 4294967296 (digits.toList.map UInt64.toNat)

def Valid (digits : Array UInt64) : Prop := ∀ digit ∈ digits, LimbArithmetic.Valid digit

theorem value_empty : value #[] = 0 := rfl

theorem value_push (digits : Array UInt64) (digit : UInt64) :
    value (digits.push digit) = value digits + 4294967296 ^ digits.size * digit.toNat := by
  simp [value, Nat.ofDigits_append]

theorem value_bound (digits : Array UInt64) (valid : Valid digits) :
    value digits < 4294967296 ^ digits.size := by
  have bound := Nat.ofDigits_lt_base_pow_length (b := 4294967296)
    (l := digits.toList.map UInt64.toNat) (by decide) (by
      intro digit member
      obtain ⟨word, wordMember, equal⟩ := List.mem_map.mp member
      rw [← equal]
      exact valid word (Array.mem_toList_iff.mp wordMember))
  simpa [value] using bound

theorem lengthFrom_le (count : ℕ) (digits : Array UInt64) : Digits.lengthFrom count digits ≤ count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [Digits.lengthFrom]
    split <;> omega

theorem length_le (digits : Array UInt64) : Digits.length digits ≤ digits.size :=
  lengthFrom_le digits.size digits

theorem lengthFrom_zero (count : ℕ) (digits : Array UInt64)
    (index : ℕ) (lower : Digits.lengthFrom count digits ≤ index) (upper : index < count) :
    digits[index]! = 0 := by
  induction count with
  | zero => omega
  | succ count ih =>
    simp only [Digits.lengthFrom] at lower
    split at lower
    · omega
    · rename_i zero
      have last : digits[count]! = 0 := by simpa using zero
      by_cases same : index = count
      · simpa [same] using last
      · exact ih lower (by omega)

theorem length_zero (digits : Array UInt64)
    (index : ℕ) (lower : Digits.length digits ≤ index) (upper : index < digits.size) :
    digits[index]! = 0 := lengthFrom_zero digits.size digits index lower upper

theorem list_zero (digits : List UInt64) (zero : ∀ digit ∈ digits, digit = 0) :
    Nat.ofDigits 4294967296 (digits.map UInt64.toNat) = 0 := by
  induction digits with
  | nil => rfl
  | cons digit rest ih =>
    have head := zero digit (by simp)
    simp [head, Nat.ofDigits_cons, ih (by intro digit member; exact zero digit (by simp [member]))]

theorem trim_value (digits : Array UInt64) : value (Digits.trim digits) = value digits := by
  have tail : Nat.ofDigits 4294967296
      ((digits.toList.drop (Digits.length digits)).map UInt64.toNat) = 0 := by
    apply list_zero
    intro digit member
    obtain ⟨index, inside, equality⟩ := List.mem_iff_getElem.mp member
    have bound : Digits.length digits + index < digits.size := by
      simp only [List.length_drop, Array.length_toList] at inside
      omega
    have zero := length_zero digits (Digits.length digits + index) (by omega) bound
    rw [List.getElem_drop] at equality
    change digits[Digits.length digits + index] = digit at equality
    rw [getElem!_pos digits (Digits.length digits + index) bound] at zero
    exact equality.symm.trans zero
  have split := congrArg (fun xs : List UInt64 => Nat.ofDigits 4294967296 (xs.map UInt64.toNat))
    (List.take_append_drop (Digits.length digits) digits.toList)
  simp only [List.map_append, Nat.ofDigits_append, tail, mul_zero, add_zero] at split
  simpa [value, Digits.trim] using split

#print axioms trim_value
#print axioms value_bound

end Project.Beck.DigitValue
