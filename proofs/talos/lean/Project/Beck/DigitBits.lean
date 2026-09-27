import Project.Beck.DigitUpdate
import Mathlib.Data.Nat.Digits.Lemmas

namespace Project.Beck.DigitBits

open LeanExe.Examples.BeckExact DigitValue DigitUpdate

theorem digit_value (a : Array UInt64) (ha : Valid a) (index : ℕ)
    (inside : index < a.size) :
    value a / 4294967296 ^ index % 4294967296 = a[index]!.toNat := by
  have valid : ∀ n ∈ a.toList.map UInt64.toNat, n < 4294967296 := by
    intro n member
    obtain ⟨word, wordMember, equal⟩ := List.mem_map.mp member
    rw [← equal]
    exact ha word (Array.mem_toList_iff.mp wordMember)
  rw [value, Nat.ofDigits_div_pow_eq_ofDigits_drop index (by decide) _ valid,
    Nat.ofDigits_mod_eq_head!]
  have listInside : index < (a.toList.map UInt64.toNat).length := by simpa using inside
  rw [List.head!_eq_getElem!, getElem!_pos _ 0 (by simp; omega), List.getElem_drop]
  simp only [Nat.add_zero, List.getElem_map, Array.getElem_toList, getElem!_pos a index inside]
  exact Nat.mod_eq_of_lt (ha _ (Array.getElem_mem inside))

theorem power_split (index : ℕ) :
    2 ^ index = 4294967296 ^ (index / 32) * 2 ^ (index % 32) := by
  have radix : (4294967296 : ℕ) = 2 ^ 32 := by norm_num
  rw [radix, ← pow_mul, ← pow_add, Nat.div_add_mod]

theorem bit_nat (word : UInt64) (index : ℕ) :
    ((word >>> (index % 32).toUInt64) &&& 1).toNat =
      word.toNat / 2 ^ (index % 32) % 2 := by
  have small : index % 32 < 32 := Nat.mod_lt _ (by decide)
  simp [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.toUInt64,
    Nat.mod_eq_of_lt (show index % 32 < 64 by omega),
    Nat.shiftRight_eq_div_pow]

theorem bit_value (a : Array UInt64) (ha : Valid a) (index : ℕ)
    (inside : index < 32 * a.size) :
    ((a[index / 32]! >>> (index % 32).toUInt64) &&& 1).toNat =
      value a / 2 ^ index % 2 := by
  have limbInside : index / 32 < a.size := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  rw [bit_nat, ← digit_value a ha _ limbInside, power_split index,
    ← Nat.div_div_eq_div_mul]
  have divides : 2 ^ (index % 32 + 1) ∣ (4294967296 : ℕ) := by
    change 2 ^ (index % 32 + 1) ∣ 2 ^ 32
    exact pow_dvd_pow 2 (by omega)
  have reduced := Nat.mod_mod_of_dvd (value a / 4294967296 ^ (index / 32)) divides
  rw [pow_succ] at reduced
  calc
    _ = ((value a / 4294967296 ^ (index / 32) % 4294967296) %
        (2 ^ (index % 32) * 2)) / 2 ^ (index % 32) :=
      (Nat.mod_mul_right_div_self _ _ _).symm
    _ = (value a / 4294967296 ^ (index / 32) % (2 ^ (index % 32) * 2)) /
        2 ^ (index % 32) := by rw [reduced]
    _ = _ := Nat.mod_mul_right_div_self _ _ _

theorem mask_value (index : ℕ) :
    ((1 : UInt64) <<< (index % 32).toUInt64).toNat = 2 ^ (index % 32) := by
  have small : index % 32 < 32 := Nat.mod_lt _ (by decide)
  have power : 2 ^ (index % 32) < (2 : ℕ) ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  norm_num at power
  simp [UInt64.toNat_shiftLeft, Nat.toUInt64,
    Nat.mod_eq_of_lt (show index % 32 < 64 by omega), Nat.shiftLeft_eq, power]

theorem low_digit_zero (a : Array UInt64) (ha : Valid a) (index : ℕ)
    (inside : index < 32 * a.size) (zero : value a % 2 ^ (index + 1) = 0) :
    a[index / 32]!.toNat % 2 ^ (index % 32 + 1) = 0 := by
  have limbInside : index / 32 < a.size := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have split : 2 ^ (index + 1) = 4294967296 ^ (index / 32) * 2 ^ (index % 32 + 1) := by
    rw [pow_succ, power_split index, pow_succ]
    ring
  have divided := Nat.mod_mul_right_div_self (value a)
    (4294967296 ^ (index / 32)) (2 ^ (index % 32 + 1))
  rw [← split, zero, Nat.zero_div] at divided
  have divides : 2 ^ (index % 32 + 1) ∣ (4294967296 : ℕ) := by
    change 2 ^ (index % 32 + 1) ∣ 2 ^ 32
    exact pow_dvd_pow 2 (by omega)
  rw [← digit_value a ha _ limbInside, Nat.mod_mod_of_dvd _ divides]
  exact divided.symm

def insertBit (a : Array UInt64) (index : ℕ) : Array UInt64 :=
  a.set! (index / 32) (a[index / 32]! + (1 <<< (index % 32).toUInt64))

theorem insert_correct (a : Array UInt64) (ha : Valid a) (index : ℕ)
    (inside : index < 32 * a.size) (zero : value a % 2 ^ (index + 1) = 0) :
    (insertBit a index).size = a.size ∧ Valid (insertBit a index) ∧
      value (insertBit a index) = value a + 2 ^ index := by
  have limbInside : index / 32 < a.size := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have digitBound := valid_get a ha _ limbInside
  have lowZero := low_digit_zero a ha index inside zero
  have radixDiv : 2 ^ (index % 32 + 1) ∣ (4294967296 : ℕ) := by
    change 2 ^ (index % 32 + 1) ∣ 2 ^ 32
    exact pow_dvd_pow 2 (by omega)
  have gapDiv := Nat.dvd_sub radixDiv (Nat.dvd_of_mod_eq_zero lowZero)
  have gap := Nat.le_of_dvd (show 0 < 4294967296 - a[index / 32]!.toNat by
    dsimp [LimbArithmetic.Valid] at digitBound
    omega) gapDiv
  rw [pow_succ] at gap
  have positive : 0 < (2 : ℕ) ^ (index % 32) := pow_pos (by decide) _
  have sumBound : a[index / 32]!.toNat + 2 ^ (index % 32) < 4294967296 := by omega
  have sumValue : (a[index / 32]! + (1 <<< (index % 32).toUInt64)).toNat =
      a[index / 32]!.toNat + 2 ^ (index % 32) := by
    rw [UInt64.toNat_add, mask_value, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by simp [insertBit], valid_set a ha _ _ ?_, ?_⟩
  · simpa [LimbArithmetic.Valid, sumValue] using sumBound
  · have replaced := value_set a (index / 32)
      (a[index / 32]! + (1 <<< (index % 32).toUInt64)) limbInside
    rw [sumValue] at replaced
    change value (insertBit a index) + _ = _ at replaced
    rw [power_split index]
    nlinarith only [replaced]

#print axioms bit_value
#print axioms insert_correct

end Project.Beck.DigitBits
