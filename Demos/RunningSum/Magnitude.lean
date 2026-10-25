import Demos.RunningSum.Spec
import Mathlib.Data.Nat.Digits.Defs

namespace Demos.RunningSum.Magnitude

def RawDigits (digits : Array UInt64) : Prop :=
  ∀ i, i < digits.size → digits[i]!.toNat < 10

def digit (digits : Array UInt64) (i : Nat) : Nat :=
  if i < digits.size then digitValue digits[digits.size - 1 - i]! else 0

def lowValue (digits : Array UInt64) : Nat → Nat
  | 0 => 0
  | n + 1 => lowValue digits n + digit digits n * 10 ^ n

def rawValue (digits : Array UInt64) : Nat :=
  Nat.ofDigits 10 (digits.toList.map UInt64.toNat)

theorem digitsValue_snoc (digits : List UInt64) (byte : UInt64) :
    digitsValue (digits ++ [byte]) = 10 * digitsValue digits + digitValue byte := by
  simp [digitsValue, List.foldl_append]

theorem ofDigits_reverse (digits : List UInt64) :
    Nat.ofDigits 10 (digits.reverse.map digitValue) = digitsValue digits := by
  induction digits using List.reverseRecOn with
  | nil => rfl
  | append_singleton digits byte ih =>
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, Nat.ofDigits, Nat.cast_id, ih, digitsValue_snoc]
      omega

theorem lowValue_eq (digits : Array UInt64) (n : Nat) (hn : n ≤ digits.size) :
    lowValue digits n = Nat.ofDigits 10 ((digits.toList.reverse.take n).map digitValue) := by
  induction n with
  | zero => simp [lowValue]
  | succ n ih =>
      rw [lowValue, ih (by omega)]
      rw [List.take_succ_eq_append_getElem (by simpa using (show n < digits.size by omega))]
      have index : digits.toList.reverse[n]'(by simpa using (show n < digits.size by omega)) =
          digits[digits.size - 1 - n]! := by
        rw [List.getElem_reverse]
        simp only [Array.length_toList, Array.getElem_toList]
        exact (getElem!_pos digits _ (by omega)).symm
      simp only [List.map_append, List.map_singleton, Nat.ofDigits_append,
        Nat.ofDigits_singleton, List.length_map, List.length_take, List.length_reverse,
        Array.length_toList, Nat.min_eq_left (by omega : n ≤ digits.size), index]
      simp only [digit, show n < digits.size by omega, ite_true]
      ring

theorem lowValue_size (digits : Array UInt64) : lowValue digits digits.size = magnitude digits := by
  rw [lowValue_eq digits digits.size le_rfl]
  rw [List.take_of_length_le (by simp)]
  exact ofDigits_reverse digits.toList

theorem digit_lt (digits : Array UInt64) (valid : DecimalDigits digits) (i : Nat) :
    digit digits i < 10 := by
  unfold digit
  split
  · have := valid (digits.size - 1 - i) (by omega)
    unfold digitValue
    omega
  · omega

theorem lowValue_lt (digits : Array UInt64) (valid : DecimalDigits digits) (n : Nat) :
    lowValue digits n < 10 ^ n := by
  induction n with
  | zero => simp [lowValue]
  | succ n ih =>
      have hd := digit_lt digits valid n
      have hp : 0 < 10 ^ n := by positivity
      simp only [lowValue, pow_succ]
      nlinarith

theorem lowValue_stable (digits : Array UInt64) (n : Nat) (hn : digits.size ≤ n) :
    lowValue digits n = magnitude digits := by
  induction n with
  | zero =>
      have size : digits.size = 0 := by omega
      simpa [size, lowValue] using lowValue_size digits
  | succ n ih =>
      by_cases bound : digits.size ≤ n
      · simp [lowValue, digit, Nat.not_lt.mpr bound, ih bound]
      · have same : digits.size = n + 1 := by omega
        simpa only [same] using lowValue_size digits

@[simp] theorem rawValue_empty : rawValue #[] = 0 := rfl

theorem rawValue_push (digits : Array UInt64) (byte : UInt64) :
    rawValue (digits.push byte) = rawValue digits + byte.toNat * 10 ^ digits.size := by
  simp [rawValue, Nat.ofDigits_append, Nat.ofDigits, mul_comm]

theorem rawDigits_push (digits : Array UInt64) (byte : UInt64)
    (valid : RawDigits digits) (bound : byte.toNat < 10) : RawDigits (digits.push byte) := by
  intro i hi
  simp only [Array.size_push] at hi
  rw [getElem!_pos (digits.push byte) i (by simpa using hi), Array.getElem_push]
  split_ifs with same
  · simpa only [getElem!_pos digits i same] using valid i same
  · exact bound

theorem add_digit (x y carry : UInt64)
    (hx : x.toNat < 10) (hy : y.toNat < 10) (hc : carry.toNat ≤ 1) :
    let value := x + y + carry
    value.toNat = x.toNat + y.toNat + carry.toNat ∧
    (value % 10).toNat < 10 ∧ (value / 10).toNat ≤ 1 ∧
    (value % 10).toNat + 10 * (value / 10).toNat = x.toNat + y.toNat + carry.toNat := by
  have hxy : (x + y).toNat = x.toNat + y.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hv : (x + y + carry).toNat = x.toNat + y.toNat + carry.toNat := by
    rw [UInt64.toNat_add, hxy, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  refine ⟨hv, ?_⟩
  simp only [UInt64.toNat_mod, UInt64.toNat_div, hv, UInt64.toNat_ofNat]
  norm_num
  omega

theorem sub_digit (x y carry : UInt64)
    (hx : x.toNat < 10) (hy : y.toNat < 10) (hc : carry.toNat ≤ 1) :
    let value := 10 + x - y - carry
    let borrow : UInt64 := if value < 10 then 1 else 0
    value.toNat = 10 + x.toNat - y.toNat - carry.toNat ∧
    (value % 10).toNat < 10 ∧ borrow.toNat ≤ 1 ∧
    (value % 10).toNat + y.toNat + carry.toNat = x.toNat + 10 * borrow.toNat := by
  have hx10 : ((10 : UInt64) + x).toNat = 10 + x.toNat := by
    rw [UInt64.toNat_add]
    simp only [UInt64.toNat_ofNat]
    omega
  have hyLe : y ≤ 10 + x := UInt64.le_iff_toNat_le.mpr (by rw [hx10]; omega)
  have hxy : ((10 : UInt64) + x - y).toNat = 10 + x.toNat - y.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hyLe, hx10]
  have hcLe : carry ≤ 10 + x - y := UInt64.le_iff_toNat_le.mpr (by rw [hxy]; omega)
  have hv : ((10 : UInt64) + x - y - carry).toNat =
      10 + x.toNat - y.toNat - carry.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hcLe, hxy]
  dsimp only
  refine ⟨hv, ?_⟩
  simp only [UInt64.lt_iff_toNat_lt, hv, UInt64.toNat_mod, UInt64.toNat_ofNat]
  split_ifs <;> simp only [UInt64.toNat_ofNat] <;> norm_num at * <;> omega

end Demos.RunningSum.Magnitude
