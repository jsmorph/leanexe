import LeanExe.Examples.RunningSum
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

namespace Project.RunningSum

def AsciiDigits (bytes : ByteArray) : Prop :=
  ∀ i, i < bytes.size → 48 ≤ bytes[i]!.toNat ∧ bytes[i]!.toNat ≤ 57

def RawDigits (bytes : ByteArray) : Prop :=
  ∀ i, i < bytes.size → bytes[i]!.toNat < 10

def digit (bytes : ByteArray) (i : Nat) : Nat :=
  if i < bytes.size then bytes[bytes.size - 1 - i]!.toNat - 48 else 0

def lowValue (bytes : ByteArray) : Nat → Nat
  | 0 => 0
  | n + 1 => lowValue bytes n + digit bytes n * 10 ^ n

def magnitude (bytes : ByteArray) : Nat := lowValue bytes bytes.size

def integer (value : LeanExe.Examples.RunningSum.Decimal) : Int :=
  if value.negative then -(magnitude value.digits : Int) else magnitude value.digits

def rawValue (bytes : ByteArray) : Nat :=
  Nat.ofDigits 10 (bytes.data.toList.map UInt8.toNat)

theorem digit_lt (bytes : ByteArray) (h : AsciiDigits bytes) (i : Nat) :
    digit bytes i < 10 := by
  unfold digit
  split
  · have := h (bytes.size - 1 - i) (by omega)
    omega
  · omega

theorem lowValue_lt (bytes : ByteArray) (h : AsciiDigits bytes) (n : Nat) :
    lowValue bytes n < 10 ^ n := by
  induction n with
  | zero => simp [lowValue]
  | succ n ih =>
    have hd := digit_lt bytes h n
    have hp : 0 < 10 ^ n := by positivity
    simp only [lowValue, pow_succ]
    nlinarith

theorem lowValue_stable (bytes : ByteArray) (n : Nat) (h : bytes.size ≤ n) :
    lowValue bytes n = magnitude bytes := by
  induction n with
  | zero =>
    have hs : bytes.size = 0 := by omega
    simp [magnitude, hs, lowValue]
  | succ n ih =>
    by_cases hn : bytes.size ≤ n
    · simp [lowValue, digit, Nat.not_lt.mpr hn, ih hn]
    · have he : bytes.size = n + 1 := by omega
      simp [magnitude, he]

@[simp] theorem rawValue_empty : rawValue ByteArray.empty = 0 := rfl

theorem rawValue_push (bytes : ByteArray) (byte : UInt8) :
    rawValue (bytes.push byte) = rawValue bytes + byte.toNat * 10 ^ bytes.size := by
  simp [rawValue, ByteArray.push, Nat.ofDigits_append, Nat.ofDigits, mul_comm]

theorem rawDigits_push (bytes : ByteArray) (byte : UInt8)
    (h : RawDigits bytes) (hb : byte.toNat < 10) : RawDigits (bytes.push byte) := by
  intro i hi
  simp only [ByteArray.size_push] at hi
  rw [ByteArray.getElem!_push]
  split_ifs with heq
  · exact hb
  · exact h i (by omega)

theorem add_digit (x y carry : UInt64)
    (hx : x.toNat < 10) (hy : y.toNat < 10) (hc : carry.toNat ≤ 1) :
    let value := x + y + carry
    value.toNat = x.toNat + y.toNat + carry.toNat ∧
    (value % 10).toUInt8.toNat < 10 ∧ (value / 10).toNat ≤ 1 ∧
    (value % 10).toUInt8.toNat + 10 * (value / 10).toNat =
      x.toNat + y.toNat + carry.toNat := by
  have hxy : (x + y).toNat = x.toNat + y.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hv : (x + y + carry).toNat = x.toNat + y.toNat + carry.toNat := by
    rw [UInt64.toNat_add, hxy, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  refine ⟨hv, ?_⟩
  simp only [UInt64.toNat_toUInt8, UInt64.toNat_mod, UInt64.toNat_div, hv,
    UInt64.toNat_ofNat]
  norm_num
  omega

theorem sub_digit (x y carry : UInt64)
    (hx : x.toNat < 10) (hy : y.toNat < 10) (hc : carry.toNat ≤ 1) :
    let value := 10 + x - y - carry
    let borrow : UInt64 := if value < 10 then 1 else 0
    value.toNat = 10 + x.toNat - y.toNat - carry.toNat ∧
    (value % 10).toUInt8.toNat < 10 ∧ borrow.toNat ≤ 1 ∧
    (value % 10).toUInt8.toNat + y.toNat + carry.toNat =
      x.toNat + 10 * borrow.toNat := by
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
  simp only [UInt64.lt_iff_toNat_lt, hv, UInt64.toNat_toUInt8,
    UInt64.toNat_mod, UInt64.toNat_ofNat]
  split_ifs <;> simp only [UInt64.toNat_ofNat] <;> norm_num at * <;> omega

#print axioms add_digit
#print axioms sub_digit

end Project.RunningSum
