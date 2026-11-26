import LeanExe.Base

/-!
Core decides `ByteArray.IsValidUTF8` with `ByteArray.validateUTF8`, which checks each character of
two, three, or four bytes with `ByteArray.utf8DecodeChar?.verify₂`, `verify₃`, or `verify₄`.  Each
assembles the code point from the low bits of the bytes and compares it with the bounds of
overlong encodings, of surrogates, and of the last code point.  `verify₂_iff`, `verify₃_iff`, and
`verify₄_iff` state these decisions as the conditions of Table 3-7 of the Unicode Standard: every
byte after the first lies from `0x80` to `0xBF`, and the first two bytes lie in the ranges of the
table's rows.

`verify₃` compares the assembled value with `0x800`, `0xD800`, and `0xDFFF`, and `verify₄` with
`0x10000` and `0x10FFFF`.  Each comparison is equivalent to one with a multiple of 64 for three
bytes, or of 4,096 for four bytes, and the bits of the third and fourth bytes lie below that
multiple, so they never change the result.  The decisions therefore depend on the first two bytes
and on whether the later bytes are continuation bytes.  `toNat_assemble₂Unchecked`,
`toNat_assemble₃Unchecked`, and `toNat_assemble₄Unchecked` give the assembled values as sums, on
which `omega` decides the comparisons, and `forall_uint8` reduces a statement about every byte to
one that `decide` checks in the kernel.
-/

namespace Verified.Shim

open ByteArray.utf8DecodeChar?

/-- A statement about every byte follows from its instances at `UInt8.ofNatLT n` for `n` below
256, which `decide` checks through `Nat.decidableBallLT`. -/
theorem forall_uint8 {P : UInt8 → Prop} (h : ∀ n (hn : n < UInt8.size), P (UInt8.ofNatLT n hn))
    (w : UInt8) : P w := by
  simpa using h w.toNat w.toNat_lt

theorem isUTF8ContinuationByte_eq (x : UInt8) :
    x.isUTF8ContinuationByte = (0x80 ≤ x && x < 0xC0) := by
  revert x
  refine forall_uint8 ?_
  decide +kernel

private theorem or_eq_add {a b k : Nat} (h : b < 2 ^ k) : a <<< k ||| b = a <<< k + b :=
  (Nat.shiftLeft_add_eq_or_of_lt h a).symm

theorem toNat_assemble₂Unchecked (w x : UInt8) :
    (assemble₂Unchecked w x).toNat = w.toNat % 32 * 64 + x.toNat % 64 := by
  have hw : w.toNat &&& 31 = w.toNat % 32 := Nat.and_two_pow_sub_one_eq_mod _ 5
  have hx : x.toNat &&& 63 = x.toNat % 64 := Nat.and_two_pow_sub_one_eq_mod _ 6
  simp (disch := omega) only [assemble₂Unchecked, UInt32.toNat_or, UInt32.toNat_shiftLeft,
    UInt8.toNat_toUInt32, UInt8.toNat_and, UInt8.reduceToNat, UInt32.reduceToNat, hw, hx,
    Nat.mod_eq_of_lt, or_eq_add]
  omega

theorem toNat_assemble₃Unchecked (w x y : UInt8) :
    (assemble₃Unchecked w x y).toNat = w.toNat % 16 * 4096 + x.toNat % 64 * 64 + y.toNat % 64 := by
  have hw : w.toNat &&& 15 = w.toNat % 16 := Nat.and_two_pow_sub_one_eq_mod _ 4
  have hx : x.toNat &&& 63 = x.toNat % 64 := Nat.and_two_pow_sub_one_eq_mod _ 6
  have hy : y.toNat &&& 63 = y.toNat % 64 := Nat.and_two_pow_sub_one_eq_mod _ 6
  simp only [assemble₃Unchecked, UInt32.toNat_or, Nat.or_assoc]
  simp (disch := omega) only [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_and,
    UInt8.reduceToNat, UInt32.reduceToNat, hw, hx, hy, Nat.mod_eq_of_lt, or_eq_add]
  omega

theorem toNat_assemble₄Unchecked (w x y z : UInt8) :
    (assemble₄Unchecked w x y z).toNat =
      w.toNat % 8 * 262144 + x.toNat % 64 * 4096 + y.toNat % 64 * 64 + z.toNat % 64 := by
  have hw : w.toNat &&& 7 = w.toNat % 8 := Nat.and_two_pow_sub_one_eq_mod _ 3
  have hx : x.toNat &&& 63 = x.toNat % 64 := Nat.and_two_pow_sub_one_eq_mod _ 6
  have hy : y.toNat &&& 63 = y.toNat % 64 := Nat.and_two_pow_sub_one_eq_mod _ 6
  have hz : z.toNat &&& 63 = z.toNat % 64 := Nat.and_two_pow_sub_one_eq_mod _ 6
  simp only [assemble₄Unchecked, UInt32.toNat_or, Nat.or_assoc]
  simp (disch := omega) only [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, UInt8.toNat_and,
    UInt8.reduceToNat, UInt32.reduceToNat, hw, hx, hy, hz, Nat.mod_eq_of_lt, or_eq_add]
  omega

theorem verify₂_iff {w x : UInt8} (h₀ : 0xC0 ≤ w) (h₁ : w < 0xE0) :
    verify₂ w x = true ↔ 0xC2 ≤ w ∧ 0x80 ≤ x ∧ x < 0xC0 := by
  have := toNat_assemble₂Unchecked w x
  have := w.toNat_lt
  have := x.toNat_lt
  simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at h₀ h₁
  simp [verify₂, isUTF8ContinuationByte_eq, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt,
    UInt32.le_iff_toNat_le, *]
  omega

theorem verify₃_iff {w x y : UInt8} (h₀ : 0xE0 ≤ w) (h₁ : w < 0xF0) :
    verify₃ w x y = true ↔ (0x80 ≤ x ∧ x < 0xC0) ∧ (0x80 ≤ y ∧ y < 0xC0) ∧
      (w = 0xE0 → 0xA0 ≤ x) ∧ (w = 0xED → x < 0xA0) := by
  have := toNat_assemble₃Unchecked w x y
  have := w.toNat_lt
  have := x.toNat_lt
  have := y.toNat_lt
  simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at h₀ h₁
  simp [verify₃, isUTF8ContinuationByte_eq, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt,
    UInt32.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, ← UInt8.toNat_inj, *]
  omega

theorem verify₄_iff {w x y z : UInt8} (h₀ : 0xF0 ≤ w) (h₁ : w < 0xF8) :
    verify₄ w x y z = true ↔ w < 0xF5 ∧ (0x80 ≤ x ∧ x < 0xC0) ∧ (0x80 ≤ y ∧ y < 0xC0) ∧
      (0x80 ≤ z ∧ z < 0xC0) ∧ (w = 0xF0 → 0x90 ≤ x) ∧ (w = 0xF4 → x < 0x90) := by
  have := toNat_assemble₄Unchecked w x y z
  have := w.toNat_lt
  have := x.toNat_lt
  have := y.toNat_lt
  have := z.toNat_lt
  simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, UInt8.reduceToNat] at h₀ h₁
  simp [verify₄, isUTF8ContinuationByte_eq, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt,
    UInt32.le_iff_toNat_le, ← UInt8.toNat_inj, *]
  omega

end Verified.Shim
