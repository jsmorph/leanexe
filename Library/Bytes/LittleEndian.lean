import Library.Bytes.Packed
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Little-endian values of byte strings.  The value of the bytes `b_0` to `b_(k-1)` is
`b_0 + 256 b_1 + … + 256^(k-1) b_(k-1)`, which `List.foldr (fun b acc => b.toNat + 256 * acc) 0`
computes, as the transcriptions of SipHash and XXH64 write it.  `foldr_byteOf` reads the eight
bytes of a word as the word, and `chunk_eq` writes a run of bytes of a list by position. -/

namespace Library.Bytes

/-- The value of the little-endian bytes `bs` with `256 ^ |bs| * init` added. -/
theorem foldr_le (bs : List UInt8) (init : Nat) :
    bs.foldr (fun b acc => b.toNat + 256 * acc) init =
      bs.foldr (fun b acc => b.toNat + 256 * acc) 0 + 256 ^ bs.length * init := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldr_cons, ih, List.length_cons, pow_succ]
    ring

/-- The little-endian value of the bytes `g 0` to `g (k - 1)`. -/
theorem foldr_range (g : Nat → UInt8) (k : Nat) :
    ((List.range k).map g).foldr (fun b acc => b.toNat + 256 * acc) 0 =
      ∑ j ∈ Finset.range k, (g j).toNat * 256 ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldr_append, foldr_le, ih, Finset.sum_range_succ]
    simp [mul_comm]

/-- The digits of `v` in base 256 below position `k` give `v % 256 ^ k`. -/
theorem sum_digits (v k : Nat) :
    ∑ j ∈ Finset.range k, (v / 256 ^ j % 256) * 256 ^ j = v % 256 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, mul_comm]

theorem byteOf_toNat (w : UInt64) {k : Nat} (hk : k < 8) :
    (byteOf w k).toNat = w.toNat / 256 ^ k % 256 := by
  have h8 : (8 * k).toUInt64.toNat = 8 * k :=
    UInt64.toNat_ofNat_of_lt' (lt_of_lt_of_le (show 8 * k < 64 by omega) (by decide))
  rw [byteOf, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8,
    Nat.mod_eq_of_lt (show 8 * k < 64 by omega), Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ (8 * k) = 256 ^ k by rw [pow_mul]; norm_num]

/-- The little-endian value of the eight bytes of `w` is `w`. -/
theorem foldr_byteOf (w : UInt64) :
    ((List.range 8).map (byteOf w)).foldr (fun b acc => b.toNat + 256 * acc) 0 = w.toNat := by
  rw [foldr_range]
  have : ∀ j ∈ Finset.range 8,
      (byteOf w j).toNat * 256 ^ j = (w.toNat / 256 ^ j % 256) * 256 ^ j :=
    fun j hj => by rw [byteOf_toNat w (Finset.mem_range.mp hj)]
  rw [Finset.sum_congr rfl this, sum_digits, Nat.mod_eq_of_lt (by simpa using w.toNat_lt)]

/-- The `k` bytes of `p` from position `i`, for `p` of length at least `i + k`. -/
theorem chunk_eq (p : List UInt8) (i k : Nat) (h : i + k ≤ p.length) :
    (p.drop i).take k = (List.range k).map fun j => p.getD (i + j) 0 := by
  apply List.ext_getElem (by simp; omega)
  intro j h1 h2
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp at h2; omega)]
  rfl

end Library.Bytes
