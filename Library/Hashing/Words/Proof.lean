import Library.Hashing.Words.Bytes
import Mathlib.Tactic.IntervalCases

/-! Byte-level facts about `bswap` and the words the hash functions assemble.  `be8` assembles eight
bytes into a word with the first byte most significant, the order of FIPS 180-4 §3.1, and
`byteOf w k` is byte `k` of `w` counting from the least significant. -/

namespace Library.Hashing.Words

/-- Eight bytes as a word, `b0` most significant. -/
def be8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  (b0.toUInt64 <<< 56) ||| (b1.toUInt64 <<< 48) ||| (b2.toUInt64 <<< 40) |||
    (b3.toUInt64 <<< 32) ||| (b4.toUInt64 <<< 24) ||| (b5.toUInt64 <<< 16) |||
    (b6.toUInt64 <<< 8) ||| b7.toUInt64

/-- Byte `k` of `w`, counting from the least significant. -/
def byteOf (w : UInt64) (k : Nat) : UInt8 := (w >>> (8 * k).toUInt64).toUInt8

theorem byteAt_eq (ws : Array UInt64) (i k : Nat) (hk : k < 8) :
    byteAt ws (8 * i + k) = byteOf ws[i]! k := by
  unfold byteAt byteOf
  rw [show (8 * i + k) / 8 = i by omega, show (8 * i + k) % 8 = k by omega]

set_option maxHeartbeats 800000 in
/-- `bswap` reverses the bytes of a word. -/
theorem bswap_eq (w : UInt64) :
    bswap w = be8 (byteOf w 0) (byteOf w 1) (byteOf w 2) (byteOf w 3) (byteOf w 4)
      (byteOf w 5) (byteOf w 6) (byteOf w 7) := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [bswap, be8, byteOf, UInt64.toBitVec_or, UInt64.toBitVec_and,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64,
    UInt64.toBitVec_toUInt8]
  interval_cases i <;> simp

set_option maxHeartbeats 800000 in
/-- Assembling the bytes of `x`, most significant first, gives `x`. -/
theorem be8_bytes (x : UInt64) :
    be8 ((x >>> 56) &&& 0xff).toUInt8 ((x >>> 48) &&& 0xff).toUInt8
      ((x >>> 40) &&& 0xff).toUInt8 ((x >>> 32) &&& 0xff).toUInt8
      ((x >>> 24) &&& 0xff).toUInt8 ((x >>> 16) &&& 0xff).toUInt8
      ((x >>> 8) &&& 0xff).toUInt8 ((x >>> 0) &&& 0xff).toUInt8 = x := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be8, UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]
  interval_cases i <;> simp

set_option maxHeartbeats 1600000 in
/-- The bytes of the word that keeps the first `r` bytes of `w` and puts `0x80` after them. -/
theorem byteOf_marked (w : UInt64) (r k : Nat) (hr : r < 8) (hk : k < 8) :
    byteOf ((w &&& (((1 : UInt64) <<< (8 * r).toUInt64) - 1)) |||
        ((0x80 : UInt64) <<< (8 * r).toUInt64)) k =
      if k < r then byteOf w k else if k = r then 0x80 else 0 := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases r <;> interval_cases k <;>
    simp [byteOf, UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft,
      UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt8] <;>
    interval_cases i <;> simp

set_option maxHeartbeats 1600000 in
/-- Byte `k` of an assembled word is byte `7 - k` of the list. -/
theorem byteOf_be8 (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (k : Nat) (hk : k < 8) :
    byteOf (be8 b0 b1 b2 b3 b4 b5 b6 b7) k = [b7, b6, b5, b4, b3, b2, b1, b0][k]! := by
  interval_cases k <;>
    (apply UInt8.toBitVec_inj.mp
     apply BitVec.eq_of_getLsbD_eq
     intro i hi
     simp [be8, byteOf, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
       UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8] <;>
       interval_cases i <;> simp)

/-- Byte `k` of `bswap x` is byte `7 - k` of `x`. -/
theorem byteOf_bswap (x : UInt64) (k : Nat) (hk : k < 8) :
    byteOf (bswap x) k = byteOf x (7 - k) := by
  rw [bswap_eq, byteOf_be8 _ _ _ _ _ _ _ _ _ hk]
  interval_cases k <;> rfl

set_option maxHeartbeats 800000 in
/-- `byteOf` in the form that `SHS.SHA512.Impl` uses to extract a digest byte. -/
theorem byteOf_eq (x : UInt64) (j : Nat) :
    byteOf x j = ((x >>> UInt64.ofNat (j * 8)) &&& 0xff).toUInt8 := by
  rw [show UInt64.ofNat (j * 8) = (8 * j).toUInt64 by rw [Nat.mul_comm]]
  unfold byteOf
  generalize x >>> (8 * j).toUInt64 = y
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [UInt64.toBitVec_toUInt8]
  interval_cases i <;> simp

set_option maxHeartbeats 800000 in
/-- The low four bytes of a word are unchanged by clearing its high four bytes. -/
theorem byteOf_low (x : UInt64) (k : Nat) (hk : k < 4) :
    byteOf (x &&& 0xFFFFFFFF) k = byteOf x k := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases k <;>
    simp [byteOf, UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, UInt64.toBitVec_toUInt8] <;>
    interval_cases i <;> simp

end Library.Hashing.Words
