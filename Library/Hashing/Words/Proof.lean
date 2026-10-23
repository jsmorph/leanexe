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

/-- Word `k` of sixteen words. -/
def Words16.get (m : Words16) (k : Nat) : UInt64 :=
  #[m.w0, m.w1, m.w2, m.w3, m.w4, m.w5, m.w6, m.w7, m.w8, m.w9, m.w10, m.w11, m.w12, m.w13, m.w14,
    m.w15][k]!

@[simp] theorem get0 (m : Words16) : m.get 0 = m.w0 := rfl
@[simp] theorem get1 (m : Words16) : m.get 1 = m.w1 := rfl
@[simp] theorem get9 (m : Words16) : m.get 9 = m.w9 := rfl
@[simp] theorem get14 (m : Words16) : m.get 14 = m.w14 := rfl
@[simp] theorem get15 (m : Words16) : m.get 15 = m.w15 := rfl

theorem bytes_size (msg : Array UInt64) (n : Nat) : (bytes msg n).size = n := by
  simp [bytes, ByteArray.size]

theorem bytes_get! (msg : Array UInt64) (n p : Nat) (hp : p < n) :
    (bytes msg n).get! p = byteAt msg p := by
  simp [bytes, ByteArray.get!, hp]

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
/-- The bytes of the word that keeps the first `r` bytes of `w` and clears the others. -/
theorem byteOf_masked (w : UInt64) (r k : Nat) (hr : r < 8) (hk : k < 8) :
    byteOf (w &&& (((1 : UInt64) <<< (8 * r).toUInt64) - 1)) k =
      if k < r then byteOf w k else 0 := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  interval_cases r <;> interval_cases k <;>
    simp [byteOf, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft,
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

/-- `Fin.foldl` over the indices below `n` as `Nat.fold`. -/
theorem finFoldl_eq_fold {β : Type} (n : Nat) (g : Nat → β → β) (init : β) :
    Fin.foldl n (fun x (i : Fin n) => g i.val x) init = Nat.fold n (fun i _ x => g i x) init := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, Nat.fold_succ]
    exact congrArg (g n) ih

theorem base_add (i k : Nat) (h : 16 * i + k < 2 ^ 64) :
    (UInt64.ofNat i <<< 4) + UInt64.ofNat k = UInt64.ofNat (16 * i + k) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    UInt64.toNat_ofNat', show UInt64.toNat 4 % 64 = 4 by decide, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : i * 2 ^ 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 16 * i + k < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : i * 2 ^ 4 + k < 2 ^ 64)]
  omega

end Library.Hashing.Words
