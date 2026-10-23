import Library.Hashing.Sha256.Program
import Library.Hashing.Words.Proof
import Library.Hashing.Sha2.Impl.SHA256

/-! The 32-bit words of `Library.Hashing.Sha256` are the low 32 bits of `UInt64` values, read by
`UInt64.toUInt32`.  Truncation commutes with addition and the bitwise operations, and the
helpers that shift right clear the high bits first, so each helper's truncation is the
corresponding 32-bit operation of `SHS.SHA256.Impl`.  `be4` assembles four bytes into a 32-bit
word with the first byte most significant, as `SHS.SHA256.Impl.beU32` does. -/

namespace Library.Hashing.Sha256

open Library.Hashing.Words

theorem low32_toUInt32 (x : UInt64) : (low32 x).toUInt32 = x.toUInt32 := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [low32, UInt64.toBitVec_toUInt32]
  interval_cases i <;> simp

theorem xor_ones_toUInt32 (x : UInt64) : (x ^^^ 0xFFFFFFFFFFFFFFFF).toUInt32 = ~~~ x.toUInt32 := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [UInt64.toBitVec_toUInt32]
  interval_cases i <;> simp

/-- A right shift of the low 32 bits is the 32-bit right shift. -/
theorem shr_toUInt32 (x r : UInt64) (h : r.toNat < 32) :
    (low32 x >>> r).toUInt32 = x.toUInt32 >>> r.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [low32, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt32.toNat_shiftRight,
    UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have hr : r.toNat % 64 = r.toNat := Nat.mod_eq_of_lt (by omega)
  have hr' : r.toNat % 2 ^ 32 % 32 = r.toNat := by
    rw [Nat.mod_eq_of_lt (by omega : r.toNat < 2 ^ 32), Nat.mod_eq_of_lt h]
  rw [hr, hr']
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide)))

/-- `rot` of the low 32 bits is the 32-bit rotation `SHS.SHA256.Impl.UInt32.rotr`. -/
theorem rot_toUInt32 (x r : UInt64) (h0 : 0 < r.toNat) (h : r.toNat < 32) :
    (rot (low32 x) r).toUInt32 = SHS.SHA256.Impl.UInt32.rotr x.toUInt32 r.toUInt32 := by
  have hsub : (32 - r).toNat = 32 - r.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; show r.toNat ≤ 32; omega)]
    rfl
  unfold rot SHS.SHA256.Impl.UInt32.rotr
  rw [UInt64.toUInt32_or, shr_toUInt32 x r h,
    UInt64.toUInt32_shiftLeft _ _ (by rw [UInt64.lt_iff_toNat_lt, hsub]; show 32 - r.toNat < 32; omega),
    low32_toUInt32]
  congr 2
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, hsub, UInt32.toNat_sub_of_le _ _
    (by rw [UInt32.le_iff_toNat_le, UInt64.toNat_toUInt32]; show r.toNat % 2 ^ 32 ≤ 32; omega),
    UInt64.toNat_toUInt32]
  rw [Nat.mod_eq_of_lt (by omega : 32 - r.toNat < 2 ^ 32), Nat.mod_eq_of_lt (by omega : r.toNat < 2 ^ 32)]
  rfl

theorem ch_toUInt32 (x y z : UInt64) :
    (ch x y z).toUInt32 = (x.toUInt32 &&& y.toUInt32) ^^^ ((~~~ x.toUInt32) &&& z.toUInt32) := by
  unfold ch
  rw [UInt64.toUInt32_xor, UInt64.toUInt32_and, UInt64.toUInt32_and, xor_ones_toUInt32]

theorem maj_toUInt32 (x y z : UInt64) :
    (maj x y z).toUInt32 =
      (x.toUInt32 &&& y.toUInt32) ^^^ (x.toUInt32 &&& z.toUInt32) ^^^ (y.toUInt32 &&& z.toUInt32) := by
  simp only [maj, UInt64.toUInt32_xor, UInt64.toUInt32_and]

open SHS.SHA256.Impl in
theorem bigSigma0_toUInt32 (x : UInt64) :
    (bigSigma0 x).toUInt32 =
      UInt32.rotr x.toUInt32 2 ^^^ UInt32.rotr x.toUInt32 13 ^^^ UInt32.rotr x.toUInt32 22 := by
  simp only [bigSigma0, UInt64.toUInt32_xor, rot_toUInt32 x 2 (by decide) (by decide),
    rot_toUInt32 x 13 (by decide) (by decide), rot_toUInt32 x 22 (by decide) (by decide)]
  rfl

open SHS.SHA256.Impl in
theorem bigSigma1_toUInt32 (x : UInt64) :
    (bigSigma1 x).toUInt32 =
      UInt32.rotr x.toUInt32 6 ^^^ UInt32.rotr x.toUInt32 11 ^^^ UInt32.rotr x.toUInt32 25 := by
  simp only [bigSigma1, UInt64.toUInt32_xor, rot_toUInt32 x 6 (by decide) (by decide),
    rot_toUInt32 x 11 (by decide) (by decide), rot_toUInt32 x 25 (by decide) (by decide)]
  rfl

open SHS.SHA256.Impl in
theorem smallSigma0_toUInt32 (x : UInt64) :
    (smallSigma0 x).toUInt32 =
      UInt32.rotr x.toUInt32 7 ^^^ UInt32.rotr x.toUInt32 18 ^^^ (x.toUInt32 >>> 3) := by
  simp only [smallSigma0, UInt64.toUInt32_xor, rot_toUInt32 x 7 (by decide) (by decide),
    rot_toUInt32 x 18 (by decide) (by decide), shr_toUInt32 x 3 (by decide)]
  rfl

open SHS.SHA256.Impl in
theorem smallSigma1_toUInt32 (x : UInt64) :
    (smallSigma1 x).toUInt32 =
      UInt32.rotr x.toUInt32 17 ^^^ UInt32.rotr x.toUInt32 19 ^^^ (x.toUInt32 >>> 10) := by
  simp only [smallSigma1, UInt64.toUInt32_xor, rot_toUInt32 x 17 (by decide) (by decide),
    rot_toUInt32 x 19 (by decide) (by decide), shr_toUInt32 x 10 (by decide)]
  rfl

/-- Four bytes as a 32-bit word, `b0` most significant. -/
def be4 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

set_option maxHeartbeats 800000 in
/-- The high half of `bswap w` holds bytes 0 to 3 of `w`, the first most significant. -/
theorem bswap_high (w : UInt64) :
    (bswap w >>> 32).toUInt32 = be4 (byteOf w 0) (byteOf w 1) (byteOf w 2) (byteOf w 3) := by
  rw [bswap_eq]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be4, be8, byteOf, UInt64.toBitVec_toUInt32, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64,
    UInt64.toBitVec_toUInt8]
  interval_cases i <;> simp

set_option maxHeartbeats 800000 in
/-- The low half of `bswap w` holds bytes 4 to 7 of `w`, the first most significant. -/
theorem bswap_low (w : UInt64) :
    (low32 (bswap w)).toUInt32 = be4 (byteOf w 4) (byteOf w 5) (byteOf w 6) (byteOf w 7) := by
  rw [low32_toUInt32, bswap_eq]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be4, be8, byteOf, UInt64.toBitVec_toUInt32, UInt32.toBitVec_or,
    UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64,
    UInt64.toBitVec_toUInt8]
  interval_cases i <;> simp

set_option maxHeartbeats 800000 in
/-- Assembling the low four bytes of `x`, most significant first, gives its low 32 bits. -/
theorem be4_low (x : UInt64) :
    be4 ((x >>> 24) &&& 0xff).toUInt8 ((x >>> 16) &&& 0xff).toUInt8
      ((x >>> 8) &&& 0xff).toUInt8 ((x >>> 0) &&& 0xff).toUInt8 = x.toUInt32 := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be4, UInt64.toBitVec_toUInt32, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt32, UInt64.toBitVec_and, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_toUInt8]
  interval_cases i <;> simp

set_option maxHeartbeats 800000 in
/-- Assembling the high four bytes of `x`, most significant first, gives its high 32 bits. -/
theorem be4_high (x : UInt64) :
    be4 ((x >>> 56) &&& 0xff).toUInt8 ((x >>> 48) &&& 0xff).toUInt8
      ((x >>> 40) &&& 0xff).toUInt8 ((x >>> 32) &&& 0xff).toUInt8 = (x >>> 32).toUInt32 := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be4, UInt64.toBitVec_toUInt32, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt32, UInt64.toBitVec_and, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_toUInt8]
  interval_cases i <;> simp

/-- Byte `j` of the 32-bit word `x`, counting from the least significant. -/
def byte32 (x : UInt32) (j : Nat) : UInt8 := (x >>> (8 * j).toUInt32).toUInt8

set_option maxHeartbeats 800000 in
/-- `byte32` in the form that `SHS.SHA256.Impl` uses to extract a digest byte. -/
theorem byte32_eq (x : UInt32) (j : Nat) :
    byte32 x j = ((x >>> UInt32.ofNat (j * 8)) &&& 0xff).toUInt8 := by
  rw [show UInt32.ofNat (j * 8) = (8 * j).toUInt32 by rw [Nat.mul_comm]]
  unfold byte32
  generalize x >>> (8 * j).toUInt32 = y
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [UInt32.toBitVec_toUInt8]
  interval_cases i <;> simp

set_option maxHeartbeats 1600000 in
/-- Bytes 0 to 3 of `pair x y` are those of the 32-bit word of `x`, most significant first. -/
theorem byteOf_pair_low (x y : UInt64) (k : Nat) (hk : k < 4) :
    byteOf (pair x y) k = byte32 x.toUInt32 (3 - k) := by
  unfold pair
  rw [bswap_eq, bswap_eq]
  interval_cases k <;>
    (apply UInt8.toBitVec_inj.mp
     apply BitVec.eq_of_getLsbD_eq
     intro i hi
     simp only [be8, byteOf, byte32, UInt64.toBitVec_or, UInt64.toBitVec_and,
       UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64,
       UInt64.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, UInt32.toBitVec_toUInt8,
       UInt64.toBitVec_toUInt32]
     interval_cases i <;> simp)

set_option maxHeartbeats 1600000 in
/-- Bytes 4 to 7 of `pair x y` are those of the 32-bit word of `y`, most significant first. -/
theorem byteOf_pair_high (x y : UInt64) (k : Nat) (hk1 : 4 ≤ k) (hk : k < 8) :
    byteOf (pair x y) k = byte32 y.toUInt32 (7 - k) := by
  unfold pair
  rw [bswap_eq, bswap_eq]
  interval_cases k <;>
    (apply UInt8.toBitVec_inj.mp
     apply BitVec.eq_of_getLsbD_eq
     intro i hi
     simp only [be8, byteOf, byte32, UInt64.toBitVec_or, UInt64.toBitVec_and,
       UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64,
       UInt64.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, UInt32.toBitVec_toUInt8,
       UInt64.toBitVec_toUInt32]
     interval_cases i <;> simp)

set_option maxHeartbeats 800000 in
/-- The bytes of `bswap x >>> 32` are those of the 32-bit word of `x`, most significant first. -/
theorem byteOf_high (x : UInt64) (k : Nat) (hk : k < 4) :
    byteOf (bswap x >>> 32) k = byte32 x.toUInt32 (3 - k) := by
  rw [bswap_eq]
  interval_cases k <;>
    (apply UInt8.toBitVec_inj.mp
     apply BitVec.eq_of_getLsbD_eq
     intro i hi
     simp only [be8, byteOf, byte32, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
       UInt64.toBitVec_shiftRight, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8,
       UInt32.toBitVec_shiftRight, UInt32.toBitVec_toUInt8, UInt64.toBitVec_toUInt32]
     interval_cases i <;> simp)

end Library.Hashing.Sha256
