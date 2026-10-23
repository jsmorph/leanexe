import Library.Hashing.Sha512.Program
import Library.Hashing.Words.Proof
import Library.Hashing.Sha2.Equiv.SHA512.Padding.Layout

/-! `paddedWord` reads the words of the padded message: for a message of fewer than `2 ^ 61` bytes,
word `16 j + t` is word `t` of block `j` of `implPaddedBlocks`, the padding of FIPS 180-4 §5.1.2
in the copied implementation, which `implPaddedBlocks_lift_eq_parsePad` proves equal to the
specification's padding and parsing.  A word holds message bytes, the byte `0x80` after the last
message byte, zero bytes, or the two words of the bit length; `paddedWord_eq` treats each case. -/

namespace Library.Hashing.Sha512

open Library.Hashing.Words
open SHS.Equiv.SHA512.Padding.Layout

/-- The number of padded blocks of a message of `n` bytes. -/
def blockCount (n : Nat) : Nat := n / 128 + if n % 128 < 112 then 1 else 2

theorem bytes_size (msg : Array UInt64) (n : Nat) : (bytes msg n).size = n := by
  simp [bytes, ByteArray.size]

theorem bytes_get! (msg : Array UInt64) (n p : Nat) (hp : p < n) :
    (bytes msg n).get! p = byteAt msg p := by
  simp [bytes, ByteArray.get!, hp]

theorem paddedSize (msg : Array UInt64) (n : Nat) :
    (implPaddedBytes (bytes msg n)).size = 128 * blockCount n := by
  rw [size_implPaddedBytes_eq, bytes_size]
  unfold zerosCount blockCount
  rw [bytes_size]
  have hd : n = 128 * (n / 128) + n % 128 := (Nat.div_add_mod n 128).symm
  have hr : n % 128 < 128 := Nat.mod_lt _ (by decide)
  by_cases h : n % 128 < 112 <;> simp only [h, if_true, if_false] <;> omega

/-- The bit length starts `16` bytes before the end of the padded message. -/
theorem lengthStart (msg : Array UInt64) (n : Nat) :
    n + 1 + zerosCount (bytes msg n) = 8 * (16 * blockCount n - 2) := by
  unfold zerosCount blockCount
  rw [bytes_size]
  have hd : n = 128 * (n / 128) + n % 128 := (Nat.div_add_mod n 128).symm
  have hr : n % 128 < 128 := Nat.mod_lt _ (by decide)
  by_cases h : n % 128 < 112 <;> simp only [h, if_true, if_false] <;> omega

/-- The big-endian word of the padded bytes `8 i` to `8 i + 7`. -/
def paddedBE (data : ByteArray) (i : Nat) : UInt64 :=
  be8 ((implPaddedBytes data).get! (8 * i + 0)) ((implPaddedBytes data).get! (8 * i + 1))
    ((implPaddedBytes data).get! (8 * i + 2)) ((implPaddedBytes data).get! (8 * i + 3))
    ((implPaddedBytes data).get! (8 * i + 4)) ((implPaddedBytes data).get! (8 * i + 5))
    ((implPaddedBytes data).get! (8 * i + 6)) ((implPaddedBytes data).get! (8 * i + 7))

/-- Word `t` of block `j` is padded word `16 j + t`. -/
theorem beU64_paddedBlock (data : ByteArray) (j : Nat) (t : Fin 16) :
    SHS.SHA512.Impl.beU64 (paddedBlock data j) t = paddedBE data (16 * j + t.val) := by
  have h0 : j * 128 + 8 * t.val = 8 * (16 * j + t.val) + 0 := by omega
  have h : ∀ k, j * 128 + (8 * t.val + k) = 8 * (16 * j + t.val) + k := fun k => by omega
  simp only [SHS.SHA512.Impl.beU64, paddedBlock, Vector.getElem_ofFn, paddedBE, be8, h0, h]

/-- A padded word whose eight bytes are given. -/
theorem paddedBE_eq (data : ByteArray) (i : Nat) (f : Nat → UInt8)
    (hk : ∀ k, k < 8 → (implPaddedBytes data).get! (8 * i + k) = f k) :
    paddedBE data i = be8 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) := by
  unfold paddedBE
  rw [hk 0 (by decide), hk 1 (by decide), hk 2 (by decide), hk 3 (by decide), hk 4 (by decide),
    hk 5 (by decide), hk 6 (by decide), hk 7 (by decide)]

/-- The padded byte at `p` of a message of `n` bytes. -/
theorem paddedByte (msg : Array UInt64) (n p : Nat) (hp : p < 128 * blockCount n) :
    (implPaddedBytes (bytes msg n)).get! p =
      if p < n then byteAt msg p
      else if p = n then 0x80
      else if p < 8 * (16 * blockCount n - 2) then 0
      else (lengthBE128 (n.toUInt64 <<< 3)).get! (p - 8 * (16 * blockCount n - 2)) := by
  rw [get!_implPaddedBytes_eq _ _ (by rw [paddedSize]; exact hp), bytes_size, lengthStart]
  by_cases h : p < n
  · rw [if_pos h, if_pos h, bytes_get! _ _ _ h]
  · rw [if_neg h, if_neg h]

theorem be8_zero : be8 0 0 0 0 0 0 0 0 = 0 := by decide

/-- The bytes of the word that holds the last message bytes and `0x80`. -/
theorem markedByte (msg : Array UInt64) (n k : Nat) (hk : k < 8)
    (hp : 8 * (n / 8) + 7 < 8 * (16 * blockCount n - 2)) :
    (implPaddedBytes (bytes msg n)).get! (8 * (n / 8) + k) =
      if k < n % 8 then byteOf msg[n / 8]! k else if k = n % 8 then 0x80 else 0 := by
  have hn : n = 8 * (n / 8) + n % 8 := (Nat.div_add_mod n 8).symm
  rw [paddedByte _ _ _ (by omega)]
  by_cases h1 : k < n % 8
  · rw [if_pos (by omega), if_pos h1, byteAt_eq _ _ _ hk]
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : k = n % 8
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2, if_pos (by omega)]

theorem shift_eq (n : UInt64) : (n &&& 7) <<< 3 = (8 * (n.toNat % 8)).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  have : n.toNat % 2 ^ 3 < 8 := Nat.mod_lt _ (by decide)
  simp [Nat.shiftLeft_eq]
  omega

/-- Word `i` of the padded message of the `n < 2 ^ 61` bytes of `msg`, for `i` below the number of
padded words, is the big-endian word of its eight padded bytes. -/
theorem paddedWord_eq (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) (i : Nat)
    (hi : i < 16 * blockCount n.toNat) :
    paddedWord msg n (UInt64.ofNat (16 * blockCount n.toNat - 1)) (UInt64.ofNat i) =
      paddedBE (bytes msg n.toNat) i := by
  set N := blockCount n.toNat with hN
  have hN1 : 1 ≤ N := by simp only [hN, blockCount]; split <;> omega
  have hN2 : N ≤ n.toNat / 128 + 2 := by simp only [hN, blockCount]; split <;> omega
  have hL : n.toNat + 1 ≤ 8 * (16 * N - 2) := by
    have := lengthStart msg n.toNat
    rw [← hN] at this
    omega
  have hiN : (UInt64.ofNat i).toNat = i := by rw [UInt64.toNat_ofNat']; omega
  have hlast : (UInt64.ofNat (16 * N - 1)).toNat = 16 * N - 1 := by
    rw [UInt64.toNat_ofNat']; omega
  have hq : (n >>> 3).toNat = n.toNat / 8 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  unfold paddedWord
  by_cases h1 : i = 16 * N - 1
  · -- The low word of the bit length.
    have hb : (UInt64.ofNat i == UInt64.ofNat (16 * N - 1)) = true := by
      rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hiN, hlast, h1]
    rw [if_pos hb, paddedBE_eq _ _
      (fun k => ((n.toNat.toUInt64 <<< 3 >>> (((7 - k) * 8 : Nat).toUInt64)) &&& 0xff).toUInt8)
      (fun k hk => by
        rw [paddedByte _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          lengthBE128_get!_eq _ _ (by omega) (by omega),
          show 15 - (8 * i + k - 8 * (16 * N - 2)) = 7 - k by omega])]
    rw [show n.toNat.toUInt64 = n from UInt64.ofNat_toNat]
    exact (be8_bytes (n <<< 3)).symm
  · have hb : (UInt64.ofNat i == UInt64.ofNat (16 * N - 1)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h1
      have := congrArg UInt64.toNat h; rw [hiN, hlast] at this; exact this
    rw [if_neg (by rw [hb]; decide)]
    by_cases h2 : i = 16 * N - 2
    · -- The high word of the bit length, zero below `2 ^ 61` bytes.
      have hb2 : (UInt64.ofNat i + 1 == UInt64.ofNat (16 * N - 1)) = true := by
        rw [beq_iff_eq]; apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, hiN, hlast, h2]; simp; omega
      rw [if_pos hb2, paddedBE_eq _ _ (fun _ => 0) (fun k hk => by
        rw [paddedByte _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          lengthBE128_get!_zero _ _ (by omega)]), be8_zero]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_shiftRight]
      simp [Nat.shiftRight_eq_div_pow]
      omega
    · have hb2 : (UInt64.ofNat i + 1 == UInt64.ofNat (16 * N - 1)) = false := by
        rw [beq_eq_false_iff_ne]; intro h; apply h2
        have := congrArg UInt64.toNat h
        rw [UInt64.toNat_add, hiN, hlast] at this; simp at this; omega
      rw [if_neg (by rw [hb2]; decide)]
      simp only
      by_cases h3 : i < n.toNat / 8
      · -- A word of message bytes.
        rw [if_pos (by rw [UInt64.lt_iff_toNat_lt, hiN, hq]; exact h3), UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega), bswap_eq, paddedBE_eq _ _ (byteOf msg[i]!) (fun k hk => by
            rw [paddedByte _ _ _ (by omega), if_pos (by omega), byteAt_eq _ _ _ hk])]
      · rw [if_neg (by rw [UInt64.lt_iff_toNat_lt, hiN, hq]; exact h3)]
        by_cases h4 : i = n.toNat / 8
        · -- The word of the last message bytes and `0x80`.
          have hb4 : (UInt64.ofNat i == n >>> 3) = true := by
            rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hiN, hq, h4]
          rw [if_pos hb4, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), shift_eq, bswap_eq,
            paddedBE_eq _ _ (fun k => if k < n.toNat % 8 then byteOf msg[i]! k
              else if k = n.toNat % 8 then 0x80 else 0) (fun k hk => by
                rw [h4, markedByte _ _ _ hk (by omega)])]
          simp only [byteOf_marked _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)) (by decide : 0 < 8),
            byteOf_marked _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)) (by decide : 1 < 8),
            byteOf_marked _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)) (by decide : 2 < 8),
            byteOf_marked _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)) (by decide : 3 < 8),
            byteOf_marked _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)) (by decide : 4 < 8),
            byteOf_marked _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)) (by decide : 5 < 8),
            byteOf_marked _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)) (by decide : 6 < 8),
            byteOf_marked _ _ _ (Nat.mod_lt _ (by decide : 8 > 0)) (by decide : 7 < 8)]
        · -- A word of zero bytes.
          have hb4 : (UInt64.ofNat i == n >>> 3) = false := by
            rw [beq_eq_false_iff_ne]; intro h; apply h4
            have := congrArg UInt64.toNat h; rw [hiN, hq] at this; exact this
          rw [if_neg (by rw [hb4]; decide), paddedBE_eq _ _ (fun _ => 0) (fun k hk => by
            rw [paddedByte _ _ _ (by omega), if_neg (by omega), if_neg (by omega),
              if_pos (by omega)]), be8_zero]

end Library.Hashing.Sha512
