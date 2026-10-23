import Library.Hashing.Sha256.WordProof
import Library.Hashing.Sha2.Equiv.SHA256.Padding.Layout

/-! `paddedWord` reads the 32-bit words of the padded message: for a message of fewer than `2 ^ 61`
bytes, the 32-bit word of word `16 j + t` is word `t` of block `j` of `implPaddedBlocks`, the
padding of FIPS 180-4 §5.1.1 in the copied implementation, which `implPaddedBlocks_lift_eq_parsePad`
proves equal to the specification's padding and parsing.  A word holds message bytes, the byte
`0x80` after the last message byte, zero bytes, or one of the two halves of the bit length;
`paddedWord_eq` treats each case. -/

namespace Library.Hashing.Sha256

open Library.Hashing.Words
open SHS.Equiv.SHA256.Padding.Layout

/-- The number of padded blocks of a message of `n` bytes. -/
def blockCount (n : Nat) : Nat := n / 64 + if n % 64 < 56 then 1 else 2

theorem paddedSize (msg : Array UInt64) (n : Nat) :
    (implPaddedBytes (bytes msg n)).size = 64 * blockCount n := by
  rw [size_implPaddedBytes_eq, bytes_size]
  unfold zerosCount blockCount
  rw [bytes_size]
  have hd : n = 64 * (n / 64) + n % 64 := (Nat.div_add_mod n 64).symm
  have hr : n % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases h : n % 64 < 56 <;> simp only [h, ite_true, ite_false] <;> omega

/-- The bit length starts eight bytes before the end of the padded message. -/
theorem lengthStart (msg : Array UInt64) (n : Nat) :
    n + 1 + zerosCount (bytes msg n) = 4 * (16 * blockCount n - 2) := by
  unfold zerosCount blockCount
  rw [bytes_size]
  have hd : n = 64 * (n / 64) + n % 64 := (Nat.div_add_mod n 64).symm
  have hr : n % 64 < 64 := Nat.mod_lt _ (by decide)
  by_cases h : n % 64 < 56 <;> simp only [h, ite_true, ite_false] <;> omega

/-- The big-endian 32-bit word of the padded bytes `4 i` to `4 i + 3`. -/
def paddedBE (data : ByteArray) (i : Nat) : UInt32 :=
  be4 ((implPaddedBytes data).get! (4 * i + 0)) ((implPaddedBytes data).get! (4 * i + 1))
    ((implPaddedBytes data).get! (4 * i + 2)) ((implPaddedBytes data).get! (4 * i + 3))

/-- Word `t` of block `j` is padded word `16 j + t`. -/
theorem beU32_paddedBlock (data : ByteArray) (j : Nat) (t : Fin 16) :
    SHS.SHA256.Impl.beU32 (paddedBlock data j) t = paddedBE data (16 * j + t.val) := by
  have h0 : j * 64 + 4 * t.val = 4 * (16 * j + t.val) + 0 := by omega
  have h : ∀ k, j * 64 + (4 * t.val + k) = 4 * (16 * j + t.val) + k := fun k => by omega
  simp only [SHS.SHA256.Impl.beU32, paddedBlock, Vector.getElem_ofFn, paddedBE, be4, h0, h]

/-- A padded word whose four bytes are given. -/
theorem paddedBE_eq (data : ByteArray) (i : Nat) (f : Nat → UInt8)
    (hk : ∀ k, k < 4 → (implPaddedBytes data).get! (4 * i + k) = f k) :
    paddedBE data i = be4 (f 0) (f 1) (f 2) (f 3) := by
  unfold paddedBE
  rw [hk 0 (by decide), hk 1 (by decide), hk 2 (by decide), hk 3 (by decide)]

/-- The padded byte at `p` of a message of `n` bytes. -/
theorem paddedByte (msg : Array UInt64) (n p : Nat) (hp : p < 64 * blockCount n) :
    (implPaddedBytes (bytes msg n)).get! p =
      if p < n then byteAt msg p
      else if p = n then 0x80
      else if p < 4 * (16 * blockCount n - 2) then 0
      else (lengthBE64 (n.toUInt64 <<< 3)).get! (p - 4 * (16 * blockCount n - 2)) := by
  rw [get!_implPaddedBytes_eq _ _ (by rw [paddedSize]; exact hp), bytes_size, lengthStart]
  by_cases h : p < n
  · rw [ite_eq_left h, ite_eq_left h, bytes_get! _ _ _ h]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Byte `4 i + k` of a message is byte `4 (i % 2) + k` of word `i / 2`. -/
theorem byteAt_eq4 (ws : Array UInt64) (i k : Nat) (hk : k < 4) :
    byteAt ws (4 * i + k) = byteOf ws[i / 2]! (4 * (i % 2) + k) := by
  unfold byteAt byteOf
  rw [show (4 * i + k) / 8 = i / 2 by omega, show (4 * i + k) % 8 = 4 * (i % 2) + k by omega]

theorem be4_zero : be4 0 0 0 0 = 0 := by decide

/-- The bytes of the 32-bit word that holds the last message bytes and `0x80`. -/
theorem markedByte (msg : Array UInt64) (n k : Nat) (hk : k < 4)
    (hp : 4 * (n / 4) + 3 < 4 * (16 * blockCount n - 2)) :
    (implPaddedBytes (bytes msg n)).get! (4 * (n / 4) + k) =
      if k < n % 4 then byteOf msg[n / 4 / 2]! (4 * (n / 4 % 2) + k)
      else if k = n % 4 then 0x80 else 0 := by
  have hn : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
  rw [paddedByte _ _ _ (by omega)]
  by_cases h1 : k < n % 4
  · rw [ite_eq_left (by omega), ite_eq_left h1, byteAt_eq4 _ _ _ hk]
  · rw [ite_eq_right (by omega), ite_eq_right h1]
    by_cases h2 : k = n % 4
    · rw [ite_eq_left (by omega), ite_eq_left h2]
    · rw [ite_eq_right (by omega), ite_eq_right h2, ite_eq_left (by omega)]

theorem shift_eq (n : UInt64) : (n &&& 7) <<< 3 = (8 * (n.toNat % 8)).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_and, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  have : n.toNat % 2 ^ 3 < 8 := Nat.mod_lt _ (by decide)
  simp [Nat.shiftLeft_eq]
  omega

theorem parity (i : Nat) (hi : i < 2 ^ 64) :
    ((UInt64.ofNat i &&& 1) == 0) = decide (i % 2 = 0) := by
  have : (UInt64.ofNat i &&& 1).toNat = i % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hi]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have h' := congrArg UInt64.toNat h
    rw [this] at h'
    simpa using h'
  · intro h
    apply UInt64.toNat_inj.mp
    rw [this, h]
    rfl

/-- The 32-bit word that `half` takes from the byte-reversed word `w`, for 32-bit word `i`. -/
theorem half_bswap (w : UInt64) (i : Nat) (hi : i < 2 ^ 64) :
    (half (bswap w) (UInt64.ofNat i)).toUInt32 =
      be4 (byteOf w (4 * (i % 2) + 0)) (byteOf w (4 * (i % 2) + 1)) (byteOf w (4 * (i % 2) + 2))
        (byteOf w (4 * (i % 2) + 3)) := by
  unfold half
  rw [parity i hi]
  by_cases h : i % 2 = 0
  · rw [decide_eq_true h, ite_eq_left rfl, bswap_high, h]
  · rw [decide_eq_false h, ite_eq_right (by decide), bswap_low, show i % 2 = 1 by omega]

/-- The 32-bit word of word `i` of the padded message of the `n < 2 ^ 61` bytes of `msg`, for `i`
below the number of padded words, is the big-endian word of its four padded bytes. -/
theorem paddedWord_eq (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) (i : Nat)
    (hi : i < 16 * blockCount n.toNat) :
    (paddedWord msg n (UInt64.ofNat (16 * blockCount n.toNat - 1)) (UInt64.ofNat i)).toUInt32 =
      paddedBE (bytes msg n.toNat) i := by
  set N := blockCount n.toNat with hN
  have hN1 : 1 ≤ N := by simp only [hN, blockCount]; split <;> omega
  have hN2 : N ≤ n.toNat / 64 + 2 := by simp only [hN, blockCount]; split <;> omega
  have hL : n.toNat + 1 ≤ 4 * (16 * N - 2) := by
    have := lengthStart msg n.toNat
    rw [← hN] at this
    omega
  have hiN : (UInt64.ofNat i).toNat = i := by rw [UInt64.toNat_ofNat']; omega
  have hlast : (UInt64.ofNat (16 * N - 1)).toNat = 16 * N - 1 := by
    rw [UInt64.toNat_ofNat']; omega
  have hq : (n >>> 2).toNat = n.toNat / 4 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have hhalf : (UInt64.ofNat i >>> 1).toNat = i / 2 := by
    rw [UInt64.toNat_shiftRight, hiN]; simp [Nat.shiftRight_eq_div_pow]
  unfold paddedWord
  by_cases h1 : i = 16 * N - 1
  · -- The low half of the bit length.
    have hb : (UInt64.ofNat i == UInt64.ofNat (16 * N - 1)) = true := by
      rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hiN, hlast, h1]
    rw [ite_eq_left hb, low32_toUInt32, paddedBE_eq _ _
      (fun k => ((n.toNat.toUInt64 <<< 3 >>> (((3 - k) * 8 : Nat).toUInt64)) &&& 0xff).toUInt8)
      (fun k hk => by
        rw [paddedByte _ _ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          lengthBE64_get!_eq _ _ (by omega),
          show 7 - (4 * i + k - 4 * (16 * N - 2)) = 3 - k by omega])]
    rw [show n.toNat.toUInt64 = n from UInt64.ofNat_toNat]
    exact (be4_low (n <<< 3)).symm
  · have hb : (UInt64.ofNat i == UInt64.ofNat (16 * N - 1)) = false := by
      rw [beq_eq_false_iff_ne]; intro h; apply h1
      have := congrArg UInt64.toNat h; rw [hiN, hlast] at this; exact this
    rw [ite_eq_right (by rw [hb]; decide)]
    by_cases h2 : i = 16 * N - 2
    · -- The high half of the bit length.
      have hb2 : (UInt64.ofNat i + 1 == UInt64.ofNat (16 * N - 1)) = true := by
        rw [beq_iff_eq]; apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, hiN, hlast, h2]; simp; omega
      rw [ite_eq_left hb2, low32_toUInt32, paddedBE_eq _ _
        (fun k => ((n.toNat.toUInt64 <<< 3 >>> (((7 - k) * 8 : Nat).toUInt64)) &&& 0xff).toUInt8)
        (fun k hk => by
          rw [paddedByte _ _ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
            lengthBE64_get!_eq _ _ (by omega),
            show 4 * i + k - 4 * (16 * N - 2) = k by omega])]
      rw [show n.toNat.toUInt64 = n from UInt64.ofNat_toNat]
      refine Eq.trans ?_ (be4_high (n <<< 3)).symm
      congr 1
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft]
      simp [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hb2 : (UInt64.ofNat i + 1 == UInt64.ofNat (16 * N - 1)) = false := by
        rw [beq_eq_false_iff_ne]; intro h; apply h2
        have := congrArg UInt64.toNat h
        rw [UInt64.toNat_add, hiN, hlast] at this; simp at this; omega
      rw [ite_eq_right (by rw [hb2]; decide)]
      simp only
      by_cases h3 : i < n.toNat / 4
      · -- A word of message bytes.
        rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hiN, hq]; exact h3), hhalf,
          half_bswap _ _ (by omega), paddedBE_eq _ _ (fun k => byteOf msg[i / 2]! (4 * (i % 2) + k))
            (fun k hk => by
              rw [paddedByte _ _ _ (by omega), ite_eq_left (by omega), byteAt_eq4 _ _ _ hk])]
      · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hiN, hq]; exact h3)]
        by_cases h4 : i = n.toNat / 4
        · -- The word of the last message bytes and `0x80`.
          have hb4 : (UInt64.ofNat i == n >>> 2) = true := by
            rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hiN, hq, h4]
          rw [ite_eq_left hb4, hhalf, shift_eq, half_bswap _ _ (by omega),
            paddedBE_eq _ _ (fun k => if k < n.toNat % 4 then byteOf msg[i / 2]! (4 * (i % 2) + k)
              else if k = n.toNat % 4 then 0x80 else 0) (fun k hk => by
                rw [h4, markedByte _ _ _ hk (by omega)])]
          have hr8 : n.toNat % 8 = 4 * (i % 2) + n.toNat % 4 := by omega
          have hm : ∀ k, k < 4 →
              byteOf ((msg[i / 2]! &&& (((1 : UInt64) <<< (8 * (n.toNat % 8)).toUInt64) - 1)) |||
                ((0x80 : UInt64) <<< (8 * (n.toNat % 8)).toUInt64)) (4 * (i % 2) + k) =
              if k < n.toNat % 4 then byteOf msg[i / 2]! (4 * (i % 2) + k)
              else if k = n.toNat % 4 then 0x80 else 0 := by
            intro k hk
            rw [byteOf_marked _ _ _ (Nat.mod_lt _ (by decide)) (by omega)]
            by_cases ha : k < n.toNat % 4
            · rw [ite_eq_left (by omega), ite_eq_left ha]
            · rw [ite_eq_right (by omega), ite_eq_right ha]
              by_cases hb : k = n.toNat % 4
              · rw [ite_eq_left (by omega), ite_eq_left hb]
              · rw [ite_eq_right (by omega), ite_eq_right hb]
          rw [hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)]
        · -- A word of zero bytes.
          have hb4 : (UInt64.ofNat i == n >>> 2) = false := by
            rw [beq_eq_false_iff_ne]; intro h; apply h4
            have := congrArg UInt64.toNat h; rw [hiN, hq] at this; exact this
          rw [ite_eq_right (by rw [hb4]; decide), paddedBE_eq _ _ (fun _ => 0) (fun k hk => by
            rw [paddedByte _ _ _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
              ite_eq_left (by omega)]), be4_zero]
          rfl

end Library.Hashing.Sha256
