import Library.Hashing.Hmac.Bits
import Library.Hashing.Sha512.Proof

/-! HMAC-SHA-512 computes FIPS 198-1.  `implHmac512` is HMAC built on the copied byte-level
implementation `SHS.SHA512.Impl.sha512`.  `implHmac512_spec` shows that its digest is the
transcription `Spec.hmacSha512` of the key's and the message's bits, and `hmacSha512_bytes` shows
that the digest bytes of `hmacSha512 key kn msg n` are those of `implHmac512` for the first `kn`
bytes of `key` and the first `n` bytes of `msg`.  The proof follows that of HMAC-SHA-256, with
blocks of 128 bytes, words of eight bytes, and a digest of 64 bytes. -/

namespace Library.Hashing.Hmac

open Library.Hashing.Words Library.Bytes Library.Hashing.Sha512
open SHS.Equiv.SHA512 SHS.Equiv.SHA512.Padding.Layout SHS.Equiv.SHA512.Padding.Equiv
  SHS.Equiv.SHA512.Padding.ByteDecoding SHS.Equiv.SHA512.Digest SHS.Equiv.SHA512.Pipeline
  SHS.Equiv.ByteArray SHS.Equiv.Bytes

/-- `K_0` of FIPS 198-1 Table 1 for SHA-512, on bytes, with the copied implementation. -/
def keyBytes512 (K : ByteArray) : ByteArray :=
  if 128 < K.size then appendZeros (digestBytes (SHS.SHA512.Impl.sha512 K)) 64
  else appendZeros K (128 - K.size)

/-- HMAC-SHA-512 on bytes, with the copied implementation. -/
def implHmac512 (K M : ByteArray) : Vector UInt8 64 :=
  SHS.SHA512.Impl.sha512 (xorBytes (keyBytes512 K) 0x5c ++
    digestBytes (SHS.SHA512.Impl.sha512 (xorBytes (keyBytes512 K) 0x36 ++ M)))

/-! ## The transcription -/

theorem impl_sha512_spec (X : ByteArray) (h : X.size < 2 ^ 61) :
    digestBitVec512 (SHS.SHA512.Impl.sha512 X) = Spec.sha512 (bits X) := by
  rw [sha512_correct X h]
  exact (dite_eq_left (bitLen_lt_of_size_lt X h)).symm

theorem bits_digestBytes512 (d : Vector UInt8 64) :
    bits (digestBytes d) = Spec.bitsOf (digestBitVec512 d) := by
  rw [digestBitVec512, bitsOf_fromBits _ (by rw [length_flatMap_byteToBits]; simp)]
  rfl

theorem size_keyBytes512 (K : ByteArray) : (keyBytes512 K).size = 128 := by
  unfold keyBytes512
  split
  · rw [size_appendZeros, size_digestBytes]
  · rw [size_appendZeros]
    omega

theorem bits_keyBytes512 (K : ByteArray) (hK : K.size < 2 ^ 61) :
    bits (keyBytes512 K) = Spec.keyBlock 128 Spec.sha512 (bits K) := by
  have hl := length_bits K
  unfold keyBytes512 Spec.keyBlock
  by_cases h1 : 128 < K.size
  · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega), bits_appendZeros,
      bits_digestBytes512, impl_sha512_spec K hK]
  · rw [ite_eq_right h1, bits_appendZeros]
    by_cases h2 : K.size = 128
    · rw [ite_eq_left (by omega), h2]
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hl,
        show 8 * (128 - K.size) = 8 * 128 - 8 * K.size by omega]

/-- HMAC-SHA-512 on bytes is the transcription of FIPS 198-1 on their bits. -/
theorem implHmac512_spec (K M : ByteArray) (hK : K.size < 2 ^ 61) (hM : M.size + 128 < 2 ^ 61) :
    digestBitVec512 (implHmac512 K M) = Spec.hmacSha512 (bits K) (bits M) := by
  have hin : (xorBytes (keyBytes512 K) 0x36 ++ M).size < 2 ^ 61 := by
    rw [ByteArray.size_append, size_xorBytes, size_keyBytes512]
    omega
  have hout : (xorBytes (keyBytes512 K) 0x5c ++
      digestBytes (SHS.SHA512.Impl.sha512 (xorBytes (keyBytes512 K) 0x36 ++ M))).size <
        2 ^ 61 := by
    rw [ByteArray.size_append, size_xorBytes, size_keyBytes512, size_digestBytes]
    decide
  unfold implHmac512 Spec.hmacSha512 Spec.hmac
  rw [impl_sha512_spec _ hout, bits_append, bits_digestBytes512, impl_sha512_spec _ hin,
    bits_append, bits_xorBytes, bits_xorBytes, size_keyBytes512, bits_keyBytes512 K hK]
  rfl

/-! ## The program -/

theorem beU64_preBlock (P : ByteArray) (t : Nat) (ht : t < 16) :
    SHS.SHA512.Impl.beU64 (preBlock P 0) ⟨t, ht⟩ =
      be8 (P.get! (8 * t + 0)) (P.get! (8 * t + 1)) (P.get! (8 * t + 2)) (P.get! (8 * t + 3))
        (P.get! (8 * t + 4)) (P.get! (8 * t + 5)) (P.get! (8 * t + 6)) (P.get! (8 * t + 7)) := by
  simp only [SHS.SHA512.Impl.beU64, preBlock, Vector.getElem_ofFn, be8, Nat.zero_mul,
    Nat.zero_add, Nat.add_zero]

theorem toVec_get (m : Words16) (t : Nat) (ht : t < 16) : m.toVec[t] = m.get t := by
  interval_cases t <;> rfl

theorem extractDigest512_get (S : SHS.SHA512.Impl.State) (t k : Nat) (ht : t < 8) (hk : k < 8) :
    (extractDigest512 S)[8 * t + k]'(by omega) =
      ((S[t]'ht >>> UInt64.ofNat ((7 - k) * 8)) &&& 0xff).toUInt8 := by
  unfold extractDigest512
  rw [Vector.getElem_ofFn]
  simp only [Fin.getElem_fin, show (8 * t + k) / 8 = t by omega, show (8 * t + k) % 8 = k by omega]

theorem be8_extract (x : UInt64) :
    be8 ((x >>> UInt64.ofNat ((7 - 0) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt64.ofNat ((7 - 1) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt64.ofNat ((7 - 2) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt64.ofNat ((7 - 3) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt64.ofNat ((7 - 4) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt64.ofNat ((7 - 5) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt64.ofNat ((7 - 6) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt64.ofNat ((7 - 7) * 8)) &&& 0xff).toUInt8 = x :=
  be8_bytes x

/-- The bytes of a digest assemble into the words of the state. -/
theorem be8_digest (S : SHS.SHA512.Impl.State) (t : Nat) (ht : t < 8) :
    be8 (extractDigest512 S)[8 * t + 0] (extractDigest512 S)[8 * t + 1]
      (extractDigest512 S)[8 * t + 2] (extractDigest512 S)[8 * t + 3]
      (extractDigest512 S)[8 * t + 4] (extractDigest512 S)[8 * t + 5]
      (extractDigest512 S)[8 * t + 6] (extractDigest512 S)[8 * t + 7] = S[t] := by
  rw [extractDigest512_get S t 0 ht (by decide), extractDigest512_get S t 1 ht (by decide),
    extractDigest512_get S t 2 ht (by decide), extractDigest512_get S t 3 ht (by decide),
    extractDigest512_get S t 4 ht (by decide), extractDigest512_get S t 5 ht (by decide),
    extractDigest512_get S t 6 ht (by decide), extractDigest512_get S t 7 ht (by decide),
    be8_extract]

set_option maxHeartbeats 800000 in
theorem be8_xor (a0 a1 a2 a3 a4 a5 a6 a7 e : UInt8) :
    be8 (a0 ^^^ e) (a1 ^^^ e) (a2 ^^^ e) (a3 ^^^ e) (a4 ^^^ e) (a5 ^^^ e) (a6 ^^^ e) (a7 ^^^ e) =
      be8 a0 a1 a2 a3 a4 a5 a6 a7 ^^^ be8 e e e e e e e e := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64,
    UInt64.toBitVec_xor, UInt8.toBitVec_xor]
  interval_cases i <;> simp

theorem keyBytes512_short (key : Array UInt64) (kn j : Nat) (hkn : kn ≤ 128) (hj : j < 128) :
    (keyBytes512 (bytes key kn)).get! j = keyByte key kn j := by
  unfold keyBytes512 keyByte
  rw [ite_eq_right (by rw [bytes_size]; omega)]
  by_cases h : j < kn
  · rw [ite_eq_left h, get!_appendZeros_lt _ _ _ (by rw [bytes_size]; exact h), bytes_get! _ _ _ h]
  · rw [ite_eq_right h, get!_appendZeros_ge _ _ _ (by rw [bytes_size]; omega)
      (by rw [bytes_size]; omega)]

theorem keyBytes512_long (K : ByteArray) (hK : 128 < K.size) (j : Nat) (hj : j < 64) :
    (keyBytes512 K).get! j = (SHS.SHA512.Impl.sha512 K)[j] := by
  unfold keyBytes512
  rw [ite_eq_left hK, get!_appendZeros_lt _ _ _ (by rw [size_digestBytes]; exact hj),
    get!_digestBytes _ _ hj]

theorem keyBytes512_long_zero (K : ByteArray) (hK : 128 < K.size) (j : Nat) (hj1 : 64 ≤ j)
    (hj2 : j < 128) : (keyBytes512 K).get! j = 0 := by
  unfold keyBytes512
  rw [ite_eq_left hK, get!_appendZeros_ge _ _ _ (by rw [size_digestBytes]; exact hj1)
    (by rw [size_digestBytes]; omega)]

/-- `keyWord512` reads word `t` of the key bytes, with zero bytes after the key. -/
theorem keyWord512_eq (key : Array UInt64) (kn : UInt64) (t : Nat) (ht : t < 16) :
    keyWord512 key kn (UInt64.ofNat t) =
      be8 (keyByte key kn.toNat (8 * t + 0)) (keyByte key kn.toNat (8 * t + 1))
        (keyByte key kn.toNat (8 * t + 2)) (keyByte key kn.toNat (8 * t + 3))
        (keyByte key kn.toNat (8 * t + 4)) (keyByte key kn.toNat (8 * t + 5))
        (keyByte key kn.toNat (8 * t + 6)) (keyByte key kn.toNat (8 * t + 7)) := by
  have hiN : (UInt64.ofNat t).toNat = t := by rw [UInt64.toNat_ofNat']; omega
  have hq : (kn >>> 3).toNat = kn.toNat / 8 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  unfold keyWord512
  simp only
  rw [hiN]
  by_cases h3 : t < kn.toNat / 8
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hiN, hq]; exact h3), bswap_eq]
    unfold keyByte
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), ite_eq_left (by omega), byteAt_eq _ _ _ (by decide),
      byteAt_eq _ _ _ (by decide), byteAt_eq _ _ _ (by decide), byteAt_eq _ _ _ (by decide),
      byteAt_eq _ _ _ (by decide), byteAt_eq _ _ _ (by decide), byteAt_eq _ _ _ (by decide),
      byteAt_eq _ _ _ (by decide)]
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hiN, hq]; exact h3)]
    by_cases h4 : t = kn.toNat / 8
    · have hb4 : (UInt64.ofNat t == kn >>> 3) = true := by
        rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hiN, hq, h4]
      rw [ite_eq_left hb4, shift_eq, bswap_eq]
      have hm : ∀ k, k < 8 →
          byteOf (key[t]! &&& (((1 : UInt64) <<< (8 * (kn.toNat % 8)).toUInt64) - 1)) k =
            keyByte key kn.toNat (8 * t + k) := by
        intro k hk
        rw [byteOf_masked _ _ _ (Nat.mod_lt _ (by decide)) hk]
        unfold keyByte
        by_cases ha : k < kn.toNat % 8
        · rw [ite_eq_left ha, ite_eq_left (by omega), byteAt_eq _ _ _ hk]
        · rw [ite_eq_right ha, ite_eq_right (by omega)]
      rw [hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide),
        hm 4 (by decide), hm 5 (by decide), hm 6 (by decide), hm 7 (by decide)]
    · have hb4 : (UInt64.ofNat t == kn >>> 3) = false := by
        rw [beq_eq_false_iff_ne]; intro h; apply h4
        have := congrArg UInt64.toNat h; rw [hiN, hq] at this; exact this
      rw [ite_eq_right (by rw [hb4]; decide)]
      unfold keyByte
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), be8_zero]

/-- The program's key block is `K_0` of the copied implementation. -/
theorem keyBlock512_get (key : Array UInt64) (kn : UInt64) (hk : kn.toNat < 2 ^ 61) (t : Nat)
    (ht : t < 16) :
    (keyBlock512 roundConstants key kn).get t =
      SHS.SHA512.Impl.beU64 (preBlock (keyBytes512 (bytes key kn.toNat)) 0) ⟨t, ht⟩ := by
  rw [beU64_preBlock]
  unfold keyBlock512
  by_cases hl : 128 < kn.toNat
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt]; exact hl)]
    have hK : 128 < (bytes key kn.toNat).size := by rw [bytes_size]; exact hl
    have hS := hashFrom_iv iv512 key kn hk
    rw [iv512_toVec] at hS
    have hD : SHS.SHA512.Impl.sha512 (bytes key kn.toNat) =
        extractDigest512
          (implSha512StateRefactored (bytes key kn.toNat) SHS.SHA512.Impl.H0_512) := by
      rw [impl_sha512_eq_refactored _ (by rw [bytes_size]; exact hk)]
      rfl
    generalize hashFrom roundConstants iv512 key kn kn = d at hS ⊢
    by_cases h8 : t < 8
    · rw [keyBytes512_long _ hK _ (by omega), keyBytes512_long _ hK _ (by omega),
        keyBytes512_long _ hK _ (by omega), keyBytes512_long _ hK _ (by omega),
        keyBytes512_long _ hK _ (by omega), keyBytes512_long _ hK _ (by omega),
        keyBytes512_long _ hK _ (by omega), keyBytes512_long _ hK _ (by omega), hD,
        be8_digest _ t h8, ← hS]
      interval_cases t <;> rfl
    · rw [keyBytes512_long_zero _ hK _ (by omega) (by omega),
        keyBytes512_long_zero _ hK _ (by omega) (by omega),
        keyBytes512_long_zero _ hK _ (by omega) (by omega),
        keyBytes512_long_zero _ hK _ (by omega) (by omega),
        keyBytes512_long_zero _ hK _ (by omega) (by omega),
        keyBytes512_long_zero _ hK _ (by omega) (by omega),
        keyBytes512_long_zero _ hK _ (by omega) (by omega),
        keyBytes512_long_zero _ hK _ (by omega) (by omega), be8_zero]
      interval_cases t <;> rfl
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt]; exact hl)]
    rw [keyBytes512_short _ _ _ (by omega) (by omega),
      keyBytes512_short _ _ _ (by omega) (by omega),
      keyBytes512_short _ _ _ (by omega) (by omega), keyBytes512_short _ _ _ (by omega) (by omega),
      keyBytes512_short _ _ _ (by omega) (by omega), keyBytes512_short _ _ _ (by omega) (by omega),
      keyBytes512_short _ _ _ (by omega) (by omega), keyBytes512_short _ _ _ (by omega) (by omega),
      ← keyWord512_eq key kn t ht]
    interval_cases t <;> rfl

/-- The block `K_0 ⊕ c` in the program is the copied implementation's. -/
theorem xorBlock_toVec (key : Array UInt64) (kn : UInt64) (hk : kn.toNat < 2 ^ 61) (b : UInt8)
    (c : UInt64) (hc : be8 b b b b b b b b = c) :
    (xorBlock (keyBlock512 roundConstants key kn) c).toVec =
      SHS.SHA512.Impl.toU64s (preBlock (xorBytes (keyBytes512 (bytes key kn.toNat)) b) 0) := by
  apply Vector.ext
  intro t ht
  have hK := size_keyBytes512 (bytes key kn.toNat)
  rw [toVec_get _ t ht, xorBlock_get _ _ t ht, keyBlock512_get key kn hk t ht,
    SHS.SHA512.Impl.toU64s, Vector.getElem_ofFn, beU64_preBlock, beU64_preBlock,
    get!_xorBytes _ _ _ (by omega), get!_xorBytes _ _ _ (by omega),
    get!_xorBytes _ _ _ (by omega), get!_xorBytes _ _ _ (by omega),
    get!_xorBytes _ _ _ (by omega), get!_xorBytes _ _ _ (by omega),
    get!_xorBytes _ _ _ (by omega), get!_xorBytes _ _ _ (by omega), be8_xor, hc]

/-! ## The inner and outer hash values -/

/-- The inner hash value is the implementation's state after `(K_0 ⊕ ipad) || text`. -/
theorem inner_toVec (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64)
    (hk : kn.toNat < 2 ^ 61) (hn : n.toNat + 128 < 2 ^ 61) :
    (hashFrom roundConstants
        (compress roundConstants iv512
          (xorBlock (keyBlock512 roundConstants key kn) 0x3636363636363636))
        msg n (n + 128)).toVec =
      implSha512StateRefactored
        (xorBytes (keyBytes512 (bytes key kn.toNat)) 0x36 ++ bytes msg n.toNat) iv512.toVec := by
  have hP : (xorBytes (keyBytes512 (bytes key kn.toNat)) 0x36).size = 128 * 1 := by
    rw [size_xorBytes, size_keyBytes512]
  have hlen : (n + 128).toNat = 128 * 1 + n.toNat := by
    rw [UInt64.toNat_add, show (128 : UInt64).toNat = 128 from rfl]
    omega
  rw [hashFrom_toVec _ 1 hP _ msg n (n + 128) hlen (by omega)]
  unfold implSha512StateRefactored
  rw [foldl_append _ 1 hP (bytes msg n.toNat), bytes_size, fold_one, compress_toVec,
    xorBlock_toVec key kn hk 0x36 0x3636363636363636 (by decide)]

/-- The final block of the outer message `(K_0 ⊕ opad) || D` for a digest `D` of 64 bytes. -/
theorem outerBlock512 (Q D : ByteArray) (hQ : Q.size = 128) (hD : D.size = 64) (t : Nat)
    (ht : t < 16) :
    SHS.SHA512.Impl.beU64 (paddedBlock (Q ++ D) 1) ⟨t, ht⟩ =
      if t < 8 then be8 (D.get! (8 * t + 0)) (D.get! (8 * t + 1)) (D.get! (8 * t + 2))
        (D.get! (8 * t + 3)) (D.get! (8 * t + 4)) (D.get! (8 * t + 5)) (D.get! (8 * t + 6))
        (D.get! (8 * t + 7))
      else if t = 8 then 0x8000000000000000 else if t = 15 then 1536 else 0 := by
  have hs : (Q ++ D).size = 192 := by rw [ByteArray.size_append, hQ, hD]
  have hz : zerosCount (Q ++ D) = 47 := by unfold zerosCount; rw [hs]; decide
  have hsize : (implPaddedBytes (Q ++ D)).size = 256 := by
    rw [size_implPaddedBytes_eq, hs, hz]
  have hb : ∀ k, k < 8 → (implPaddedBytes (Q ++ D)).get! (128 + 8 * t + k) =
      if 128 + 8 * t + k < 192 then D.get! (8 * t + k)
      else if 128 + 8 * t + k = 192 then 0x80
      else if 128 + 8 * t + k < 192 + 1 + 47 then 0
      else (lengthBE128 ((192 : Nat).toUInt64 <<< 3)).get! (128 + 8 * t + k - (192 + 1 + 47)) := by
    intro k hk
    rw [get!_implPaddedBytes_eq _ _ (by rw [hsize]; omega), hs, hz]
    by_cases h : 128 + 8 * t + k < 192
    · rw [ite_eq_left h, ite_eq_left h, get!_append_right _ _ _ (by omega) (by omega), hQ,
        show 128 + 8 * t + k - 128 = 8 * t + k by omega]
    · rw [ite_eq_right h, ite_eq_right h]
  have hidx : ∀ k, 8 * (16 * 1 + t) + k = 128 + 8 * t + k := fun k => by omega
  rw [beU64_paddedBlock, paddedBE, hidx 0, hidx 1, hidx 2, hidx 3, hidx 4, hidx 5, hidx 6, hidx 7,
    hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), hb 6 (by decide), hb 7 (by decide)]
  interval_cases t <;> simp [lengthBE128_get!_eq, lengthBE128_get!_zero] <;> decide

theorem digest_bytes512 (h : Words8) :
    (⟨bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3, bswap h.w4, bswap h.w5, bswap h.w6,
      bswap h.w7⟩ : Words8).bytes = extractDigest512 h.toVec := by
  apply Vector.ext
  intro i hi
  rw [Words8.bytes, Vector.getElem_ofFn]
  unfold extractDigest512
  rw [Vector.getElem_ofFn]
  exact byteAt_bswap _ h.toVec i (by omega) (words8_get h (i / 8) (by omega))

/-- The outer hash value is the implementation's state after `(K_0 ⊕ opad) || D`, where `D` is
the digest of the inner message, whose state is `inner`. -/
theorem outer_toVec (key : Array UInt64) (kn : UInt64) (hk : kn.toNat < 2 ^ 61) (Y : ByteArray)
    (hY : Y.size < 2 ^ 61) (inner : Words8)
    (hI : inner.toVec = implSha512StateRefactored Y iv512.toVec) :
    (compress roundConstants
        (compress roundConstants iv512
          (xorBlock (keyBlock512 roundConstants key kn) 0x5c5c5c5c5c5c5c5c))
        ⟨inner.w0, inner.w1, inner.w2, inner.w3, inner.w4, inner.w5, inner.w6, inner.w7,
          0x8000000000000000, 0, 0, 0, 0, 0, 0, 1536⟩).toVec =
      implSha512StateRefactored (xorBytes (keyBytes512 (bytes key kn.toNat)) 0x5c ++
        digestBytes (SHS.SHA512.Impl.sha512 Y)) iv512.toVec := by
  have hD : SHS.SHA512.Impl.sha512 Y = extractDigest512 inner.toVec := by
    rw [impl_sha512_eq_refactored _ hY, hI, iv512_toVec]
    rfl
  have hQ : (xorBytes (keyBytes512 (bytes key kn.toNat)) 0x5c).size = 128 * 1 := by
    rw [size_xorBytes, size_keyBytes512]
  have hB : (⟨inner.w0, inner.w1, inner.w2, inner.w3, inner.w4, inner.w5, inner.w6, inner.w7,
        0x8000000000000000, 0, 0, 0, 0, 0, 0, 1536⟩ : Words16).toVec =
      SHS.SHA512.Impl.toU64s (paddedBlock (xorBytes (keyBytes512 (bytes key kn.toNat)) 0x5c ++
        digestBytes (extractDigest512 inner.toVec)) 1) := by
    apply Vector.ext
    intro t ht
    rw [SHS.SHA512.Impl.toU64s, Vector.getElem_ofFn,
      outerBlock512 _ _ (by omega) (size_digestBytes _) t ht]
    by_cases h8 : t < 8
    · rw [ite_eq_left h8, get!_digestBytes _ _ (by omega), get!_digestBytes _ _ (by omega),
        get!_digestBytes _ _ (by omega), get!_digestBytes _ _ (by omega),
        get!_digestBytes _ _ (by omega), get!_digestBytes _ _ (by omega),
        get!_digestBytes _ _ (by omega), get!_digestBytes _ _ (by omega), be8_digest _ t h8]
      interval_cases t <;> rfl
    · rw [ite_eq_right h8]
      interval_cases t <;> rfl
  unfold implSha512StateRefactored
  rw [foldl_append _ 1 hQ, size_digestBytes, fold_one, hD, show blockCount 64 = 1 by decide,
    fold_one, show (1 + 0 : Nat) = 1 from rfl, compress_toVec, compress_toVec,
    xorBlock_toVec key kn hk 0x5c 0x5c5c5c5c5c5c5c5c (by decide), hB]

/-- The digest bytes of the program are those of HMAC on the copied implementation. -/
theorem hmacSha512_bytes (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64)
    (hk : kn.toNat < 2 ^ 61) (hn : n.toNat + 128 < 2 ^ 61) :
    (hmacSha512 key kn msg n).bytes = implHmac512 (bytes key kn.toNat) (bytes msg n.toNat) := by
  have hY : (xorBytes (keyBytes512 (bytes key kn.toNat)) 0x36 ++ bytes msg n.toNat).size <
      2 ^ 61 := by
    rw [ByteArray.size_append, size_xorBytes, size_keyBytes512, bytes_size]
    omega
  have hX : (xorBytes (keyBytes512 (bytes key kn.toNat)) 0x5c ++
      digestBytes (SHS.SHA512.Impl.sha512
        (xorBytes (keyBytes512 (bytes key kn.toNat)) 0x36 ++ bytes msg n.toNat))).size <
          2 ^ 61 := by
    rw [ByteArray.size_append, size_xorBytes, size_keyBytes512, size_digestBytes]
    decide
  unfold hmacSha512 hmacSha512With implHmac512
  simp only
  rw [digest_bytes512, outer_toVec key kn hk _ hY _ (inner_toVec key kn msg n hk hn),
    impl_sha512_eq_refactored _ hX, iv512_toVec]
  rfl

/-- HMAC-SHA-512 of the first `kn` bytes of `key` and the first `n` bytes of `msg` is the digest of
FIPS 198-1 on their bits. -/
theorem hmacSha512_spec (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64)
    (hk : kn.toNat < 2 ^ 61) (hn : n.toNat + 128 < 2 ^ 61) :
    digestBitVec512 (hmacSha512 key kn msg n).bytes =
      Spec.hmacSha512 (bits (bytes key kn.toNat)) (bits (bytes msg n.toNat)) := by
  rw [hmacSha512_bytes key kn msg n hk hn]
  exact implHmac512_spec _ _ (by rw [bytes_size]; exact hk) (by rw [bytes_size]; exact hn)

#print axioms hmacSha512_spec

end Library.Hashing.Hmac
