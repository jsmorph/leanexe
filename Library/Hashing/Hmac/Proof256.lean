import Library.Hashing.Hmac.Bits
import Library.Hashing.Sha256.Proof

/-! HMAC-SHA-256 computes FIPS 198-1.  `implHmac256` is HMAC built on the copied byte-level
implementation `SHS.SHA256.Impl.sha256`.  `implHmac256_spec` shows that its digest is the
transcription `Spec.hmacSha256` of the key's and the message's bits, and `hmacSha256_bytes` shows
that the digest bytes of `hmacSha256 key kn msg n` are those of `implHmac256` for the first `kn`
bytes of `key` and the first `n` bytes of `msg`.  The program's key block is `K_0` of Table 1,
its inner hash value is the implementation's state after `(K_0 ⊕ ipad) || text`, and its final
block is the padded block that follows `K_0 ⊕ opad` in the outer message. -/

namespace Library.Hashing.Hmac

open Library.Hashing.Words Library.Hashing.Sha256
open SHS.Equiv.SHA256 SHS.Equiv.SHA256.Padding.Layout SHS.Equiv.SHA256.Padding.Equiv
  SHS.Equiv.SHA256.Padding.ByteDecoding SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Pipeline
  SHS.Equiv.ByteArray SHS.Equiv.Bytes

/-- `K_0` of FIPS 198-1 Table 1 for SHA-256, on bytes, with the copied implementation. -/
def keyBytes256 (K : ByteArray) : ByteArray :=
  if 64 < K.size then appendZeros (digestBytes (SHS.SHA256.Impl.sha256 K)) 32
  else appendZeros K (64 - K.size)

/-- HMAC-SHA-256 on bytes, with the copied implementation. -/
def implHmac256 (K M : ByteArray) : Vector UInt8 32 :=
  SHS.SHA256.Impl.sha256 (xorBytes (keyBytes256 K) 0x5c ++
    digestBytes (SHS.SHA256.Impl.sha256 (xorBytes (keyBytes256 K) 0x36 ++ M)))

/-! ## The transcription -/

theorem impl_sha256_spec (X : ByteArray) (h : X.size < 2 ^ 61) :
    digestBitVec (SHS.SHA256.Impl.sha256 X) = Spec.sha256 (bits X) := by
  rw [sha256_correct X h]
  exact (dite_eq_left (bitLen_lt_of_size_lt X h)).symm

theorem bits_digestBytes256 (d : Vector UInt8 32) :
    bits (digestBytes d) = Spec.bitsOf (digestBitVec d) := by
  rw [digestBitVec, bitsOf_fromBits _ (by rw [length_flatMap_byteToBits]; simp)]
  rfl

theorem size_keyBytes256 (K : ByteArray) : (keyBytes256 K).size = 64 := by
  unfold keyBytes256
  split
  · rw [size_appendZeros, size_digestBytes]
  · rw [size_appendZeros]
    omega

theorem bits_keyBytes256 (K : ByteArray) (hK : K.size < 2 ^ 61) :
    bits (keyBytes256 K) = Spec.keyBlock 64 Spec.sha256 (bits K) := by
  have hl := length_bits K
  unfold keyBytes256 Spec.keyBlock
  by_cases h1 : 64 < K.size
  · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_left (by omega), bits_appendZeros,
      bits_digestBytes256, impl_sha256_spec K hK]
  · rw [ite_eq_right h1, bits_appendZeros]
    by_cases h2 : K.size = 64
    · rw [ite_eq_left (by omega), h2]
      simp
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), hl,
        show 8 * (64 - K.size) = 8 * 64 - 8 * K.size by omega]

/-- HMAC-SHA-256 on bytes is the transcription of FIPS 198-1 on their bits. -/
theorem implHmac256_spec (K M : ByteArray) (hK : K.size < 2 ^ 61) (hM : M.size + 64 < 2 ^ 61) :
    digestBitVec (implHmac256 K M) = Spec.hmacSha256 (bits K) (bits M) := by
  have hin : (xorBytes (keyBytes256 K) 0x36 ++ M).size < 2 ^ 61 := by
    rw [ByteArray.size_append, size_xorBytes, size_keyBytes256]
    omega
  have hout : (xorBytes (keyBytes256 K) 0x5c ++
      digestBytes (SHS.SHA256.Impl.sha256 (xorBytes (keyBytes256 K) 0x36 ++ M))).size < 2 ^ 61 := by
    rw [ByteArray.size_append, size_xorBytes, size_keyBytes256, size_digestBytes]
    decide
  unfold implHmac256 Spec.hmacSha256 Spec.hmac
  rw [impl_sha256_spec _ hout, bits_append, bits_digestBytes256, impl_sha256_spec _ hin, bits_append,
    bits_xorBytes, bits_xorBytes, size_keyBytes256, bits_keyBytes256 K hK]
  rfl

/-! ## The program -/

theorem beU32_preBlock (P : ByteArray) (t : Nat) (ht : t < 16) :
    SHS.SHA256.Impl.beU32 (preBlock P 0) ⟨t, ht⟩ =
      be4 (P.get! (4 * t + 0)) (P.get! (4 * t + 1)) (P.get! (4 * t + 2)) (P.get! (4 * t + 3)) := by
  simp only [SHS.SHA256.Impl.beU32, preBlock, Vector.getElem_ofFn, be4, Nat.zero_mul,
    Nat.zero_add, Nat.add_zero]

theorem toVec32_get (m : Words16) (t : Nat) (ht : t < 16) : m.toVec32[t] = (m.get t).toUInt32 := by
  interval_cases t <;> rfl

theorem extractDigest_get (S : SHS.SHA256.Impl.State) (t k : Nat) (ht : t < 8) (hk : k < 4) :
    (extractDigest S)[4 * t + k]'(by omega) =
      ((S[t]'ht >>> UInt32.ofNat ((3 - k) * 8)) &&& 0xff).toUInt8 := by
  unfold extractDigest
  rw [Vector.getElem_ofFn]
  simp only [Fin.getElem_fin, show (4 * t + k) / 4 = t by omega, show (4 * t + k) % 4 = k by omega]

set_option maxHeartbeats 800000 in
theorem be4_extract (x : UInt32) :
    be4 ((x >>> UInt32.ofNat ((3 - 0) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt32.ofNat ((3 - 1) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt32.ofNat ((3 - 2) * 8)) &&& 0xff).toUInt8
      ((x >>> UInt32.ofNat ((3 - 3) * 8)) &&& 0xff).toUInt8 = x := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be4, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32,
    UInt32.toBitVec_and, UInt32.toBitVec_shiftRight, UInt32.toBitVec_toUInt8]
  interval_cases i <;> simp

/-- The bytes of a digest assemble into the words of the state. -/
theorem be4_digest (S : SHS.SHA256.Impl.State) (t : Nat) (ht : t < 8) :
    be4 (extractDigest S)[4 * t + 0] (extractDigest S)[4 * t + 1] (extractDigest S)[4 * t + 2]
      (extractDigest S)[4 * t + 3] = S[t] := by
  rw [extractDigest_get S t 0 ht (by decide), extractDigest_get S t 1 ht (by decide),
    extractDigest_get S t 2 ht (by decide), extractDigest_get S t 3 ht (by decide), be4_extract]

theorem be4_zero' : be4 0 0 0 0 = 0 := by decide

theorem be4_xor (a b c d e : UInt8) :
    be4 (a ^^^ e) (b ^^^ e) (c ^^^ e) (d ^^^ e) = be4 a b c d ^^^ be4 e e e e := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be4, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32,
    UInt32.toBitVec_xor, UInt8.toBitVec_xor]
  interval_cases i <;> simp

theorem keyBytes256_short (key : Array UInt64) (kn j : Nat) (hkn : kn ≤ 64) (hj : j < 64) :
    (keyBytes256 (bytes key kn)).get! j = keyByte key kn j := by
  unfold keyBytes256 keyByte
  rw [ite_eq_right (by rw [bytes_size]; omega)]
  by_cases h : j < kn
  · rw [ite_eq_left h, get!_appendZeros_lt _ _ _ (by rw [bytes_size]; exact h), bytes_get! _ _ _ h]
  · rw [ite_eq_right h, get!_appendZeros_ge _ _ _ (by rw [bytes_size]; omega)
      (by rw [bytes_size]; omega)]

theorem keyBytes256_long (K : ByteArray) (hK : 64 < K.size) (j : Nat) (hj : j < 32) :
    (keyBytes256 K).get! j = (SHS.SHA256.Impl.sha256 K)[j] := by
  unfold keyBytes256
  rw [ite_eq_left hK, get!_appendZeros_lt _ _ _ (by rw [size_digestBytes]; exact hj),
    get!_digestBytes _ _ hj]

theorem keyBytes256_long_zero (K : ByteArray) (hK : 64 < K.size) (j : Nat) (hj1 : 32 ≤ j)
    (hj2 : j < 64) : (keyBytes256 K).get! j = 0 := by
  unfold keyBytes256
  rw [ite_eq_left hK, get!_appendZeros_ge _ _ _ (by rw [size_digestBytes]; exact hj1)
    (by rw [size_digestBytes]; omega)]

/-- `keyWord256` reads the 32-bit word `t` of the key bytes, with zero bytes after the key. -/
theorem keyWord256_eq (key : Array UInt64) (kn : UInt64) (t : Nat) (ht : t < 16) :
    (keyWord256 key kn (UInt64.ofNat t)).toUInt32 =
      be4 (keyByte key kn.toNat (4 * t + 0)) (keyByte key kn.toNat (4 * t + 1))
        (keyByte key kn.toNat (4 * t + 2)) (keyByte key kn.toNat (4 * t + 3)) := by
  have hiN : (UInt64.ofNat t).toNat = t := by rw [UInt64.toNat_ofNat']; omega
  have hq : (kn >>> 2).toNat = kn.toNat / 4 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have hhalf : (UInt64.ofNat t >>> 1).toNat = t / 2 := by
    rw [UInt64.toNat_shiftRight, hiN]; simp [Nat.shiftRight_eq_div_pow]
  unfold keyWord256
  simp only
  by_cases h3 : t < kn.toNat / 4
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, hiN, hq]; exact h3), hhalf,
      half_bswap _ _ (by omega)]
    unfold keyByte
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega), byteAt_eq4 _ _ _ (by decide), byteAt_eq4 _ _ _ (by decide),
      byteAt_eq4 _ _ _ (by decide), byteAt_eq4 _ _ _ (by decide)]
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, hiN, hq]; exact h3)]
    by_cases h4 : t = kn.toNat / 4
    · have hb4 : (UInt64.ofNat t == kn >>> 2) = true := by
        rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hiN, hq, h4]
      rw [ite_eq_left hb4, hhalf, shift_eq, half_bswap _ _ (by omega)]
      have hm : ∀ k, k < 4 →
          byteOf (key[t / 2]! &&& (((1 : UInt64) <<< (8 * (kn.toNat % 8)).toUInt64) - 1))
            (4 * (t % 2) + k) = keyByte key kn.toNat (4 * t + k) := by
        intro k hk
        rw [byteOf_masked _ _ _ (Nat.mod_lt _ (by decide)) (by omega)]
        unfold keyByte
        by_cases ha : 4 * (t % 2) + k < kn.toNat % 8
        · rw [ite_eq_left ha, ite_eq_left (by omega), byteAt_eq4 _ _ _ hk]
        · rw [ite_eq_right ha, ite_eq_right (by omega)]
      rw [hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)]
    · have hb4 : (UInt64.ofNat t == kn >>> 2) = false := by
        rw [beq_eq_false_iff_ne]; intro h; apply h4
        have := congrArg UInt64.toNat h; rw [hiN, hq] at this; exact this
      rw [ite_eq_right (by rw [hb4]; decide)]
      unfold keyByte
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), be4_zero']
      rfl

/-- The program's key block is `K_0` of the copied implementation. -/
theorem keyBlock256_get (key : Array UInt64) (kn : UInt64) (hk : kn.toNat < 2 ^ 61) (t : Nat)
    (ht : t < 16) :
    ((keyBlock256 roundConstants key kn).get t).toUInt32 =
      SHS.SHA256.Impl.beU32 (preBlock (keyBytes256 (bytes key kn.toNat)) 0) ⟨t, ht⟩ := by
  rw [beU32_preBlock]
  unfold keyBlock256
  by_cases hl : 64 < kn.toNat
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt]; exact hl)]
    have hK : 64 < (bytes key kn.toNat).size := by rw [bytes_size]; exact hl
    have hS := hashFrom_iv iv256 key kn hk
    rw [iv256_toVec32] at hS
    have hD : SHS.SHA256.Impl.sha256 (bytes key kn.toNat) =
        extractDigest
          (implSha256StateRefactored (bytes key kn.toNat) SHS.SHA256.Impl.H256_256) := by
      rw [impl_sha256_eq_refactored _ (by rw [bytes_size]; exact hk)]
      rfl
    generalize hashFrom roundConstants iv256 key kn kn = d at hS ⊢
    by_cases h8 : t < 8
    · rw [keyBytes256_long _ hK _ (by omega), keyBytes256_long _ hK _ (by omega),
        keyBytes256_long _ hK _ (by omega), keyBytes256_long _ hK _ (by omega), hD,
        be4_digest _ t h8, ← hS]
      interval_cases t <;> rfl
    · rw [keyBytes256_long_zero _ hK _ (by omega) (by omega),
        keyBytes256_long_zero _ hK _ (by omega) (by omega),
        keyBytes256_long_zero _ hK _ (by omega) (by omega),
        keyBytes256_long_zero _ hK _ (by omega) (by omega), be4_zero']
      interval_cases t <;> rfl
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt]; exact hl)]
    rw [keyBytes256_short _ _ _ (by omega) (by omega),
      keyBytes256_short _ _ _ (by omega) (by omega),
      keyBytes256_short _ _ _ (by omega) (by omega), keyBytes256_short _ _ _ (by omega) (by omega),
      ← keyWord256_eq key kn t ht]
    interval_cases t <;> rfl

/-- The block `K_0 ⊕ c` in the program is the copied implementation's. -/
theorem xorBlock_toVec32 (key : Array UInt64) (kn : UInt64) (hk : kn.toNat < 2 ^ 61) (b : UInt8)
    (c : UInt64) (hc : c.toUInt32 = be4 b b b b) :
    (xorBlock (keyBlock256 roundConstants key kn) c).toVec32 =
      SHS.SHA256.Impl.toU32s (preBlock (xorBytes (keyBytes256 (bytes key kn.toNat)) b) 0) := by
  apply Vector.ext
  intro t ht
  have hK := size_keyBytes256 (bytes key kn.toNat)
  rw [toVec32_get _ t ht, xorBlock_get _ _ t ht, UInt64.toUInt32_xor, keyBlock256_get key kn hk t ht,
    SHS.SHA256.Impl.toU32s,
    Vector.getElem_ofFn, beU32_preBlock, beU32_preBlock, get!_xorBytes _ _ _ (by omega),
    get!_xorBytes _ _ _ (by omega), get!_xorBytes _ _ _ (by omega), get!_xorBytes _ _ _ (by omega),
    be4_xor, hc]

/-! ## The inner and outer hash values -/

/-- The inner hash value is the implementation's state after `(K_0 ⊕ ipad) || text`. -/
theorem inner_toVec32 (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64)
    (hk : kn.toNat < 2 ^ 61) (hn : n.toNat + 64 < 2 ^ 61) :
    (hashFrom roundConstants
        (compress roundConstants iv256 (xorBlock (keyBlock256 roundConstants key kn) 0x36363636))
        msg n (n + 64)).toVec32 =
      implSha256StateRefactored
        (xorBytes (keyBytes256 (bytes key kn.toNat)) 0x36 ++ bytes msg n.toNat) iv256.toVec32 := by
  have hP : (xorBytes (keyBytes256 (bytes key kn.toNat)) 0x36).size = 64 * 1 := by
    rw [size_xorBytes, size_keyBytes256]
  have hlen : (n + 64).toNat = 64 * 1 + n.toNat := by
    rw [UInt64.toNat_add, show (64 : UInt64).toNat = 64 from rfl]
    omega
  rw [hashFrom_toVec32 _ 1 hP _ msg n (n + 64) hlen (by omega)]
  unfold implSha256StateRefactored
  rw [foldl_append _ 1 hP (bytes msg n.toNat), bytes_size, fold_one, compress_toVec32,
    xorBlock_toVec32 key kn hk 0x36 0x36363636 (by decide)]

/-- The final block of the outer message `(K_0 ⊕ opad) || D` for a digest `D` of 32 bytes. -/
theorem outerBlock (Q D : ByteArray) (hQ : Q.size = 64) (hD : D.size = 32) (t : Nat)
    (ht : t < 16) :
    SHS.SHA256.Impl.beU32 (paddedBlock (Q ++ D) 1) ⟨t, ht⟩ =
      if t < 8 then be4 (D.get! (4 * t + 0)) (D.get! (4 * t + 1)) (D.get! (4 * t + 2))
        (D.get! (4 * t + 3))
      else if t = 8 then 0x80000000 else if t = 15 then 768 else 0 := by
  have hs : (Q ++ D).size = 96 := by rw [ByteArray.size_append, hQ, hD]
  have hz : zerosCount (Q ++ D) = 23 := by unfold zerosCount; rw [hs]; decide
  have hsize : (implPaddedBytes (Q ++ D)).size = 128 := by
    rw [size_implPaddedBytes_eq, hs, hz]
  have hb : ∀ k, k < 4 → (implPaddedBytes (Q ++ D)).get! (64 + 4 * t + k) =
      if 64 + 4 * t + k < 96 then D.get! (4 * t + k)
      else if 64 + 4 * t + k = 96 then 0x80
      else if 64 + 4 * t + k < 96 + 1 + 23 then 0
      else (lengthBE64 ((96 : Nat).toUInt64 <<< 3)).get! (64 + 4 * t + k - (96 + 1 + 23)) := by
    intro k hk
    rw [get!_implPaddedBytes_eq _ _ (by rw [hsize]; omega), hs, hz]
    by_cases h : 64 + 4 * t + k < 96
    · rw [ite_eq_left h, ite_eq_left h, get!_append_right _ _ _ (by omega) (by omega), hQ,
        show 64 + 4 * t + k - 64 = 4 * t + k by omega]
    · rw [ite_eq_right h, ite_eq_right h]
  have hidx : ∀ k, 4 * (16 * 1 + t) + k = 64 + 4 * t + k := fun k => by omega
  rw [beU32_paddedBlock, paddedBE, hidx 0, hidx 1, hidx 2, hidx 3, hb 0 (by decide),
    hb 1 (by decide), hb 2 (by decide), hb 3 (by decide)]
  interval_cases t <;> simp [lengthBE64_get!_eq] <;> decide

theorem digest_bytes (h : Words8) :
    (⟨pair h.w0 h.w1, pair h.w2 h.w3, pair h.w4 h.w5, pair h.w6 h.w7⟩ : Words4).bytes 32 =
      extractDigest h.toVec32 := by
  apply Vector.ext
  intro i hi
  rw [Words4.bytes, Vector.getElem_ofFn]
  unfold extractDigest
  rw [Vector.getElem_ofFn]
  exact digestByte h i hi

/-- The outer hash value is the implementation's state after `(K_0 ⊕ opad) || D`, where `D` is
the digest of the inner message, whose state is `inner`. -/
theorem outer_toVec32 (key : Array UInt64) (kn : UInt64) (hk : kn.toNat < 2 ^ 61) (Y : ByteArray)
    (hY : Y.size < 2 ^ 61) (inner : Words8)
    (hI : inner.toVec32 = implSha256StateRefactored Y iv256.toVec32) :
    (compress roundConstants
        (compress roundConstants iv256 (xorBlock (keyBlock256 roundConstants key kn) 0x5c5c5c5c))
        ⟨inner.w0, inner.w1, inner.w2, inner.w3, inner.w4, inner.w5, inner.w6, inner.w7,
          0x80000000, 0, 0, 0, 0, 0, 0, 768⟩).toVec32 =
      implSha256StateRefactored (xorBytes (keyBytes256 (bytes key kn.toNat)) 0x5c ++
        digestBytes (SHS.SHA256.Impl.sha256 Y)) iv256.toVec32 := by
  have hD : SHS.SHA256.Impl.sha256 Y = extractDigest inner.toVec32 := by
    rw [impl_sha256_eq_refactored _ hY, hI, iv256_toVec32]
    rfl
  have hQ : (xorBytes (keyBytes256 (bytes key kn.toNat)) 0x5c).size = 64 * 1 := by
    rw [size_xorBytes, size_keyBytes256]
  have hB : (⟨inner.w0, inner.w1, inner.w2, inner.w3, inner.w4, inner.w5, inner.w6, inner.w7,
        0x80000000, 0, 0, 0, 0, 0, 0, 768⟩ : Words16).toVec32 =
      SHS.SHA256.Impl.toU32s (paddedBlock (xorBytes (keyBytes256 (bytes key kn.toNat)) 0x5c ++
        digestBytes (extractDigest inner.toVec32)) 1) := by
    apply Vector.ext
    intro t ht
    rw [SHS.SHA256.Impl.toU32s, Vector.getElem_ofFn,
      outerBlock _ _ (by omega) (size_digestBytes _) t ht]
    by_cases h8 : t < 8
    · rw [ite_eq_left h8, get!_digestBytes _ _ (by omega), get!_digestBytes _ _ (by omega),
        get!_digestBytes _ _ (by omega), get!_digestBytes _ _ (by omega), be4_digest _ t h8]
      interval_cases t <;> rfl
    · rw [ite_eq_right h8]
      interval_cases t <;> rfl
  unfold implSha256StateRefactored
  rw [foldl_append _ 1 hQ, size_digestBytes, fold_one, hD, show blockCount 32 = 1 by decide,
    fold_one, show (1 + 0 : Nat) = 1 from rfl, compress_toVec32, compress_toVec32,
    xorBlock_toVec32 key kn hk 0x5c 0x5c5c5c5c (by decide), hB]

/-- The digest bytes of the program are those of HMAC on the copied implementation. -/
theorem hmacSha256_bytes (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64)
    (hk : kn.toNat < 2 ^ 61) (hn : n.toNat + 64 < 2 ^ 61) :
    (hmacSha256 key kn msg n).bytes 32 = implHmac256 (bytes key kn.toNat) (bytes msg n.toNat) := by
  have hY : (xorBytes (keyBytes256 (bytes key kn.toNat)) 0x36 ++ bytes msg n.toNat).size <
      2 ^ 61 := by
    rw [ByteArray.size_append, size_xorBytes, size_keyBytes256, bytes_size]
    omega
  have hX : (xorBytes (keyBytes256 (bytes key kn.toNat)) 0x5c ++
      digestBytes (SHS.SHA256.Impl.sha256
        (xorBytes (keyBytes256 (bytes key kn.toNat)) 0x36 ++ bytes msg n.toNat))).size <
          2 ^ 61 := by
    rw [ByteArray.size_append, size_xorBytes, size_keyBytes256, size_digestBytes]
    decide
  unfold hmacSha256 hmacSha256With implHmac256
  simp only
  rw [digest_bytes, outer_toVec32 key kn hk _ hY _ (inner_toVec32 key kn msg n hk hn),
    impl_sha256_eq_refactored _ hX, iv256_toVec32]
  rfl

/-- HMAC-SHA-256 of the first `kn` bytes of `key` and the first `n` bytes of `msg` is the digest of
FIPS 198-1 on their bits. -/
theorem hmacSha256_spec (key : Array UInt64) (kn : UInt64) (msg : Array UInt64) (n : UInt64)
    (hk : kn.toNat < 2 ^ 61) (hn : n.toNat + 64 < 2 ^ 61) :
    digestBitVec ((hmacSha256 key kn msg n).bytes 32) =
      Spec.hmacSha256 (bits (bytes key kn.toNat)) (bits (bytes msg n.toNat)) := by
  rw [hmacSha256_bytes key kn msg n hk hn]
  exact implHmac256_spec _ _ (by rw [bytes_size]; exact hk) (by rw [bytes_size]; exact hn)

#print axioms hmacSha256_spec

end Library.Hashing.Hmac
