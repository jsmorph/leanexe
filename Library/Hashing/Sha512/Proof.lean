import Library.Hashing.Sha512.CompressProof
import Library.Hashing.Sha512.PaddingProof
import Library.Hashing.Sha2.Equiv.SHA512.Main

/-! The SHA-512 family computes FIPS 180-4.  For a message of fewer than `2 ^ 61` bytes held in
`msg`, the digest bytes of `sha512 msg n`, read most significant bit first, are the digest that
`SHS.SHA512.sha512` of `Library.Hashing.Sha2.Spec` gives for the message's bits, and likewise for
SHA-384, SHA-512/256, and SHA-512/224.  The proof shows that the program's state after each
block is that of the copied implementation `SHS.SHA512.Impl`, so that its digest bytes are those
of `Impl.sha512`, and then applies `SHS.Equiv.SHA512.sha512_correct` and its companions. -/

namespace Library.Hashing.Sha512

open Library.Hashing.Words
open SHS.Equiv.SHA512 SHS.Equiv.SHA512.Padding.Layout SHS.Equiv.SHA512.Padding.Equiv
  SHS.Equiv.SHA512.Padding.ByteDecoding SHS.Equiv.SHA512.Digest SHS.Equiv.SHA512.Pipeline

theorem blocks_toNat (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    ((n >>> 7) + (if (n &&& 127) < 112 then 1 else 2) : UInt64).toNat = blockCount n.toNat := by
  have h7 : (n >>> 7).toNat = n.toNat / 128 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have h127 : (n &&& 127).toNat = n.toNat % 128 := by
    rw [UInt64.toNat_and, show (127 : UInt64).toNat = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  unfold blockCount
  by_cases h : n.toNat % 128 < 112
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, h127]; exact h), ite_eq_left h, UInt64.toNat_add, h7]
    simp; omega
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, h127]; exact h), ite_eq_right h, UInt64.toNat_add, h7]
    simp; omega

/-- Block `i` of the program's padded message is block `i` of `implPaddedBlocks`. -/
theorem loadBlock_toVec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) (i : Nat)
    (hi : i < blockCount n.toNat) :
    (loadBlock msg n (UInt64.ofNat (16 * blockCount n.toNat - 1)) (UInt64.ofNat i <<< 4)).toVec =
      SHS.SHA512.Impl.toU64s (paddedBlock (bytes msg n.toNat) i) := by
  have hN : blockCount n.toNat ≤ n.toNat / 128 + 2 := by unfold blockCount; split <;> omega
  have key : ∀ k (hk : k < 16),
      paddedWord msg n (UInt64.ofNat (16 * blockCount n.toNat - 1))
          ((UInt64.ofNat i <<< 4) + UInt64.ofNat k) =
        SHS.SHA512.Impl.beU64 (paddedBlock (bytes msg n.toNat) i) ⟨k, hk⟩ := by
    intro k hk
    rw [base_add i k (by omega), paddedWord_eq _ _ hn _ (by omega), beU64_paddedBlock]
  have key0 : paddedWord msg n (UInt64.ofNat (16 * blockCount n.toNat - 1))
      (UInt64.ofNat i <<< 4) = SHS.SHA512.Impl.beU64 (paddedBlock (bytes msg n.toNat) i) 0 := by
    have := key 0 (by decide)
    rwa [show (UInt64.ofNat 0 : UInt64) = 0 from rfl, UInt64.add_zero] at this
  apply Vector.ext
  intro t ht
  rw [SHS.SHA512.Impl.toU64s, Vector.getElem_ofFn]
  interval_cases t <;>
    simp only [loadBlock, Words16.toVec, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
  · exact key0
  all_goals exact key _ (by decide)

/-- The program's final hash value is that of the copied implementation. -/
theorem hashWith_toVec (iv : Words8) (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    (hashWith roundConstants iv msg n).toVec =
      implSha512StateRefactored (bytes msg n.toNat) iv.toVec := by
  unfold hashWith implSha512StateRefactored
  rw [implPaddedBlocks_foldl, paddedSize, Nat.mul_div_cancel_left _ (by decide : 0 < 128),
    finFoldl_eq_fold _ (fun i b => SHS.SHA512.Impl.compress b
      (SHS.SHA512.Impl.toU64s (paddedBlock (bytes msg n.toNat) i)))]
  dsimp only
  rw [LeanExe.loop, blocks_toNat n hn]
  have hlast : (((n >>> 7) + (if (n &&& 127) < 112 then (1 : UInt64) else 2)) <<< (4 : UInt64)) - 1 =
      UInt64.ofNat (16 * blockCount n.toNat - 1) := by
    apply UInt64.toNat_inj.mp
    have hb := blocks_toNat n hn
    have hN : blockCount n.toNat ≤ n.toNat / 128 + 2 := by unfold blockCount; split <;> omega
    have hN1 : 1 ≤ blockCount n.toNat := by unfold blockCount; split <;> omega
    rw [UInt64.toNat_sub_of_le, UInt64.toNat_shiftLeft, hb, UInt64.toNat_ofNat']
    · simp [Nat.shiftLeft_eq]; omega
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_shiftLeft, hb]; simp [Nat.shiftLeft_eq]; omega
  rw [hlast]
  have hk : ∀ k, k ≤ blockCount n.toNat →
      (Nat.fold k (fun i _ h => compress roundConstants h
          (loadBlock msg n (UInt64.ofNat (16 * blockCount n.toNat - 1))
            (UInt64.ofNat i <<< 4))) iv).toVec =
        Nat.fold k (fun i _ b => SHS.SHA512.Impl.compress b
          (SHS.SHA512.Impl.toU64s (paddedBlock (bytes msg n.toNat) i))) iv.toVec := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Nat.fold_succ, Nat.fold_succ, compress_toVec, ih (by omega),
        loadBlock_toVec _ _ hn _ (by omega)]
  exact hk _ (Nat.le_refl _)

/-- Byte `i` of digest words whose word `i / 8` is `bswap h[i / 8]`, in the form in which
`SHS.SHA512.Impl` extracts digest bytes from the hash value `h`. -/
theorem byteAt_bswap (ws : Array UInt64) (h : SHS.SHA512.Impl.State) (i : Nat) (hi : i / 8 < 8)
    (hw : ws[i / 8]! = bswap h[i / 8]) :
    byteAt ws i = ((h[i / 8] >>> UInt64.ofNat ((7 - i % 8) * 8)) &&& 0xff).toUInt8 := by
  show byteOf ws[i / 8]! (i % 8) = _
  rw [hw, byteOf_bswap _ _ (Nat.mod_lt _ (by decide)), byteOf_eq]

/-- `byteAt_bswap` for a word whose high four bytes are cleared, at its low four bytes. -/
theorem byteAt_bswap_low (ws : Array UInt64) (h : SHS.SHA512.Impl.State) (i : Nat)
    (hi : i / 8 < 8) (hr : i % 8 < 4) (hw : ws[i / 8]! = bswap h[i / 8] &&& 0xFFFFFFFF) :
    byteAt ws i = ((h[i / 8] >>> UInt64.ofNat ((7 - i % 8) * 8)) &&& 0xff).toUInt8 := by
  show byteOf ws[i / 8]! (i % 8) = _
  rw [hw, byteOf_low _ _ hr, byteOf_bswap _ _ (Nat.mod_lt _ (by decide)), byteOf_eq]

theorem words8_get (h : Words8) (q : Nat) (hq : q < 8) :
    (#[bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3, bswap h.w4, bswap h.w5, bswap h.w6,
      bswap h.w7] : Array UInt64)[q]! = bswap (h.toVec[q]'hq) := by
  interval_cases q <;> rfl

theorem words6_get (h : Words8) (q : Nat) (hq : q < 6) :
    (#[bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3, bswap h.w4, bswap h.w5] :
      Array UInt64)[q]! = bswap (h.toVec[q]'(by omega)) := by
  interval_cases q <;> rfl

theorem words4_get (h : Words8) (q : Nat) (hq : q < 4) :
    (#[bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3] : Array UInt64)[q]! =
      bswap (h.toVec[q]'(by omega)) := by
  interval_cases q <;> rfl

theorem words224_last (h : Words8) (q : Nat) (hq : q = 3) :
    (#[bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3 &&& 0xFFFFFFFF] : Array UInt64)[q]! =
      bswap (h.toVec[q]'(by omega)) &&& 0xFFFFFFFF := by
  subst hq; rfl

theorem words224_get (h : Words8) (q : Nat) (hq : q < 3) :
    (#[bswap h.w0, bswap h.w1, bswap h.w2, bswap h.w3 &&& 0xFFFFFFFF] : Array UInt64)[q]! =
      bswap (h.toVec[q]'(by omega)) := by
  interval_cases q <;> rfl

theorem iv512_toVec : iv512.toVec = SHS.SHA512.Impl.H0_512 := rfl
theorem iv384_toVec : iv384.toVec = SHS.SHA512.Impl.H0_384 := rfl
theorem iv512_256_toVec : iv512_256.toVec = SHS.SHA512.Impl.H0_512_256 := rfl
theorem iv512_224_toVec : iv512_224.toVec = SHS.SHA512.Impl.H0_512_224 := rfl

theorem sha512_bytes (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    (sha512 msg n).bytes = SHS.SHA512.Impl.sha512 (bytes msg n.toNat) := by
  rw [impl_sha512_eq_refactored _ (by rw [bytes_size]; exact hn)]
  unfold implSha512Refactored
  rw [← iv512_toVec, ← hashWith_toVec _ _ _ hn]
  unfold sha512 sha512With
  generalize hashWith roundConstants iv512 msg n = h
  apply Vector.ext
  intro i hi
  rw [Words8.bytes, Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact byteAt_bswap _ h.toVec i (by omega) (words8_get h (i / 8) (by omega))

theorem sha384_bytes (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    (sha384 msg n).bytes = SHS.SHA512.Impl.sha384 (bytes msg n.toNat) := by
  rw [impl_sha384_eq_refactored _ (by rw [bytes_size]; exact hn)]
  unfold implSha384Refactored
  rw [← iv384_toVec, ← hashWith_toVec _ _ _ hn]
  unfold sha384 sha384With
  generalize hashWith roundConstants iv384 msg n = h
  apply Vector.ext
  intro i hi
  rw [Words6.bytes, Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact byteAt_bswap _ h.toVec i (by omega) (words6_get h (i / 8) (by omega))

theorem sha512_256_bytes (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    (sha512_256 msg n).bytes 32 = SHS.SHA512.Impl.sha512_256 (bytes msg n.toNat) := by
  rw [impl_sha512_256_eq_refactored _ (by rw [bytes_size]; exact hn)]
  unfold implSha512_256Refactored
  rw [← iv512_256_toVec, ← hashWith_toVec _ _ _ hn]
  unfold sha512_256 sha512_256With
  generalize hashWith roundConstants iv512_256 msg n = h
  apply Vector.ext
  intro i hi
  rw [Words4.bytes, Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact byteAt_bswap _ h.toVec i (by omega) (words4_get h (i / 8) (by omega))

theorem sha512_224_bytes (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    (sha512_224 msg n).bytes 28 = SHS.SHA512.Impl.sha512_224 (bytes msg n.toNat) := by
  rw [impl_sha512_224_eq_refactored _ (by rw [bytes_size]; exact hn)]
  unfold implSha512_224Refactored
  rw [← iv512_224_toVec, ← hashWith_toVec _ _ _ hn]
  unfold sha512_224 sha512_224With
  generalize hashWith roundConstants iv512_224 msg n = h
  apply Vector.ext
  intro i hi
  rw [Words4.bytes, Vector.getElem_ofFn, Vector.getElem_ofFn]
  by_cases h3 : i / 8 < 3
  · exact byteAt_bswap _ h.toVec i (by omega) (words224_get h (i / 8) h3)
  · exact byteAt_bswap_low _ h.toVec i (by omega) (by omega) (words224_last h (i / 8) (by omega))

/-- SHA-512 of the bytes of `msg` is the digest of FIPS 180-4 §6.4. -/
theorem sha512_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    digestBitVec512 (sha512 msg n).bytes =
      SHS.SHA512.sha512 (bytesToBitMessage (bytes msg n.toNat))
        (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) := by
  rw [sha512_bytes msg n hn]
  exact sha512_correct _ (by rw [bytes_size]; exact hn)

/-- SHA-384 of the bytes of `msg` is the digest of FIPS 180-4 §6.5. -/
theorem sha384_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    digestBitVec384 (sha384 msg n).bytes =
      SHS.SHA512.sha384 (bytesToBitMessage (bytes msg n.toNat))
        (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) := by
  rw [sha384_bytes msg n hn]
  exact sha384_correct _ (by rw [bytes_size]; exact hn)

/-- SHA-512/256 of the bytes of `msg` is the digest of FIPS 180-4 §6.7. -/
theorem sha512_256_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    digestBitVec512_256 ((sha512_256 msg n).bytes 32) =
      SHS.SHA512.sha512_256 (bytesToBitMessage (bytes msg n.toNat))
        (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) := by
  rw [sha512_256_bytes msg n hn]
  exact sha512_256_correct _ (by rw [bytes_size]; exact hn)

/-- SHA-512/224 of the bytes of `msg` is the digest of FIPS 180-4 §6.6. -/
theorem sha512_224_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    digestBitVec512_224 ((sha512_224 msg n).bytes 28) =
      SHS.SHA512.sha512_224 (bytesToBitMessage (bytes msg n.toNat))
        (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) := by
  rw [sha512_224_bytes msg n hn]
  exact sha512_224_correct _ (by rw [bytes_size]; exact hn)

#print axioms sha512_spec
#print axioms sha384_spec
#print axioms sha512_256_spec
#print axioms sha512_224_spec

end Library.Hashing.Sha512
