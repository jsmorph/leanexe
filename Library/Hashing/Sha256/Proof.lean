import Library.Hashing.Sha256.CompressProof
import Library.Hashing.Sha256.PaddingProof

/-! SHA-256 and SHA-224 compute FIPS 180-4.  For a message of fewer than `2 ^ 61` bytes held in
`msg`, the digest bytes of `sha256 msg n`, read most significant bit first, are the digest that
`SHS.SHA256.sha256` of `Library.Hashing.Sha2.Spec` gives for the message's bits, and likewise for
SHA-224.  The proof shows that the 32-bit words of the program's state after each block are the
state of the copied implementation `SHS.SHA256.Impl`, so that its digest bytes are those of
`Impl.sha256`, and then applies `SHS.Equiv.SHA256.sha256_correct` and `sha224_correct`. -/

namespace Library.Hashing.Sha256

open Library.Hashing.Words
open SHS.Equiv.SHA256 SHS.Equiv.SHA256.Padding.Layout SHS.Equiv.SHA256.Padding.Equiv
  SHS.Equiv.SHA256.Padding.ByteDecoding SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Pipeline

theorem blocks_toNat (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    ((n >>> 6) + (if (n &&& 63) < 56 then 1 else 2) : UInt64).toNat = blockCount n.toNat := by
  have h6 : (n >>> 6).toNat = n.toNat / 64 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]
  have h63 : (n &&& 63).toNat = n.toNat % 64 := by
    rw [UInt64.toNat_and, show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  unfold blockCount
  by_cases h : n.toNat % 64 < 56
  · rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, h63]; exact h), ite_eq_left h,
      UInt64.toNat_add, h6]
    simp; omega
  · rw [ite_eq_right (by rw [UInt64.lt_iff_toNat_lt, h63]; exact h), ite_eq_right h,
      UInt64.toNat_add, h6]
    simp; omega

/-- Block `i` of the program's padded message after the prefix `pre` of `p` whole blocks is
block `p + i` of `implPaddedBlocks`. -/
theorem loadBlock_toVec32 (pre : ByteArray) (p : Nat) (hpre : pre.size = 64 * p)
    (msg : Array UInt64) (n len : UInt64) (hlen : len.toNat = 64 * p + n.toNat)
    (hl : len.toNat < 2 ^ 61) (i : Nat) (hi : i < blockCount n.toNat) :
    (loadBlock msg n len (UInt64.ofNat (16 * blockCount n.toNat - 1))
        (UInt64.ofNat i <<< 4)).toVec32 =
      SHS.SHA256.Impl.toU32s (paddedBlock (pre ++ bytes msg n.toNat) (p + i)) := by
  have hN : blockCount n.toNat ≤ n.toNat / 64 + 2 := by unfold blockCount; split <;> omega
  have key : ∀ k (hk : k < 16),
      (paddedWord msg n len (UInt64.ofNat (16 * blockCount n.toNat - 1))
          ((UInt64.ofNat i <<< 4) + UInt64.ofNat k)).toUInt32 =
        SHS.SHA256.Impl.beU32 (paddedBlock (pre ++ bytes msg n.toNat) (p + i)) ⟨k, hk⟩ := by
    intro k hk
    rw [base_add i k (by omega), paddedWord_eq pre p hpre _ _ _ hlen hl _ (by omega),
      beU32_paddedBlock]
    exact congrArg _ (by simp only; omega)
  have key0 : (paddedWord msg n len (UInt64.ofNat (16 * blockCount n.toNat - 1))
      (UInt64.ofNat i <<< 4)).toUInt32 =
        SHS.SHA256.Impl.beU32 (paddedBlock (pre ++ bytes msg n.toNat) (p + i)) 0 := by
    have := key 0 (by decide)
    rwa [show (UInt64.ofNat 0 : UInt64) = 0 from rfl, UInt64.add_zero] at this
  apply Vector.ext
  intro t ht
  rw [SHS.SHA256.Impl.toU32s, Vector.getElem_ofFn]
  interval_cases t <;>
    simp only [loadBlock, Words16.toVec32, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
  · exact key0
  all_goals exact key _ (by decide)

/-- The 32-bit words of the hash value that `hashFrom` reaches from `h` are the implementation's
after the blocks that follow the prefix `pre`. -/
theorem hashFrom_toVec32 (pre : ByteArray) (p : Nat) (hpre : pre.size = 64 * p) (h : Words8)
    (msg : Array UInt64) (n len : UInt64) (hlen : len.toNat = 64 * p + n.toNat)
    (hl : len.toNat < 2 ^ 61) :
    (hashFrom roundConstants h msg n len).toVec32 =
      Nat.fold (blockCount n.toNat) (fun i _ b => SHS.SHA256.Impl.compress b
        (SHS.SHA256.Impl.toU32s (paddedBlock (pre ++ bytes msg n.toNat) (p + i)))) h.toVec32 := by
  have hn : n.toNat < 2 ^ 61 := by omega
  unfold hashFrom
  dsimp only
  rw [LeanExe.loop, blocks_toNat n hn]
  have hlast : (((n >>> 6) + (if (n &&& 63) < 56 then (1 : UInt64) else 2)) <<< (4 : UInt64)) - 1 =
      UInt64.ofNat (16 * blockCount n.toNat - 1) := by
    apply UInt64.toNat_inj.mp
    have hb := blocks_toNat n hn
    have hN : blockCount n.toNat ≤ n.toNat / 64 + 2 := by unfold blockCount; split <;> omega
    have hN1 : 1 ≤ blockCount n.toNat := by unfold blockCount; split <;> omega
    rw [UInt64.toNat_sub_of_le, UInt64.toNat_shiftLeft, hb, UInt64.toNat_ofNat']
    · simp [Nat.shiftLeft_eq]; omega
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_shiftLeft, hb]; simp [Nat.shiftLeft_eq]; omega
  rw [hlast]
  have hk : ∀ k, k ≤ blockCount n.toNat →
      (Nat.fold k (fun i _ s => compress roundConstants s
          (loadBlock msg n len (UInt64.ofNat (16 * blockCount n.toNat - 1))
            (UInt64.ofNat i <<< 4))) h).toVec32 =
        Nat.fold k (fun i _ b => SHS.SHA256.Impl.compress b
          (SHS.SHA256.Impl.toU32s (paddedBlock (pre ++ bytes msg n.toNat) (p + i)))) h.toVec32 := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [Nat.fold_succ, Nat.fold_succ, compress_toVec32, ih (by omega),
        loadBlock_toVec32 pre p hpre _ _ _ hlen hl _ (by omega)]
  exact hk _ (Nat.le_refl _)

/-- Block `i` of the whole blocks of `pre`. -/
def preBlock (pre : ByteArray) (i : Nat) : Vector UInt8 64 :=
  Vector.ofFn fun (j : Fin 64) => pre.get! (i * 64 + j.val)

theorem paddedBlock_pre (pre : ByteArray) (p : Nat) (hpre : pre.size = 64 * p)
    (data : ByteArray) (i : Nat) (hi : i < p) :
    paddedBlock (pre ++ data) i = preBlock pre i := by
  apply Vector.ext
  intro j hj
  simp only [paddedBlock, preBlock, Vector.getElem_ofFn]
  rw [get!_implPaddedBytes_data _ _ (by rw [ByteArray.size_append]; omega),
    SHS.Equiv.ByteArray.get!_append_left _ _ _ (by omega)]

theorem fold_split {β : Type} (g : Nat → β → β) (init : β) (p : Nat) : ∀ N,
    Nat.fold (p + N) (fun i _ b => g i b) init =
      Nat.fold N (fun i _ b => g (p + i) b) (Nat.fold p (fun i _ b => g i b) init)
  | 0 => rfl
  | N + 1 => by rw [← Nat.add_assoc, Nat.fold_succ, Nat.fold_succ, fold_split g init p N]

/-- A fold over the padded blocks of `pre ++ data` is the fold over the blocks of `data` from the
fold over the `p` blocks of `pre`. -/
theorem foldl_append (pre : ByteArray) (p : Nat) (hpre : pre.size = 64 * p) (data : ByteArray)
    {β : Type} (c : β → Vector UInt8 64 → β) (init : β) :
    (implPaddedBlocks (pre ++ data)).foldl c init =
      Nat.fold (blockCount data.size) (fun i _ b => c b (paddedBlock (pre ++ data) (p + i)))
        (Nat.fold p (fun i _ b => c b (preBlock pre i)) init) := by
  have hp : ∀ k, k ≤ p →
      Nat.fold k (fun i _ b => c b (paddedBlock (pre ++ data) i)) init =
        Nat.fold k (fun i _ b => c b (preBlock pre i)) init := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.fold_zero, Nat.fold_zero]
    | succ k ih =>
      intro hk
      rw [Nat.fold_succ, Nat.fold_succ, ih (by omega), paddedBlock_pre pre p hpre data k (by omega)]
  rw [implPaddedBlocks_foldl, paddedSize pre p hpre,
    Nat.mul_div_cancel_left _ (by decide : 0 < 64),
    finFoldl_eq_fold _ (fun i b => c b (paddedBlock (pre ++ data) i)),
    fold_split (fun i b => c b (paddedBlock (pre ++ data) i)), hp p (Nat.le_refl _)]

/-- The 32-bit words of the program's final hash value of a message from the initial value `iv`
are the implementation's. -/
theorem hashFrom_iv (iv : Words8) (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    (hashFrom roundConstants iv msg n n).toVec32 =
      implSha256StateRefactored (bytes msg n.toNat) iv.toVec32 := by
  have e := foldl_append ByteArray.empty 0 rfl (bytes msg n.toNat)
    (fun s b => SHS.SHA256.Impl.compress s (SHS.SHA256.Impl.toU32s b)) iv.toVec32
  simp only [ByteArray.empty_append, Nat.fold_zero] at e
  rw [bytes_size] at e
  unfold implSha256StateRefactored
  rw [e, hashFrom_toVec32 ByteArray.empty 0 rfl iv msg n n (by simp) hn]
  simp only [ByteArray.empty_append]

theorem iv256_toVec32 : iv256.toVec32 = SHS.SHA256.Impl.H256_256 := rfl
theorem iv224_toVec32 : iv224.toVec32 = SHS.SHA256.Impl.H256_224 := rfl

/-- Byte `i` of the SHA-256 digest words, from the final hash value `h`, in the form in which
`SHS.SHA256.Impl` extracts digest bytes. -/
theorem digestByte (h : Words8) (i : Nat) (hi : i < 32) :
    byteAt #[pair h.w0 h.w1, pair h.w2 h.w3, pair h.w4 h.w5, pair h.w6 h.w7] i =
      ((h.toVec32[i / 4]'(by omega) >>> UInt32.ofNat ((3 - i % 4) * 8)) &&& 0xff).toUInt8 := by
  obtain ⟨q, r, rfl, hr⟩ : ∃ q r, i = 8 * q + r ∧ r < 8 := ⟨i / 8, i % 8, by omega, by omega⟩
  have hq : q < 4 := by omega
  rw [byteAt_eq _ _ _ hr]
  by_cases h4 : r < 4
  · simp only [show (8 * q + r) / 4 = 2 * q by omega, show (8 * q + r) % 4 = r by omega]
    interval_cases q
    · show byteOf (pair h.w0 h.w1) r = _
      rw [byteOf_pair_low _ _ _ h4, byte32_eq]; rfl
    · show byteOf (pair h.w2 h.w3) r = _
      rw [byteOf_pair_low _ _ _ h4, byte32_eq]; rfl
    · show byteOf (pair h.w4 h.w5) r = _
      rw [byteOf_pair_low _ _ _ h4, byte32_eq]; rfl
    · show byteOf (pair h.w6 h.w7) r = _
      rw [byteOf_pair_low _ _ _ h4, byte32_eq]; rfl
  · simp only [show (8 * q + r) / 4 = 2 * q + 1 by omega, show (8 * q + r) % 4 = r - 4 by omega,
      show 3 - (r - 4) = 7 - r by omega]
    interval_cases q
    · show byteOf (pair h.w0 h.w1) r = _
      rw [byteOf_pair_high _ _ _ (by omega) hr, byte32_eq]; rfl
    · show byteOf (pair h.w2 h.w3) r = _
      rw [byteOf_pair_high _ _ _ (by omega) hr, byte32_eq]; rfl
    · show byteOf (pair h.w4 h.w5) r = _
      rw [byteOf_pair_high _ _ _ (by omega) hr, byte32_eq]; rfl
    · show byteOf (pair h.w6 h.w7) r = _
      rw [byteOf_pair_high _ _ _ (by omega) hr, byte32_eq]; rfl

/-- Byte `i` of the SHA-224 digest words, from the final hash value `h`. -/
theorem digestByte224 (h : Words8) (i : Nat) (hi : i < 28) :
    byteAt #[pair h.w0 h.w1, pair h.w2 h.w3, pair h.w4 h.w5, bswap h.w6 >>> 32] i =
      ((h.toVec32[i / 4]'(by omega) >>> UInt32.ofNat ((3 - i % 4) * 8)) &&& 0xff).toUInt8 := by
  obtain ⟨q, r, rfl, hr⟩ : ∃ q r, i = 8 * q + r ∧ r < 8 := ⟨i / 8, i % 8, by omega, by omega⟩
  have hq : q < 4 := by omega
  rw [byteAt_eq _ _ _ hr]
  by_cases h3 : q = 3
  · subst h3
    have hr4 : r < 4 := by omega
    simp only [show (8 * 3 + r) / 4 = 6 by omega, show (8 * 3 + r) % 4 = r by omega]
    show byteOf (bswap h.w6 >>> 32) r = _
    rw [byteOf_high _ _ hr4, byte32_eq]
    rfl
  · have hq3 : q < 3 := by omega
    by_cases h4 : r < 4
    · simp only [show (8 * q + r) / 4 = 2 * q by omega, show (8 * q + r) % 4 = r by omega]
      interval_cases q
      · show byteOf (pair h.w0 h.w1) r = _
        rw [byteOf_pair_low _ _ _ h4, byte32_eq]; rfl
      · show byteOf (pair h.w2 h.w3) r = _
        rw [byteOf_pair_low _ _ _ h4, byte32_eq]; rfl
      · show byteOf (pair h.w4 h.w5) r = _
        rw [byteOf_pair_low _ _ _ h4, byte32_eq]; rfl
    · simp only [show (8 * q + r) / 4 = 2 * q + 1 by omega, show (8 * q + r) % 4 = r - 4 by omega,
        show 3 - (r - 4) = 7 - r by omega]
      interval_cases q
      · show byteOf (pair h.w0 h.w1) r = _
        rw [byteOf_pair_high _ _ _ (by omega) hr, byte32_eq]; rfl
      · show byteOf (pair h.w2 h.w3) r = _
        rw [byteOf_pair_high _ _ _ (by omega) hr, byte32_eq]; rfl
      · show byteOf (pair h.w4 h.w5) r = _
        rw [byteOf_pair_high _ _ _ (by omega) hr, byte32_eq]; rfl

theorem sha256_bytes (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    (sha256 msg n).bytes 32 = SHS.SHA256.Impl.sha256 (bytes msg n.toNat) := by
  rw [impl_sha256_eq_refactored _ (by rw [bytes_size]; exact hn)]
  unfold implSha256Refactored
  rw [← iv256_toVec32, ← hashFrom_iv _ _ _ hn]
  unfold sha256 sha256With extractDigest
  generalize hashFrom roundConstants iv256 msg n n = h
  apply Vector.ext
  intro i hi
  rw [Words4.bytes, Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact digestByte h i hi

theorem sha224_bytes (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    (sha224 msg n).bytes 28 = SHS.SHA256.Impl.sha224 (bytes msg n.toNat) := by
  rw [impl_sha224_eq_refactored _ (by rw [bytes_size]; exact hn)]
  unfold implSha224Refactored
  rw [← iv224_toVec32, ← hashFrom_iv _ _ _ hn]
  unfold sha224 sha224With extractDigest224
  generalize hashFrom roundConstants iv224 msg n n = h
  apply Vector.ext
  intro i hi
  rw [Words4.bytes, Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact digestByte224 h i hi

/-- SHA-256 of the bytes of `msg` is the digest of FIPS 180-4 §6.2. -/
theorem sha256_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    digestBitVec ((sha256 msg n).bytes 32) =
      SHS.SHA256.sha256 (bytesToBitMessage (bytes msg n.toNat))
        (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) := by
  rw [sha256_bytes msg n hn]
  exact sha256_correct _ (by rw [bytes_size]; exact hn)

/-- SHA-224 of the bytes of `msg` is the digest of FIPS 180-4 §6.3. -/
theorem sha224_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    digestBitVec224 ((sha224 msg n).bytes 28) =
      SHS.SHA256.sha224 (bytesToBitMessage (bytes msg n.toNat))
        (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) := by
  rw [sha224_bytes msg n hn]
  exact sha224_correct _ (by rw [bytes_size]; exact hn)

#print axioms sha256_spec
#print axioms sha224_spec

end Library.Hashing.Sha256
