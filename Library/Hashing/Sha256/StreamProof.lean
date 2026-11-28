module

public import Library.Hashing.Sha256.Stream
public import Library.Hashing.Sha256.Proof
public import LeanExe.Dialect.BytesLemmas
public import LeanExe.Dialect.Lemmas

@[expose] public section

/-! The block-level SHA-256 computes FIPS 180-4.  `blocksFold data q s` is the copied
implementation's hash value after the first `q` blocks of `data` from `s`.  `update_toVec32` states
that the 32-bit words of `update h b q` are `blocksFold` of the first `q` blocks of `b` from those
of `h`, since `byteBlock` reads the words of a block as `SHS.SHA256.Impl.toU32s` does
(`byteBlock_toVec32`) and `compress_toVec32` gives each compression.  `blocksFold_append` splits a
fold over a concatenation whose first part is whole blocks, and `blocksFold_append_tail` drops the
bytes after the blocks that a fold reads.  `finish_bytes` states that `finish` from the hash value
of a prefix of whole blocks gives the digest bytes of `Impl.sha256` of the prefix followed by the
bytes of the window that it hashes, through `hashFrom_toVec32` and the packing of `pack`
(`pack_bytes`), and `finish_spec` the digest of the transcription.  `stream_spec` composes them:
hashing pieces of whole blocks with `update` from `iv256` and the remaining bytes with `finish`
gives the digest of FIPS 180-4 of the concatenation.  `digestBitVec_inj` states that two digests
with the same bits are equal. -/

namespace Library.Hashing.Sha256

open Library.Hashing.Words Library.Bytes LeanExe.Bytes
open SHS.Equiv.SHA256 SHS.Equiv.SHA256.Padding.Layout SHS.Equiv.SHA256.Padding.Equiv
  SHS.Equiv.SHA256.Padding.ByteDecoding SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Pipeline

/-! ## Bytes -/

set_option maxHeartbeats 800000 in
/-- Four widened bytes joined by shifts, truncated to 32 bits, form `be4` of them. -/
theorem be4_widened (b0 b1 b2 b3 : UInt8) :
    ((b0.toUInt64 <<< 24) ||| (b1.toUInt64 <<< 16) ||| (b2.toUInt64 <<< 8) |||
      b3.toUInt64).toUInt32 = be4 b0 b1 b2 b3 := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be4, UInt64.toBitVec_toUInt32, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt32, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft,
    UInt8.toBitVec_toUInt64]
  interval_cases i <;> simp

set_option maxHeartbeats 1600000 in
/-- Eight widened bytes joined by shifts, the first least significant, form `be8` of the bytes in
the reverse order. -/
theorem le8_widened (x0 x1 x2 x3 x4 x5 x6 x7 : UInt8) :
    x0.toUInt64 ||| (x1.toUInt64 <<< 8) ||| (x2.toUInt64 <<< 16) ||| (x3.toUInt64 <<< 24) |||
      (x4.toUInt64 <<< 32) ||| (x5.toUInt64 <<< 40) ||| (x6.toUInt64 <<< 48) |||
      (x7.toUInt64 <<< 56) = be8 x7 x6 x5 x4 x3 x2 x1 x0 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [be8, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64]
  interval_cases i <;> simp

/-- Position `k` of word `i` of four bytes, for `k` below 4 and a word that ends within `2^64`
bytes. -/
theorem wordPos (i : Nat) (k : UInt64) (hk : k.toNat < 4) (hi : 4 * i + 4 ≤ 2 ^ 64) :
    ((UInt64.ofNat i <<< 2) + k).toNat = 4 * i + k.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    show UInt64.toNat 2 % 64 = 2 by decide, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : i * 2 ^ 2 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : i * 2 ^ 2 + k.toNat < 2 ^ 64)]
  omega

/-- `byteWord` reads the big-endian 32-bit word of four bytes. -/
theorem byteWord_toUInt32 (b : LeanExe.Bytes) (i : Nat) (hi : 4 * i + 4 ≤ 2 ^ 64) :
    (byteWord b (UInt64.ofNat i)).toUInt32 = be4 (b.data.get! (4 * i))
      (b.data.get! (4 * i + 1)) (b.data.get! (4 * i + 2)) (b.data.get! (4 * i + 3)) := by
  have p0 : (UInt64.ofNat i <<< 2).toNat = 4 * i := by
    have := wordPos i 0 (by decide) hi
    rwa [UInt64.add_zero] at this
  unfold byteWord
  dsimp only
  rw [get_eq_get!, get_eq_get!, get_eq_get!, get_eq_get!, p0, wordPos i 1 (by decide) hi,
    wordPos i 2 (by decide) hi, wordPos i 3 (by decide) hi]
  exact be4_widened _ _ _ _

/-- Block `j` that `byteBlock` reads is block `j` of the bytes, as the implementation parses it. -/
theorem byteBlock_toVec32 (b : LeanExe.Bytes) (j : Nat) (hj : 64 * j + 64 ≤ 2 ^ 64) :
    (byteBlock b (UInt64.ofNat j <<< 4)).toVec32 = SHS.SHA256.Impl.toU32s (preBlock b.data j) := by
  have key : ∀ k (hk : k < 16),
      (byteWord b ((UInt64.ofNat j <<< 4) + UInt64.ofNat k)).toUInt32 =
        SHS.SHA256.Impl.beU32 (preBlock b.data j) ⟨k, hk⟩ := by
    intro k hk
    rw [base_add j k (by omega), byteWord_toUInt32 b _ (by omega)]
    have e0 : 4 * (16 * j + k) = j * 64 + 4 * k := by omega
    have e1 : 4 * (16 * j + k) + 1 = j * 64 + (4 * k + 1) := by omega
    have e2 : 4 * (16 * j + k) + 2 = j * 64 + (4 * k + 2) := by omega
    have e3 : 4 * (16 * j + k) + 3 = j * 64 + (4 * k + 3) := by omega
    rw [e1, e2, e3, e0]
    simp only [SHS.SHA256.Impl.beU32, preBlock, Vector.getElem_ofFn, be4]
  have key0 : (byteWord b (UInt64.ofNat j <<< 4)).toUInt32 =
      SHS.SHA256.Impl.beU32 (preBlock b.data j) 0 := by
    have := key 0 (by decide)
    rwa [show (UInt64.ofNat 0 : UInt64) = 0 from rfl, UInt64.add_zero] at this
  apply Vector.ext
  intro t ht
  rw [SHS.SHA256.Impl.toU32s, Vector.getElem_ofFn]
  interval_cases t <;>
    simp only [byteBlock, Words16.toVec32, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ]
  · exact key0
  all_goals exact key _ (by decide)

/-! ## Folds over whole blocks -/

/-- The implementation's hash value after the first `q` blocks of `data`, from `s`. -/
def blocksFold (data : ByteArray) (q : Nat) (s : SHS.SHA256.Impl.State) : SHS.SHA256.Impl.State :=
  Nat.fold q
    (fun i _ acc => SHS.SHA256.Impl.compress acc (SHS.SHA256.Impl.toU32s (preBlock data i)))
    s

theorem blocksFold_zero (data : ByteArray) (s : SHS.SHA256.Impl.State) :
    blocksFold data 0 s = s := by
  unfold blocksFold
  rw [Nat.fold_zero]

theorem blocksFold_succ (data : ByteArray) (q : Nat) (s : SHS.SHA256.Impl.State) :
    blocksFold data (q + 1) s = SHS.SHA256.Impl.compress (blocksFold data q s)
      (SHS.SHA256.Impl.toU32s (preBlock data q)) := by
  unfold blocksFold
  rw [Nat.fold_succ]

/-- Folds over two byte arrays whose first `q` blocks agree agree. -/
theorem blocksFold_congr (d e : ByteArray) (s : SHS.SHA256.Impl.State) :
    ∀ q, (∀ i, i < q → preBlock d i = preBlock e i) →
      blocksFold d q s = blocksFold e q s := by
  intro q
  induction q with
  | zero => intro _; rw [blocksFold_zero, blocksFold_zero]
  | succ q ih =>
    intro same
    rw [blocksFold_succ, blocksFold_succ, ih (fun i hi => same i (by omega)),
      same q (by omega)]

/-- The 32-bit words of `update h b q` are the implementation's hash value after the first `q`
blocks of `b` from those of `h`. -/
theorem update_toVec32 (h : Words8) (b : LeanExe.Bytes) (q : UInt64) (hq : 64 * q.toNat ≤ 2 ^ 64) :
    (update h b q).toVec32 = blocksFold b.data q.toNat h.toVec32 := by
  unfold update updateWith
  rw [LeanExe.loop]
  have key : ∀ k, k ≤ q.toNat →
      (Nat.fold k (fun i _ s => compress roundConstants s
          (byteBlock b (UInt64.ofNat i <<< 4))) h).toVec32 = blocksFold b.data k h.toVec32 := by
    intro k
    induction k with
    | zero => intro _; rw [Nat.fold_zero, blocksFold_zero]
    | succ k ih =>
      intro hk
      rw [Nat.fold_succ, compress_toVec32, ih (by omega), byteBlock_toVec32 b k (by omega),
        blocksFold_succ]
  exact key _ le_rfl

theorem preBlock_append_left (pre c : ByteArray) (i : Nat) (hi : 64 * i + 64 ≤ pre.size) :
    preBlock (pre ++ c) i = preBlock pre i := by
  apply Vector.ext
  intro t ht
  simp only [preBlock, Vector.getElem_ofFn]
  exact SHS.Equiv.ByteArray.get!_append_left _ _ _ (by omega)

theorem preBlock_append_right (pre c : ByteArray) (p : Nat) (hpre : pre.size = 64 * p) (i : Nat) :
    preBlock (pre ++ c) (p + i) = preBlock c i := by
  apply Vector.ext
  intro t ht
  simp only [preBlock, Vector.getElem_ofFn]
  by_cases hin : i * 64 + t < c.size
  · rw [SHS.Equiv.ByteArray.get!_append_right _ _ _ (by rw [hpre]; nlinarith) (by
        rw [hpre]; rw [show (p + i) * 64 + t - 64 * p = i * 64 + t by rw [Nat.add_mul]; omega];
        exact hin),
      hpre, show (p + i) * 64 + t - 64 * p = i * 64 + t by rw [Nat.add_mul]; omega]
  · rw [get!_of_le _ (by rw [ByteArray.size_append, hpre]; rw [Nat.add_mul]; omega),
      get!_of_le _ (by omega)]

/-- The whole blocks of `pre ++ c`, where `pre` holds `p` whole blocks: those of `pre` and then
those of `c`. -/
theorem blocksFold_append (pre c : ByteArray) (p : Nat) (hpre : pre.size = 64 * p)
    (s : SHS.SHA256.Impl.State) :
    ∀ q, blocksFold (pre ++ c) (p + q) s = blocksFold c q (blocksFold pre p s) := by
  have left : ∀ i, i < p → preBlock (pre ++ c) i = preBlock pre i :=
    fun i hi => preBlock_append_left pre c i (by omega)
  have right : ∀ i, preBlock (pre ++ c) (p + i) = preBlock c i :=
    preBlock_append_right pre c p hpre
  generalize pre ++ c = whole at left right
  intro q
  induction q with
  | zero =>
    rw [Nat.add_zero, blocksFold_zero]
    exact blocksFold_congr whole pre s p left
  | succ q ih => rw [← Nat.add_assoc, blocksFold_succ, blocksFold_succ, ih, right q]

/-- A fold over the first `q` blocks reads no byte after them. -/
theorem blocksFold_append_tail (a t : ByteArray) (q : Nat) (hq : 64 * q ≤ a.size)
    (s : SHS.SHA256.Impl.State) : blocksFold (a ++ t) q s = blocksFold a q s :=
  blocksFold_congr _ _ s q fun i hi => preBlock_append_left a t i (by omega)

/-! ## The digest -/

/-- Position `k` of word `i` of eight bytes from `start`, for `k` below 8 and a word that ends
within `2^64` bytes. -/
theorem packPos (start : UInt64) (i : Nat) (k : UInt64) (hk : k.toNat < 8)
    (hi : start.toNat + 8 * i + 8 ≤ 2 ^ 64) :
    ((start + (UInt64.ofNat i <<< 3)) + k).toNat = start.toNat + 8 * i + k.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    show UInt64.toNat 3 % 64 = 3 by decide, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : i * 2 ^ 3 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : start.toNat + i * 2 ^ 3 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : start.toNat + i * 2 ^ 3 + k.toNat < 2 ^ 64)]
  omega

/-- `packWord` is the word whose bytes are those of `b` from `start + 8 i`, the first least
significant. -/
theorem packWord_eq (b : LeanExe.Bytes) (start : UInt64) (i : Nat)
    (hi : start.toNat + 8 * i + 8 ≤ 2 ^ 64) :
    packWord b start (UInt64.ofNat i) = be8 (b.data.get! (start.toNat + 8 * i + 7))
      (b.data.get! (start.toNat + 8 * i + 6)) (b.data.get! (start.toNat + 8 * i + 5))
      (b.data.get! (start.toNat + 8 * i + 4)) (b.data.get! (start.toNat + 8 * i + 3))
      (b.data.get! (start.toNat + 8 * i + 2)) (b.data.get! (start.toNat + 8 * i + 1))
      (b.data.get! (start.toNat + 8 * i)) := by
  have p0 : (start + (UInt64.ofNat i <<< 3)).toNat = start.toNat + 8 * i := by
    have := packPos start i 0 (by decide) hi
    rwa [UInt64.add_zero] at this
  unfold packWord
  dsimp only
  simp only [get_eq_get!]
  rw [p0, packPos start i 1 (by decide) hi, packPos start i 2 (by decide) hi,
    packPos start i 3 (by decide) hi, packPos start i 4 (by decide) hi,
    packPos start i 5 (by decide) hi, packPos start i 6 (by decide) hi,
    packPos start i 7 (by decide) hi]
  exact le8_widened _ _ _ _ _ _ _ _

/-- Byte `i` of the packed words of the `n` bytes of `b` from `start` is byte `start + i` of `b`. -/
theorem byteAt_pack (b : LeanExe.Bytes) (start n : UInt64)
    (hb : start.toNat + n.toNat + 8 < 2 ^ 64) (i : Nat) (hi : i < n.toNat) :
    byteAt (pack b start n) i = b.data.get! (start.toNat + i) := by
  have hcount : ((n + 7) >>> 3).toNat = (n.toNat + 7) / 8 := by
    have hlt : (n.toNat + 7) % 18446744073709551616 = n.toNat + 7 :=
      Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_shiftRight, UInt64.toNat_add]
    simp [Nat.shiftRight_eq_div_pow, hlt]
  obtain ⟨q, r, rfl, hr⟩ : ∃ q r, i = 8 * q + r ∧ r < 8 :=
    ⟨i / 8, i % 8, by omega, by omega⟩
  rw [byteAt_eq _ _ _ hr, show start.toNat + (8 * q + r) = start.toNat + 8 * q + r by omega]
  unfold pack
  rw [LeanExe.Dialect.build_get (by rw [hcount]; omega), packWord_eq b start q (by omega),
    byteOf_be8 _ _ _ _ _ _ _ _ _ hr]
  interval_cases r <;> rfl

/-- The packed bytes of `pack b start n` are the `n` bytes of `b` from `start`. -/
theorem pack_bytes (b : LeanExe.Bytes) (start n : UInt64)
    (hb : start.toNat + n.toNat + 8 < 2 ^ 64) (hw : start.toNat + n.toNat ≤ b.data.size) :
    bytes (pack b start n) n.toNat = b.data.extract start.toNat (start.toNat + n.toNat) := by
  apply ByteArray.ext
  apply Array.ext
  · show (bytes (pack b start n) n.toNat).size =
      (b.data.extract start.toNat (start.toNat + n.toNat)).size
    rw [bytes_size, ByteArray.size_extract]
    omega
  · intro i h1 h2
    have hi : i < n.toNat := by
      have := h1
      simp only [ByteArray.size_data, bytes_size] at this
      exact this
    have e : (bytes (pack b start n) n.toNat).data[i] = byteAt (pack b start n) i := by
      have general : ∀ j (hj : j < ((Array.range n.toNat).map (byteAt (pack b start n))).size),
          ((Array.range n.toNat).map (byteAt (pack b start n)))[j] = byteAt (pack b start n) j :=
        fun j hj => by simp
      exact general i _
    rw [e, byteAt_pack b start n hb i hi, get!_of_lt _ (by omega)]
    simp only [ByteArray.data_extract, Array.getElem_extract]
    rfl

/-- `finish` from the hash value of `p` whole blocks `pre`, with the `n` bytes of `b` from `start`
and the length of the whole message, gives the digest bytes of the implementation's SHA-256 of
`pre` followed by those bytes. -/
theorem finish_bytes (pre : ByteArray) (p : Nat) (hpre : pre.size = 64 * p) (h : Words8)
    (hh : h.toVec32 = blocksFold pre p SHS.SHA256.Impl.H256_256) (b : LeanExe.Bytes)
    (start n len : UInt64) (hw : start.toNat + n.toNat ≤ b.data.size)
    (hb : b.data.size + 8 < 2 ^ 64) (hlen : len.toNat = pre.size + n.toNat)
    (hl : len.toNat < 2 ^ 61) :
    (finish h b start n len).bytes 32 =
      SHS.SHA256.Impl.sha256 (pre ++ b.data.extract start.toNat (start.toNat + n.toNat)) := by
  have hE : (b.data.extract start.toNat (start.toNat + n.toNat)).size = n.toNat := by
    rw [ByteArray.size_extract]
    omega
  rw [impl_sha256_eq_refactored _ (by rw [ByteArray.size_append, hE]; omega)]
  unfold implSha256Refactored implSha256StateRefactored
  rw [foldl_append pre p hpre _, hE]
  have e := hashFrom_toVec32 pre p hpre h (pack b start n) n len (by omega) hl
  rw [pack_bytes b start n (by omega) hw, hh] at e
  unfold blocksFold at e
  rw [← e]
  unfold finish finishWith extractDigest
  generalize hashFrom roundConstants h (pack b start n) n len = g
  apply Vector.ext
  intro i hi
  rw [Words4.bytes, Vector.getElem_ofFn, Vector.getElem_ofFn]
  exact digestByte g i hi

/-- `finish` from the hash value of `p` whole blocks `pre` gives the digest of the transcription of
FIPS 180-4 for the bits of `pre` followed by the `n` bytes of `b` from `start`. -/
theorem finish_spec (pre : ByteArray) (p : Nat) (hpre : pre.size = 64 * p) (h : Words8)
    (hh : h.toVec32 = blocksFold pre p SHS.SHA256.Impl.H256_256) (b : LeanExe.Bytes)
    (start n len : UInt64) (hw : start.toNat + n.toNat ≤ b.data.size)
    (hb : b.data.size + 8 < 2 ^ 64) (hlen : len.toNat = pre.size + n.toNat)
    (hl : len.toNat < 2 ^ 61) :
    digestBitVec ((finish h b start n len).bytes 32) =
      SHS.SHA256.sha256
        (bytesToBitMessage (pre ++ b.data.extract start.toNat (start.toNat + n.toNat)))
        (bitLen_lt_of_size_lt _ (by rw [ByteArray.size_append, ByteArray.size_extract]; omega)) := by
  rw [finish_bytes pre p hpre h hh b start n len hw hb hlen hl]
  exact sha256_correct _ (by rw [ByteArray.size_append, ByteArray.size_extract]; omega)

/-! ## Distinct digests have distinct bits -/

theorem natFromBits_snoc (xs : List Bool) (y : Bool) :
    SHS.Equiv.FromBits.natFromBits (xs ++ [y]) =
      2 * SHS.Equiv.FromBits.natFromBits xs + (if y then 1 else 0) := by
  unfold SHS.Equiv.FromBits.natFromBits
  rw [List.foldl_append]
  rfl

/-- Bit lists of one length with one value are equal. -/
theorem natFromBits_inj : ∀ (xs ys : List Bool), xs.length = ys.length →
    SHS.Equiv.FromBits.natFromBits xs = SHS.Equiv.FromBits.natFromBits ys → xs = ys := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
    intro ys hl _
    exact (List.eq_nil_of_length_eq_zero hl.symm).symm
  | append_singleton xs x ih =>
    intro ys hl hv
    obtain ⟨ys', y, rfl⟩ : ∃ ys' y, ys = ys' ++ [y] := by
      cases ys using List.reverseRecOn with
      | nil => simp at hl
      | append_singleton ys' y _ => exact ⟨ys', y, rfl⟩
    rw [natFromBits_snoc, natFromBits_snoc] at hv
    have hxy : x = y := by
      cases x <;> cases y <;> simp at hv ⊢ <;> omega
    subst hxy
    have hrest : SHS.Equiv.FromBits.natFromBits xs = SHS.Equiv.FromBits.natFromBits ys' := by
      omega
    rw [ih ys' (by simp at hl; omega) hrest]

theorem byteToBits_inj (a b : UInt8) (h : SHS.Equiv.Bytes.byteToBits a =
    SHS.Equiv.Bytes.byteToBits b) : a = b := by
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have ha : (SHS.Equiv.Bytes.byteToBits a)[7 - i]'(by
        rw [SHS.Equiv.Bytes.byteToBits_length]; omega) = a.toNat.testBit i := by
      simp [SHS.Equiv.Bytes.byteToBits, List.getElem_reverse]
      congr 1
      omega
    have hb : (SHS.Equiv.Bytes.byteToBits b)[7 - i]'(by
        rw [SHS.Equiv.Bytes.byteToBits_length]; omega) = b.toNat.testBit i := by
      simp [SHS.Equiv.Bytes.byteToBits, List.getElem_reverse]
      congr 1
      omega
    rw [← ha, ← hb]
    congr 1
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega : 8 ≤ i))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le b.toNat_lt
        (Nat.pow_le_pow_right (by decide) (by omega : 8 ≤ i)))]

theorem flatMap_byteToBits_inj : ∀ (xs ys : List UInt8), xs.length = ys.length →
    xs.flatMap SHS.Equiv.Bytes.byteToBits = ys.flatMap SHS.Equiv.Bytes.byteToBits → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hl, h => by
    rw [List.flatMap_cons, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by
      rw [SHS.Equiv.Bytes.byteToBits_length, SHS.Equiv.Bytes.byteToBits_length])
    rw [byteToBits_inj x y h1, flatMap_byteToBits_inj xs ys (by simpa using hl) h2]

/-- Two digests with the same bits are equal. -/
theorem digestBitVec_inj (d e : Vector UInt8 32) (h : digestBitVec d = digestBitVec e) : d = e := by
  have hlen : ∀ v : Vector UInt8 32,
      (v.toList.flatMap SHS.Equiv.Bytes.byteToBits).length = 256 := by
    intro v
    rw [List.length_flatMap]
    simp [SHS.Equiv.Bytes.byteToBits_length]
  have hv := congrArg BitVec.toNat h
  unfold digestBitVec at hv
  rw [SHS.Equiv.FromBits.fromBits_toNat_of_length_le _ (by rw [hlen]),
    SHS.Equiv.FromBits.fromBits_toNat_of_length_le _ (by rw [hlen])] at hv
  have hbits := natFromBits_inj _ _ (by rw [hlen, hlen]) hv
  exact Vector.toList_inj.mp (flatMap_byteToBits_inj _ _ (by simp) hbits)

/-- The bytes of `pieces` one after another. -/
def joinAll (pieces : List LeanExe.Bytes) : ByteArray :=
  pieces.foldl (fun acc piece => acc ++ piece.data) ByteArray.empty

/-- Appending pieces does not shorten a byte array. -/
theorem joinFrom_size_le : ∀ (rest : List LeanExe.Bytes) (acc : ByteArray),
    acc.size ≤ (rest.foldl (fun a piece => a ++ piece.data) acc).size
  | [], _ => le_rfl
  | c :: rest, acc => by
    simp only [List.foldl_cons]
    exact le_trans (by rw [ByteArray.size_append]; omega) (joinFrom_size_le rest (acc ++ c.data))

/-- The bytes of `d` from its start to its end are `d`. -/
theorem extract_all (d : ByteArray) : d.extract 0 d.size = d := by
  apply ByteArray.ext
  simp

/-- Hashing pieces of whole blocks with `update` of all their blocks from `iv256`, and the bytes
`b` that follow them with `finish` and the length of the whole message, gives the digest of the
transcription of FIPS 180-4 for the bits of the pieces followed by `b`. -/
theorem stream_spec (pieces : List LeanExe.Bytes) (whole : ∀ c ∈ pieces, c.data.size % 64 = 0)
    (b : LeanExe.Bytes) (len : UInt64)
    (hlen : len.toNat = (joinAll pieces).size + b.data.size) (hl : len.toNat < 2 ^ 61) :
    digestBitVec ((finish (pieces.foldl (fun h c => update h c (c.size >>> 6)) iv256) b 0 b.size
      len).bytes 32) =
      SHS.SHA256.sha256 (bytesToBitMessage (joinAll pieces ++ b.data))
        (bitLen_lt_of_size_lt _ (by rw [ByteArray.size_append]; omega)) := by
  have key : ∀ (rest : List LeanExe.Bytes) (acc : ByteArray) (h : Words8),
      (∀ c ∈ rest, c.data.size % 64 = 0) → acc.size % 64 = 0 →
      (rest.foldl (fun a piece => a ++ piece.data) acc).size < 2 ^ 61 →
      h.toVec32 = blocksFold acc (acc.size / 64) SHS.SHA256.Impl.H256_256 →
      (rest.foldl (fun a piece => a ++ piece.data) acc).size % 64 = 0 ∧
        (rest.foldl (fun h c => update h c (c.size >>> 6)) h).toVec32 =
          blocksFold (rest.foldl (fun a piece => a ++ piece.data) acc)
          ((rest.foldl (fun a piece => a ++ piece.data) acc).size / 64)
          SHS.SHA256.Impl.H256_256 := by
    intro rest
    induction rest with
    | nil => intro acc h _ hacc _ hh; exact ⟨hacc, hh⟩
    | cons c rest ih =>
      intro acc h hrest hacc hsize hh
      simp only [List.foldl_cons] at hsize ⊢
      have hgrow := joinFrom_size_le rest (acc ++ c.data)
      have hc := hrest c (List.mem_cons_self ..)
      have hcs : c.data.size < 2 ^ 64 := by rw [ByteArray.size_append] at hgrow; omega
      have hq : (c.size >>> 6).toNat = c.data.size / 64 := by
        rw [UInt64.toNat_shiftRight, LeanExe.Bytes.size_toNat c hcs]
        simp [Nat.shiftRight_eq_div_pow]
      refine ih (acc ++ c.data) (update h c (c.size >>> 6))
        (fun d hd => hrest d (List.mem_cons_of_mem _ hd))
        (by rw [ByteArray.size_append]; omega) hsize ?_
      rw [update_toVec32 h c _ (by rw [hq]; omega), hq, hh,
        ← blocksFold_append acc c.data (acc.size / 64) (by omega), ByteArray.size_append]
      congr 1
      omega
  have hj : joinAll pieces =
      pieces.foldl (fun a piece => a ++ piece.data) ByteArray.empty := rfl
  obtain ⟨hwhole, hstate⟩ :=
    key pieces ByteArray.empty iv256 whole rfl (by rw [← hj]; omega)
      (by rw [show ByteArray.empty.size / 64 = 0 from rfl, blocksFold_zero]; rfl)
  rw [← hj] at hwhole hstate
  have hs : b.size.toNat = b.data.size := LeanExe.Bytes.size_toNat b (by omega)
  have e := finish_spec (joinAll pieces) ((joinAll pieces).size / 64) (by omega) _ hstate b 0 b.size
    len (by rw [hs]; simp) (by omega) (by rw [hs]; exact hlen) hl
  simp only [UInt64.toNat_zero, Nat.zero_add, hs, extract_all] at e
  exact e

end Library.Hashing.Sha256

#print axioms Library.Hashing.Sha256.stream_spec
#print axioms Library.Hashing.Sha256.finish_spec
#print axioms Library.Hashing.Sha256.update_toVec32
#print axioms Library.Hashing.Sha256.digestBitVec_inj
