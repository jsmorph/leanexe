import Library.Hashing.Sha3.SpongeProof
import Library.Hashing.Words.Bytes

/-! The lane programs compute the SHA-3 functions of the transcription.  A message of `n` bytes is
`messageBits msg n`, the first `n` bytes of the packed array read least significant bit first in
each byte as `h2b` of Appendix B.1 reads them, and a digest's bytes are read in the same order.
For a message of fewer than `2^61` bytes, `sha3_224_spec`, `sha3_256_spec`, `sha3_384_spec`, and
`sha3_512_spec` state that the bits of the digest's bytes are the transcription's digest. -/

namespace Library.Hashing.Sha3.Proof

open Library.Hashing.Sha3 Library.Hashing.Sha3.Spec Library.Hashing.Sha3.RoundProof
  Library.Hashing.Sha3.SpongeProof Library.Hashing.Words Library.Bytes

/-- The bits of the first `n` bytes of `msg`, least significant first in each byte. -/
def messageBits (msg : Array UInt64) (n : Nat) : Bits :=
  bitsOfBytes ((List.range n).map (byteAt msg))

/-- The sponge of the transcription at a rate of `rw` words is the program's state after the
absorbing loop, followed by the squeeze of Algorithm 8, steps 7 to 10. -/
theorem sponge_absorb (msg : Array UInt64) (n rw sfx : UInt64) (suffix : Bits)
    (hrw0 : 0 < rw.toNat) (hrw : rw.toNat ≤ 25) (hn : n.toNat < 2 ^ 61)
    (hs : suffix.length ≤ 6)
    (hsfx : ∀ i, sfx.toNat.testBit i = (suffix ++ [true]).getD i false) (d : Nat) :
    sponge (keccakP 6 24) pad101 1600 (64 * rw.toNat) (messageBits msg n.toNat ++ suffix) d =
      squeeze (keccakP 6 24) (64 * rw.toNat) d (d / (64 * rw.toNat) + 1)
        (toBits (toState (absorb msg n rw sfx))) [] := by
  unfold sponge messageBits
  rw [padded_eq msg n rw sfx suffix hrw0 hrw hn hs hsfx, absorb_spec msg n rw sfx hrw _ rfl]
  simp only
  rw [show (paddedBits msg n sfx ((n / (8 * rw) + 1) * rw - 1)
      ((n / (8 * rw) + 1).toNat * (64 * rw.toNat))).length / (64 * rw.toNat) =
        (n / (8 * rw) + 1).toNat by
    simp only [paddedBits, List.length_map, List.length_range]
    exact Nat.mul_div_cancel _ (by omega)]

/-- A single pass of the squeeze gives `Trunc_d(S)` when `d ≤ r`. -/
theorem squeeze_one (f : Bits → Bits) {r d : Nat} (S : Bits) (hS : r ≤ S.length) (hd : d ≤ r) :
    squeeze f r d (d / r + 1) S [] = trunc d S := by
  rw [squeeze]
  simp only [List.nil_append, trunc, List.length_take, Nat.min_eq_left hS, hd, ↓reduceIte,
    List.take_take, Nat.min_eq_left hd]

/-- The bits of the first `k` bytes of words `ws` are the first `8 k` bits of the lanes when each
bit of `ws` below `8 k` is the lanes' bit. -/
theorem bits_digest (ws : Array UInt64) (k : Nat) (s : Lanes) (hk : 8 * k ≤ 1600)
    (h : ∀ t, t < 8 * k →
      bit ws[t / 64]! (t % 64) = bit ((laneList s).getD (t / 64) 0) (t % 64)) :
    bitsOfBytes (List.ofFn fun i : Fin k => byteAt ws i.val) =
      trunc (8 * k) (toBits (toState s)) := by
  apply ext_getD (by rw [length_bitsOfBytes, trunc, List.length_take, length_toBits]; simp; omega)
  intro t ht
  rw [length_bitsOfBytes, List.length_ofFn] at ht
  have htr : (trunc (8 * k) (toBits (toState s))).getD t false =
      (toBits (toState s)).getD t false := by
    simp [trunc, List.getD_eq_getElem?_getD, ht]
  rw [getD_bitsOfBytes _ (by simp; omega), htr, getD_lanes _ (by omega), ← h t ht]
  have : (List.ofFn fun i : Fin k => byteAt ws i.val).getD (t / 8) 0 = byteAt ws (t / 8) := by
    simp [List.getD_eq_getElem?_getD, show t / 8 < k by omega]
  rw [this, testBit_byteAt _ _ (by omega)]
  congr 2 <;> omega

/-- A suffix byte below 256 whose first eight bits are a string of at most eight bits holds that
string. -/
theorem sfx_bits (v : Nat) (L : Bits) (hv : v < 2 ^ 8) (hL : L.length ≤ 8)
    (h : ∀ i, i < 8 → v.testBit i = L.getD i false) :
    ∀ i, v.testBit i = L.getD i false := by
  intro i
  by_cases hi : i < 8
  · exact h i hi
  · rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega))),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem sfx_hash : ∀ i, (0x06 : UInt64).toNat.testBit i = ([false, true] ++ [true]).getD i false :=
  sfx_bits 6 _ (by decide) (by decide) (by decide)

/-- The digest of a hash function of FIPS 202 §6.1 at a rate of `rw` words and a length of `d`
bits, from the program's state after absorbing. -/
theorem keccak_hash (msg : Array UInt64) (n rw : UInt64) (c d : Nat) (hn : n.toNat < 2 ^ 61)
    (hrw0 : 0 < rw.toNat) (hrw : rw.toNat ≤ 25) (hc : 1600 - c = 64 * rw.toNat)
    (hd : d ≤ 64 * rw.toNat) :
    keccak c (messageBits msg n.toNat ++ [false, true]) d =
      trunc d (toBits (toState (absorb msg n rw 0x06))) := by
  rw [keccak, hc, sponge_absorb msg n rw 0x06 [false, true] hrw0 hrw hn (by decide) sfx_hash,
    squeeze_one _ _ (by rw [length_toBits]; omega) hd]

theorem sha3_256_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    bitsOfBytes ((sha3_256 msg n).bytes 32).toList = Spec.sha3_256 (messageBits msg n.toNat) := by
  rw [Spec.sha3_256, keccak_hash msg n 17 512 256 hn (by decide) (by decide) (by decide)
    (by decide), sha3_256, Words4.bytes, Vector.toList_ofFn]
  apply bits_digest _ 32 _ (by decide)
  intro t ht
  have : t / 64 < 4 := by omega
  generalize t / 64 = j at this ⊢
  interval_cases j <;> rfl

theorem sha3_224_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    bitsOfBytes ((sha3_224 msg n).bytes 28).toList = Spec.sha3_224 (messageBits msg n.toNat) := by
  rw [Spec.sha3_224, keccak_hash msg n 18 448 224 hn (by decide) (by decide) (by decide)
    (by decide), sha3_224, Words4.bytes, Vector.toList_ofFn]
  apply bits_digest _ 28 _ (by decide)
  intro t ht
  have : t / 64 < 4 := by omega
  have hlow : t / 64 = 3 → t % 64 < 32 := by omega
  generalize t / 64 = j at this hlow ⊢
  interval_cases j
  · rfl
  · rfl
  · rfl
  · have hz := hlow rfl
    have hm : bit 0xFFFFFFFF (t % 64) = true := by
      simp only [bit, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl,
        Nat.testBit_two_pow_sub_one, hz, decide_true]
    show bit ((absorb msg n 18 0x06).a3 &&& 0xFFFFFFFF) (t % 64) =
      bit (absorb msg n 18 0x06).a3 (t % 64)
    rw [bit_and, hm, Bool.and_true]

theorem sha3_384_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    bitsOfBytes (sha3_384 msg n).bytes.toList = Spec.sha3_384 (messageBits msg n.toNat) := by
  rw [Spec.sha3_384, keccak_hash msg n 13 768 384 hn (by decide) (by decide) (by decide)
    (by decide), sha3_384, Words6.bytes, Vector.toList_ofFn]
  apply bits_digest _ 48 _ (by decide)
  intro t ht
  have : t / 64 < 6 := by omega
  generalize t / 64 = j at this ⊢
  interval_cases j <;> rfl

theorem sha3_512_spec (msg : Array UInt64) (n : UInt64) (hn : n.toNat < 2 ^ 61) :
    bitsOfBytes (sha3_512 msg n).bytes.toList = Spec.sha3_512 (messageBits msg n.toNat) := by
  rw [Spec.sha3_512, keccak_hash msg n 9 1024 512 hn (by decide) (by decide) (by decide)
    (by decide), sha3_512, Words8.bytes, Vector.toList_ofFn]
  apply bits_digest _ 64 _ (by decide)
  intro t ht
  have : t / 64 < 8 := by omega
  generalize t / 64 = j at this ⊢
  interval_cases j <;> rfl

end Library.Hashing.Sha3.Proof
