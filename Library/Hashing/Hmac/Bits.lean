import Library.Hashing.Hmac.Program
import Library.Hashing.Hmac.Spec
import Library.Hashing.Words.Proof
import Library.Hashing.Sha2.Equiv.Common.Bytes
import Library.Hashing.Sha2.Equiv.Common.FromBits
import Library.Hashing.Sha2.Equiv.SHA256.Padding.ByteDecoding

/-! Facts that the HMAC-SHA-256 and HMAC-SHA-512 proofs share.  The first part concerns the bits
of byte strings: their length, the bits of a concatenation, of appended zero bytes, and of a
byte-wise XOR, and the bits of a `Word.fromBits`.  `bits` is the body of `bytesToBitMessage` in
both the SHA-256 and the SHA-512 parts of the copied proofs.  The second part concerns the bytes
of a digest, the bytes of a short key block, and the program's `xorBlock`. -/

namespace Library.Hashing.Hmac

open SHS SHS.Equiv.Bytes SHS.Equiv.FromBits Library.Hashing.Words Library.Bytes

/-- The bits of the bytes of `B`, the most significant bit of each byte first. -/
def bits (B : ByteArray) : Message := B.data.toList.flatMap byteToBits

/-- The bytes of `K`, each XORed with `c`. -/
def xorBytes (K : ByteArray) (c : UInt8) : ByteArray := ⟨K.data.map (· ^^^ c)⟩

theorem size_xorBytes (K : ByteArray) (c : UInt8) : (xorBytes K c).size = K.size := by
  cases K
  simp [xorBytes, ByteArray.size]

theorem get!_xorBytes (K : ByteArray) (c : UInt8) (j : Nat) (hj : j < K.size) :
    (xorBytes K c).get! j = K.get! j ^^^ c := by
  rw [SHS.Equiv.ByteArray.get!_eq_getElem _ _ (by rw [size_xorBytes]; exact hj),
    SHS.Equiv.ByteArray.get!_eq_getElem _ _ hj]
  cases K
  simp [xorBytes, ByteArray.getElem_eq_getElem_data]

theorem length_flatMap_byteToBits : ∀ l : List UInt8, (l.flatMap byteToBits).length = 8 * l.length
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, byteToBits_length, length_flatMap_byteToBits l,
      List.length_cons]
    omega

theorem length_bits (B : ByteArray) : (bits B).length = 8 * B.size := by
  rw [bits, length_flatMap_byteToBits, Array.length_toList]
  rfl

theorem bits_append (A B : ByteArray) : bits (A ++ B) = bits A ++ bits B :=
  SHS.Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage_append A B

theorem bits_appendZeros (B : ByteArray) (k : Nat) :
    bits (SHS.Equiv.ByteArray.appendZeros B k) = bits B ++ List.replicate (8 * k) false :=
  SHS.Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage_appendZeros B k

theorem byteToBits_xor (a c : UInt8) :
    byteToBits (a ^^^ c) = List.zipWith (· ^^ ·) (byteToBits a) (byteToBits c) := by
  apply List.ext_getElem (by simp [byteToBits])
  intro j h1 h2
  simp [byteToBits, UInt8.toNat_xor, Nat.testBit_xor]

theorem bits_xorBytes (K : ByteArray) (c : UInt8) :
    bits (xorBytes K c) =
      Spec.xorBits (bits K) (List.replicate K.size (Spec.byteBits c)).flatten := by
  cases K with
  | mk d =>
    show (d.map (· ^^^ c)).toList.flatMap byteToBits =
      List.zipWith (· ^^ ·) (d.toList.flatMap byteToBits)
        (List.replicate d.size (byteToBits c)).flatten
    rw [Array.toList_map, ← Array.length_toList]
    generalize d.toList = l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.length_cons,
        List.replicate_succ, List.flatten_cons,
        List.zipWith_append (by rw [byteToBits_length, byteToBits_length]), ih, byteToBits_xor]

theorem natFromBits_testBit : ∀ (l : List Bool) (i : Nat) (hi : i < l.length),
    (natFromBits l).testBit i = l[l.length - 1 - i] := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro i hi; simp at hi
  | append_singleton L b ih =>
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    have e : natFromBits (L ++ [b]) = 2 * natFromBits L + (if b then 1 else 0) := by
      simp only [natFromBits, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e]
    rcases i with _ | i
    · have hb : (L ++ [b])[(L ++ [b]).length - 1 - 0]'(by simp) = b := by simp
      rw [hb, Nat.testBit_zero]
      cases b <;> simp
    · rw [Nat.testBit_succ,
        show (2 * natFromBits L + (if b then 1 else 0)) / 2 = natFromBits L by split <;> omega,
        ih i (by omega)]
      simp only [List.length_append, List.length_singleton]
      rw [List.getElem_append_left (by omega)]
      simp only [show L.length + 1 - 1 - (i + 1) = L.length - 1 - i by omega]

/-- The bits of a `Word.fromBits` of a list of its width are the list. -/
theorem bitsOf_fromBits (l : List Bool) {N : Nat} (hl : l.length = N) :
    Spec.bitsOf (Word.fromBits (n := N) l) = l := by
  apply List.ext_getElem (by simp [Spec.bitsOf, hl])
  intro j h1 h2
  simp only [Spec.bitsOf, List.getElem_map, List.getElem_reverse, List.getElem_range,
    List.length_range]
  rw [BitVec.getLsbD, fromBits_toNat_of_length_le l hl.le, natFromBits_testBit l _ (by omega)]
  simp only [hl, show N - 1 - (N - 1 - j) = j by omega]

/-- The bytes of a digest. -/
def digestBytes {k : Nat} (d : Vector UInt8 k) : ByteArray := ⟨d.toArray⟩

theorem size_digestBytes {k : Nat} (d : Vector UInt8 k) : (digestBytes d).size = k := by
  simp [digestBytes, ByteArray.size]

theorem get!_digestBytes {k : Nat} (d : Vector UInt8 k) (j : Nat) (hj : j < k) :
    (digestBytes d).get! j = d[j] := by
  rw [SHS.Equiv.ByteArray.get!_eq_getElem _ _ (by rw [size_digestBytes]; exact hj)]
  simp [digestBytes, ByteArray.getElem_eq_getElem_data]

/-- Byte `j` of the key block of a key of `kn` bytes in `key` that fits in one block: a key byte,
or zero after the key. -/
def keyByte (key : Array UInt64) (kn j : Nat) : UInt8 := if j < kn then byteAt key j else 0

theorem xorBlock_get (m : Words16) (c : UInt64) (t : Nat) (ht : t < 16) :
    (xorBlock m c).get t = m.get t ^^^ c := by
  interval_cases t <;> rfl

theorem fold_one {β : Type} (f : (i : Nat) → i < 1 → β → β) (init : β) :
    Nat.fold 1 f init = f 0 (by decide) init := rfl

end Library.Hashing.Hmac
