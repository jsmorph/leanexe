import Library.Hashing.Sha2.Equiv.SHA256.Padding.Layout
import Library.Hashing.Sha2.Equiv.Common.Bytes
import Library.Hashing.Sha2.Spec.Preprocessing

/-! # SHA-256 padding: byte → bit decoding

`bytesToBitMessage` decodes a `ByteArray` into the spec's `Message`
(`List Bool`, MSB-first within each byte).  This file collects the
distributivity laws of `bytesToBitMessage` over `++` / `push 0x80` /
`appendZeros` / `lengthBE64`, plus the headline lemma
`bytesToBitMessage_implPaddedBytes` that bridges the byte-level
streaming pad to the spec's `SHS.SHA1.pad ∘ bytesToBitMessage`.

Follows FIPS 180-4 §5.1.1 (SHA-256 padding: append `1`-bit, then zero
bits, then a 64-bit big-endian length). -/

open SHS.Equiv.Bytes
open SHS.Equiv.ByteArray
open SHS.Equiv.SHA256.Padding.Layout

open SHS.SHA256

namespace SHS.Equiv.SHA256.Padding.ByteDecoding

open scoped SHS.SHA256

/-- Decode a `ByteArray` into the spec's `Message` (List Bool, MSB-first
within each byte). -/
def bytesToBitMessage (data : ByteArray) : SHS.Message :=
  data.data.toList.flatMap fun b => byteToBits b

/-- `bytesToBitMessage` distributes over `ByteArray.append`. -/
theorem bytesToBitMessage_append (a b : ByteArray) :
    bytesToBitMessage (a ++ b) =
      bytesToBitMessage a ++ bytesToBitMessage b := by
  unfold bytesToBitMessage
  simp

/-- Pushing the `0x80` separator appends the eight bits
`[true, false, …, false]` (MSB-first). -/
theorem bytesToBitMessage_push_0x80 (data : ByteArray) :
    bytesToBitMessage (data.push 0x80) =
      bytesToBitMessage data ++
        [true, false, false, false, false, false, false, false] := by
  unfold bytesToBitMessage
  simp
  unfold byteToBits
  decide

/-- `appendZeros` appends `8 * k` `false` bits. -/
theorem bytesToBitMessage_appendZeros (bs : ByteArray) (k : Nat) :
    bytesToBitMessage (appendZeros bs k) =
      bytesToBitMessage bs ++ List.replicate (8 * k) false := by
  unfold bytesToBitMessage
  induction k with
  | zero => simp [appendZeros]
  | succ k ih =>
    rw [appendZeros]
    simp [Array.toList_push]
    show List.flatMap
      (fun b => byteToBits b) (appendZeros bs k).data.toList ++ byteToBits 0 =
      List.flatMap (fun b => byteToBits b) bs.data.toList ++ List.replicate (8 * (k + 1)) false
    rw [ih]
    rw [List.append_assoc]
    rw [Nat.mul_succ]
    rw [← List.replicate_append_replicate]
    congr

/-- `lengthBE64` decodes to the 64-bit big-endian bit list of `bits`. -/
theorem bytesToBitMessage_lengthBE64 (bits : UInt64) :
    bytesToBitMessage (lengthBE64 bits) =
      (List.range 64).reverse.map bits.toNat.testBit := by
  unfold lengthBE64
  simp [List.range', List.foldl, bytesToBitMessage, byteToBits,
        List.range, List.range.loop]
  simp +arith only [show (256 : Nat) = 2 ^ 8 from rfl,
        Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.reduceAdd]
  simp +decide

/-- The byte-length encoded in `lengthBE64 (data.size.toUInt64 <<< 3)`
matches `(8 * data.size)` bit-by-bit, provided `data.size < 2^61`.

The bound `data.size < 2^61` is exactly what makes
`8 * data.size < 2^64`, so the FIPS 180-4 §5.1.1 bit-length suffix fits
in a single `UInt64` without wraparound. -/
theorem testBit_totalBits (data : ByteArray) (h : data.size < 2 ^ 61) (i : Nat) :
    (data.size.toUInt64 <<< 3).toNat.testBit i = (8 * data.size).testBit i := by
  congr 1
  rw [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have h1 : data.size % 2 ^ 64 = data.size := Nat.mod_eq_of_lt (by omega)
  have h3 : (UInt64.toNat 3) % 64 = 3 := by decide
  rw [h1, h3]
  show data.size <<< 3 % 2 ^ 64 = 8 * data.size
  rw [show data.size <<< 3 = data.size * 8 from by simp [Nat.shiftLeft_eq]]
  rw [Nat.mul_comm 8, Nat.mod_eq_of_lt]
  omega

/-- Streaming pad ↔ spec `pad`.  Combine the four distributivity steps
plus a case-split on `data.size % 64 < 56`.

The bound `data.size < 2^61` ensures `8 * data.size < 2^64` so the
FIPS 180-4 §5.1.1 64-bit bit-length suffix fits in a `UInt64`. -/
theorem bytesToBitMessage_implPaddedBytes
    (data : ByteArray) (h : data.size < 2 ^ 61) :
    bytesToBitMessage (implPaddedBytes data) =
      SHS.SHA1.pad (bytesToBitMessage data) := by
  have hLen : (bytesToBitMessage data).length = 8 * data.size := by
    simp only [bytesToBitMessage, byteToBits, List.length_flatMap, List.length_map,
      List.length_reverse, List.length_range]
    rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl, List.map_const,
      List.sum_replicate_nat]
    show data.data.toList.length * 8 = 8 * data.size
    rw [Array.length_toList, Nat.mul_comm]
    rfl
  have hTB : (fun i => (data.size.toUInt64 <<< 3).toNat.testBit i) =
             ((8 * data.size).testBit) := by
    funext i; exact testBit_totalBits data h i
  unfold implPaddedBytes SHS.SHA1.pad SHS.SHA256.pad
  simp only [bytesToBitMessage_append, bytesToBitMessage_appendZeros,
    bytesToBitMessage_push_0x80, bytesToBitMessage_lengthBE64, hLen, hTB]
  set z := zerosCount data with hz_eq
  unfold zerosCount at hz_eq
  rw [show ([true, false, false, false, false, false, false, false] : List Bool) =
      [true] ++ List.replicate 7 false from by decide]
  simp only [List.append_assoc, List.replicate_append_replicate]
  have hRange : 7 + 8 * z < 512 := by rw [hz_eq]; split <;> omega
  have hr : data.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have h8mod : 8 * data.size % 512 = 8 * (data.size % 64) := by
    have h512 : 512 = 8 * 64 := by decide
    rw [h512, Nat.mul_mod_mul_left]
  have hCond : 8 * data.size + 1 + (7 + 8 * z) ≡ 448 [MOD 512] := by
    show (8 * data.size + 1 + (7 + 8 * z)) % 512 = 448 % 512
    rw [hz_eq]
    have h448 : (448 : Nat) % 512 = 448 := by decide
    rw [h448]
    split <;> omega
  have hMin : ∀ j, j < 7 + 8 * z → ¬ (8 * data.size + 1 + j ≡ 448 [MOD 512]) := by
    intro j hj hcontra
    have hj_lt : j < 512 := by omega
    have hEq : (8 * data.size + 1 + (7 + 8 * z)) % 512 =
               (8 * data.size + 1 + j) % 512 := hCond.trans hcontra.symm
    have hL : (8 * data.size + 1 + (7 + 8 * z)) % 512 = (1 + (7 + 8 * z) +
              8 * data.size % 512) % 512 := by omega
    omega
  have hFind :
      (List.find? (fun k => decide (8 * data.size + 1 + k ≡ 448 [MOD 512])) (List.range 512))
        = some (7 + 8 * z) := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, ?_, ?_⟩
    · simpa using hCond
    · exact List.mem_range.mpr hRange
    · intro j hj; simpa using hMin j hj
  rw [hFind]; rfl

end SHS.Equiv.SHA256.Padding.ByteDecoding
