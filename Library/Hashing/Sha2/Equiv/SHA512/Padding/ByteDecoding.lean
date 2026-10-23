import Library.Hashing.Sha2.Equiv.SHA512.Padding.Layout
import Library.Hashing.Sha2.Equiv.Common.Bytes
import Library.Hashing.Sha2.Spec.Preprocessing

/-! # SHA-512 padding: byte → bit decoding

Parallel to `equiv/SHA256/Padding/ByteDecoding.lean` with SHA-512's
1024-bit-block-mod, 896-residue, 128-bit length suffix (FIPS 180-4
§5.1.2).

`bytesToBitMessage` decodes a `ByteArray` into the spec's `Message`
(`List Bool`, MSB-first within each byte).  This file collects the
distributivity laws of `bytesToBitMessage` over `++` / `push 0x80` /
`appendZeros` / `lengthBE128`, plus the headline lemma
`bytesToBitMessage_implPaddedBytes` that bridges the byte-level
streaming pad to the spec's `SHS.SHA512.pad ∘ bytesToBitMessage`. -/

open SHS.Equiv.Bytes
open SHS.Equiv.ByteArray
open SHS.Equiv.SHA512.Padding.Layout

open SHS.SHA512

namespace SHS.Equiv.SHA512.Padding.ByteDecoding

open scoped SHS.SHA512

/-- Decode a `ByteArray` into the spec's `Message` (`List Bool`,
MSB-first within each byte). -/
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

/-- `lengthBE128` decodes to a 128-bit MSB-first bit list: 64 zero bits
followed by the 64-bit BE encoding of `bits`. -/
theorem bytesToBitMessage_lengthBE128 (bits : UInt64) :
    bytesToBitMessage (lengthBE128 bits) =
      List.replicate 64 false ++ (List.range 64).reverse.map bits.toNat.testBit := by
  unfold lengthBE128
  simp [List.range', List.foldl, bytesToBitMessage, byteToBits,
        List.range, List.range.loop]
  simp +arith only [show (256 : Nat) = 2 ^ 8 from rfl,
        Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.reduceAdd]
  simp +decide

/-- The byte-length encoded in `lengthBE128 (data.size.toUInt64 <<< 3)`
matches `(8 * data.size)` bit-by-bit, for `data.size < 2 ^ 61`. -/
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

/-- For `data.size < 2 ^ 61`, the upper 64 bits of `8 * data.size` are zero. -/
private theorem testBit_8size_high (data : ByteArray) (h : data.size < 2 ^ 61)
    (i : Nat) (hi : 64 ≤ i) : (8 * data.size).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  calc 8 * data.size < 8 * 2 ^ 61 := by omega
    _ = 2 ^ 64 := by decide
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi

/-- Streaming pad ↔ SHA-512 spec `pad`. -/
theorem bytesToBitMessage_implPaddedBytes
    (data : ByteArray) (h : data.size < 2 ^ 61) :
    bytesToBitMessage (implPaddedBytes data) =
      SHS.SHA512.pad (bytesToBitMessage data) := by
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
  unfold implPaddedBytes SHS.SHA512.pad
  simp only [bytesToBitMessage_append, bytesToBitMessage_appendZeros,
    bytesToBitMessage_push_0x80, bytesToBitMessage_lengthBE128, hLen, hTB]
  set z := zerosCount data with hz_eq
  unfold zerosCount at hz_eq
  rw [show ([true, false, false, false, false, false, false, false] : List Bool) =
      [true] ++ List.replicate 7 false from by decide]
  simp only [List.append_assoc, List.replicate_append_replicate]
  -- Goal: ... ++ [true] ++ replicate (7 + 8*z) false ++ (replicate 64 false ++ ...)
  --        = bytesToBitMessage data ++ [true] ++ replicate k false ++
  --          (List.range 128).reverse.map (8 * data.size).testBit
  -- where k is the spec's chosen `k < 1024` with `ℓ + 1 + k ≡ 896 (mod 1024)`.
  -- Combine `(7 + 8 * z)` zeros with the 64 zero bytes from `lengthBE128`'s
  -- high half: total `(7 + 8 * z + 64)` zeros, then the 64-bit BE of bits.
  -- Also rewrite `(List.range 128).reverse.map testBit` as
  -- `(replicate 64 false ++ (List.range 64).reverse.map testBit)` using
  -- that the upper 64 bits of `8 * data.size` are zero.
  have hHigh : (List.range 128).reverse.map (8 * data.size).testBit =
      List.replicate 64 false ++ (List.range 64).reverse.map (8 * data.size).testBit := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      have hn128 : n < 128 := by simpa using h1
      simp only [List.getElem_map, List.getElem_reverse, List.length_range, List.getElem_range]
      by_cases hn : n < 64
      · -- LHS: testBit (127 - n) — high half (since 127 - n ≥ 64).
        have h_idx : 128 - 1 - n = 127 - n := by omega
        have h_high : 64 ≤ 127 - n := by omega
        rw [h_idx, testBit_8size_high data h _ h_high]
        -- RHS: replicate 64 false has `false` at index n.
        rw [List.getElem_append_left (by simp; omega)]
        rw [List.getElem_replicate]
      · -- LHS: testBit (127 - n) — low half.
        rw [List.getElem_append_right (by simpa using Nat.not_lt.mp hn)]
        simp only [List.length_replicate, List.getElem_map, List.getElem_reverse,
          List.length_range, List.getElem_range]
        congr 1
        omega
  -- Rewrite the spec side's 128-bit length suffix into 64 zeros + 64-bit
  -- BE testBit using the size-bound (high half is zero).
  rw [hHigh]
  -- spec.pad's `replicate k false` for `k = 7 + 8 * z`.
  set zPad := 7 + 8 * z with hzPad
  have hzPad_lt : zPad < 1024 := by
    rw [hzPad, hz_eq]; split <;> omega
  have hr : data.size % 128 < 128 := Nat.mod_lt _ (by decide)
  have h8mod : 8 * data.size % 1024 = 8 * (data.size % 128) := by
    have h1024 : 1024 = 8 * 128 := by decide
    rw [h1024, Nat.mul_mod_mul_left]
  have hCond : 8 * data.size + 1 + zPad ≡ 896 [MOD 1024] := by
    show (8 * data.size + 1 + zPad) % 1024 = 896 % 1024
    rw [hzPad, hz_eq]
    have h896 : (896 : Nat) % 1024 = 896 := by decide
    rw [h896]
    split <;> omega
  have hMin : ∀ j, j < zPad → ¬ (8 * data.size + 1 + j ≡ 896 [MOD 1024]) := by
    intro j hj hcontra
    have hj_lt : j < 1024 := by omega
    -- Both LHS and RHS modular conditions: (8s + 1 + k) % 1024 = 896
    have hCond' : (8 * data.size + 1 + zPad) % 1024 = 896 := by
      have h896 : (896 : Nat) % 1024 = 896 := by decide
      have := hCond
      unfold Nat.ModEq at this
      rw [h896] at this
      exact this
    have hContra' : (8 * data.size + 1 + j) % 1024 = 896 := by
      have h896 : (896 : Nat) % 1024 = 896 := by decide
      have := hcontra
      unfold Nat.ModEq at this
      rw [h896] at this
      exact this
    -- Both equal `(8 * (data.size % 128) + 1 + k) % 1024` via h8mod.
    have hSimplifyL : (8 * data.size + 1 + zPad) % 1024
        = (8 * (data.size % 128) + 1 + zPad) % 1024 := by omega
    have hSimplifyR : (8 * data.size + 1 + j) % 1024
        = (8 * (data.size % 128) + 1 + j) % 1024 := by omega
    rw [hSimplifyL] at hCond'
    rw [hSimplifyR] at hContra'
    rw [hzPad, hz_eq] at hCond' hj
    split at hCond' <;> split at hj <;> omega
  have hFind :
      (List.find? (fun k => decide (8 * data.size + 1 + k ≡ 896 [MOD 1024])) (List.range 1024))
        = some zPad := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, ?_, ?_⟩
    · simpa using hCond
    · exact List.mem_range.mpr hzPad_lt
    · intro j hj; simpa using hMin j hj
  rw [hFind]; rfl

end SHS.Equiv.SHA512.Padding.ByteDecoding
