import Library.Hashing.Sha2.Equiv.SHA512.Padding.ByteDecoding
import Library.Hashing.Sha2.Equiv.SHA512.ToU64s
import Library.Hashing.Sha2.Equiv.Common.Chunks
import Mathlib.Tactic.IntervalCases

/-! # SHA-512 padding: byte-level vs bit-level parse

Parallel to `equiv/SHA256/Padding/Parsing.lean` at 128-byte blocks,
1024-bit blocks, 64-bit words, 8 bytes per word.

Bridges the implementation's byte-level `implPaddedBlocks` with the
spec's bit-level `parse ∘ pad`.  The intermediate device is
`parseBytes` (below): a byte-aligned parse that bypasses
`List.toChunks` and shows the impl's block-wise slicing matches the
spec's chunked-bit parse.

Follows FIPS 180-4 §5.2.2 (parsing the padded message into 16 × 64-bit
words per 1024-bit block). -/

open SHS.Equiv.Bytes
open SHS.Equiv.ByteArray
open SHS.Equiv.Chunks
open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.ToU64s
open SHS.Equiv.SHA512.Padding.Layout
open SHS.Equiv.SHA512.Padding.ByteDecoding

open SHS.SHA512

namespace SHS.Equiv.SHA512.Padding.Parsing

open scoped SHS.SHA512

/-- Byte-level alternative to `SHS.SHA512.parse`: parse a 128-aligned
`ByteArray` directly into 16-word blocks, bypassing bit-level `toChunks`. -/
private def parseBytes (bs : ByteArray) : Array Block :=
  Array.ofFn (n := bs.size / 128) fun i =>
    toSpecBlock (Impl.toU64s (Vector.ofFn fun j : Fin 128 =>
      bs.get! (i.val * 128 + j.val)))

-- `interval_cases k` enumerates the eight indices `0..7` of the
-- take-8-of-128 slice, and each case unfolds `List.getElem_take +
-- List.getElem_drop` plus a `Nat.add_assoc` rewrite — the eight nested
-- `omega` discharges per case push past the default budget.
set_option maxHeartbeats 400000 in
/-- Eight bytes at offset `i * 128 + 8 * j` of a `ByteArray` of size
`≥ i * 128 + 8 * j + 8` are recovered by
`take 8 ∘ drop (8*j) ∘ take 128 ∘ drop (i*128)`.  Isolated from the
main `parseBytes_eq_parse` proof so the indexing arithmetic does not
clutter it. -/
private theorem eightBytes_take_drop (bs : ByteArray) (i j : Nat)
    (hSize : i * 128 + 8 * j + 8 ≤ bs.size) (hj : j < 16) :
    List.take 8 (List.drop (8 * j) (List.take 128 (List.drop (i * 128) bs.data.toList))) =
    [bs.data.toList[i * 128 + 8 * j]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 128 + 8 * j + 1]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 128 + 8 * j + 2]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 128 + 8 * j + 3]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 128 + 8 * j + 4]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 128 + 8 * j + 5]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 128 + 8 * j + 6]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 128 + 8 * j + 7]'(by rw [Array.length_toList, ByteArray.size_data]; omega)
    ] := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega : 8 ≤ 128 - 8 * j),
      List.drop_drop]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, Array.length_toList, ByteArray.size_data]; omega
  · intro k _ hk2
    simp only [List.length_cons, List.length_nil] at hk2
    interval_cases k <;> simp [List.getElem_take, List.getElem_drop, Nat.add_assoc]

/-- The lifted byte-block view of the streaming pad equals the
byte-level `parseBytes` of the padded bytes.  Both unfold to the same
`Array.ofFn` indexing the same `implPaddedBytes`. -/
private theorem implPaddedBlocks_eq_parseBytes (data : ByteArray) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b)) =
      parseBytes (implPaddedBytes data) := by
  unfold implPaddedBlocks parseBytes
  apply Array.ext
  · simp
  · intro i h₁ _
    simp only [Array.getElem_map, Array.getElem_ofFn]

-- This is the spec↔impl parse bridge: it `Array.ext`s a 16-block × 8-byte
-- decode against `SHS.SHA512.parse`'s `toChunks`-based slicing.  The
-- per-block proof uses eight `get!_eq_toList_getElem` rewrites with
-- intermediate arithmetic `show` lemmas, so the unfolded term tree is
-- large enough to need the bumped heartbeat budget.

set_option maxHeartbeats 800000 in
/-- Byte-level `parseBytes` of a 128-aligned `ByteArray` equals the
spec's bit-level `parse` of its `bytesToBitMessage`.  Combines the
chunked-bit characterisation `toChunks_eq_drop_take` with the byte
view `eightBytes_take_drop` to align each 8-byte slice. -/
private theorem parseBytes_eq_parse (bs : ByteArray) (hMod : bs.size % 128 = 0) :
    parseBytes bs = SHS.SHA512.parse (bytesToBitMessage bs) := by
  unfold parseBytes SHS.SHA512.parse
  have hData : bs.data.size = bs.size := rfl
  have hLen : (bytesToBitMessage bs).length = 1024 * (bs.size / 128) := by
    show (bs.data.toList.flatMap byteToBits).length = _
    rw [List.length_flatMap]
    rw [show (fun (a : UInt8) => (byteToBits a).length) = (fun _ => 8) from
      funext fun _ => byteToBits_length _]
    rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl,
      List.map_const, List.sum_replicate_nat]
    rw [Array.length_toList, hData]
    omega
  rw [toChunks_eq_drop_take 1024 (by omega) _ (bs.size / 128) hLen]
  apply Array.ext
  · simp [Array.size_ofFn, List.toArray, List.length_map,
      List.length_range]
  · intro i hi1 hi2
    simp only [Array.getElem_ofFn, Array.getElem_map, List.getElem_toArray,
      List.getElem_map, List.getElem_range]
    show toSpecBlock _ = _
    unfold bytesToBitMessage
    rw [show i * 1024 = 8 * (i * 128) from by omega,
        show (1024 : Nat) = 8 * 128 from rfl,
        flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8]
    have hSize128 : i < bs.size / 128 := by
      simp [Array.size_ofFn] at hi1; exact hi1
    have hTakeLen : ((bs.data.toList.drop (i * 128)).take 128).length = 128 := by
      simp [List.length_take, List.length_drop, hData]
      omega
    have hFlatLen : (((bs.data.toList.drop (i * 128)).take 128).flatMap byteToBits).length =
        64 * 16 := by
      rw [List.length_flatMap]
      rw [show (fun (a : UInt8) => (byteToBits a).length) = (fun _ => 8) from
        funext fun _ => byteToBits_length _]
      rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl,
        List.map_const, List.sum_replicate_nat, hTakeLen]
    rw [toChunks_eq_drop_take 64 (by omega) _ 16 hFlatLen]
    apply Vector.ext
    intro j hjLt
    have hLHS := toSpecBlock_toU64s_index
      (Vector.ofFn fun (k : Fin 128) => bs.get! (i * 128 + k.val)) ⟨j, hjLt⟩
    have hSizeLHS : j < 16 := hjLt
    rw [show (toSpecBlock (Impl.toU64s
            (Vector.ofFn fun (k : Fin 128) => bs.get! (i * 128 + k.val))))[j]'hjLt =
          (toSpecBlock (Impl.toU64s
            (Vector.ofFn fun (k : Fin 128) => bs.get! (i * 128 + k.val))))[j]! from
        (getElem!_pos _ j hSizeLHS).symm]
    rw [hLHS]
    rw [Vector.getElem_ofFn]
    simp only [Fin.getElem?_fin]
    rw [Array.getElem?_eq_getElem (by simp [List.length_map, List.length_range]; exact hjLt)]
    simp only [Option.getD_some, List.getElem_toArray, List.getElem_map, List.getElem_range]
    congr 1
    rw [show j * 64 = 8 * (8 * j) from by omega,
        show (64 : Nat) = 8 * 8 from rfl,
        flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8]
    unfold eightBytesBits
    have hSizeBs : i * 128 + 8 * j + 8 ≤ bs.size := by
      have : 128 * (i + 1) ≤ 128 * (bs.size / 128) := Nat.mul_le_mul_left 128 hSize128
      have : bs.size = 128 * (bs.size / 128) := by omega
      omega
    rw [eightBytes_take_drop bs i j hSizeBs hjLt]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [Vector.getElem_ofFn]
    rw [get!_eq_toList_getElem bs (i * 128 + 8 * j) (by omega),
        show i * 128 + (8 * j + 1) = i * 128 + 8 * j + 1 from by omega,
        get!_eq_toList_getElem bs (i * 128 + 8 * j + 1) (by omega),
        show i * 128 + (8 * j + 2) = i * 128 + 8 * j + 2 from by omega,
        get!_eq_toList_getElem bs (i * 128 + 8 * j + 2) (by omega),
        show i * 128 + (8 * j + 3) = i * 128 + 8 * j + 3 from by omega,
        get!_eq_toList_getElem bs (i * 128 + 8 * j + 3) (by omega),
        show i * 128 + (8 * j + 4) = i * 128 + 8 * j + 4 from by omega,
        get!_eq_toList_getElem bs (i * 128 + 8 * j + 4) (by omega),
        show i * 128 + (8 * j + 5) = i * 128 + 8 * j + 5 from by omega,
        get!_eq_toList_getElem bs (i * 128 + 8 * j + 5) (by omega),
        show i * 128 + (8 * j + 6) = i * 128 + 8 * j + 6 from by omega,
        get!_eq_toList_getElem bs (i * 128 + 8 * j + 6) (by omega),
        show i * 128 + (8 * j + 7) = i * 128 + 8 * j + 7 from by omega,
        get!_eq_toList_getElem bs (i * 128 + 8 * j + 7) (by omega)]
    simp [List.append_assoc]

/-- The headline of this file: lifting `implPaddedBlocks` through
`toSpecBlock ∘ Impl.toU64s` equals the spec's `parse (pad msg)` of the
input bit-message.  Routes through `parseBytes` as the intermediate
byte-level form.  Consumed by `Pipeline.lean`'s `implPaddedBlocks_lift`
rewrite. -/
theorem implPaddedBlocks_lift_eq_parsePad (data : ByteArray)
    (h : data.size < 2 ^ 61) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b)) =
      SHS.SHA512.parse (SHS.SHA512.pad (bytesToBitMessage data)) := by
  rw [← bytesToBitMessage_implPaddedBytes data h]
  rw [implPaddedBlocks_eq_parseBytes]
  exact parseBytes_eq_parse _ (size_implPaddedBytes_mod data)

end SHS.Equiv.SHA512.Padding.Parsing
