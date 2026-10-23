import Library.Hashing.Sha2.Equiv.SHA256.Padding.ByteDecoding
import Library.Hashing.Sha2.Equiv.SHA256.ToU32s
import Library.Hashing.Sha2.Equiv.Common.Chunks
import Mathlib.Tactic.IntervalCases

/-! # SHA-256 padding: byte-level vs bit-level parse

Bridges the implementation's byte-level `implPaddedBlocks` with the
spec's bit-level `parse ∘ pad`.  The intermediate device is `parseBytes`
(below): a byte-aligned parse that bypasses `List.toChunks` and shows
the impl's block-wise slicing matches the spec's chunked-bit parse.

Follows FIPS 180-4 §5.2.1 (parsing the padded message into 16 × 32-bit
words per 512-bit block). -/

open SHS.Equiv.Bytes
open SHS.Equiv.ByteArray
open SHS.Equiv.Chunks
open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.ToU32s
open SHS.Equiv.SHA256.Padding.Layout
open SHS.Equiv.SHA256.Padding.ByteDecoding

open SHS.SHA256

namespace SHS.Equiv.SHA256.Padding.Parsing

open scoped SHS.SHA256

/-- Byte-level alternative to `SHS.SHA256.parse`: parse a 64-aligned
`ByteArray` directly into 16-word blocks, bypassing bit-level `toChunks`. -/
private def parseBytes (bs : ByteArray) : Array Block :=
  Array.ofFn (n := bs.size / 64) fun i =>
    toSpecBlock (Impl.toU32s (Vector.ofFn fun j : Fin 64 =>
      bs.get! (i.val * 64 + j.val)))

/-- Four bytes at offset `i * 64 + 4 * j` of a `ByteArray` of size `≥ i * 64 + 4 * j + 4`
    are recovered by `take 4 ∘ drop (4*j) ∘ take 64 ∘ drop (i*64)`.  Isolated from the
    main `parseBytes_eq_parse` proof so the indexing arithmetic does not clutter it. -/
private theorem fourBytes_take_drop (bs : ByteArray) (i j : Nat)
    (hSize : i * 64 + 4 * j + 4 ≤ bs.size) (hj : j < 16) :
    List.take 4 (List.drop (4 * j) (List.take 64 (List.drop (i * 64) bs.data.toList))) =
    [bs.data.toList[i * 64 + 4 * j]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 64 + 4 * j + 1]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 64 + 4 * j + 2]'(by rw [Array.length_toList, ByteArray.size_data]; omega),
     bs.data.toList[i * 64 + 4 * j + 3]'(by rw [Array.length_toList, ByteArray.size_data]; omega)
    ] := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega : 4 ≤ 64 - 4 * j),
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
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU32s b)) =
      parseBytes (implPaddedBytes data) := by
  unfold implPaddedBlocks parseBytes
  apply Array.ext
  · simp
  · intro i h₁ _
    simp only [Array.getElem_map, Array.getElem_ofFn]

/-- Byte-level parse equals bit-level parse over `bytesToBitMessage`,
for any 64-aligned `ByteArray`. -/
private theorem parseBytes_eq_parse (bs : ByteArray) (hMod : bs.size % 64 = 0) :
    parseBytes bs = SHS.SHA256.parse (bytesToBitMessage bs) := by
  unfold parseBytes SHS.SHA256.parse
  have hData : bs.data.size = bs.size := rfl
  have hLen : (bytesToBitMessage bs).length = 512 * (bs.size / 64) := by
    show (bs.data.toList.flatMap byteToBits).length = _
    rw [List.length_flatMap]
    rw [show (fun (a : UInt8) => (byteToBits a).length) = (fun _ => 8) from
      funext fun _ => byteToBits_length _]
    rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl,
      List.map_const, List.sum_replicate_nat]
    rw [Array.length_toList, hData]
    omega
  rw [toChunks_eq_drop_take 512 (by omega) _ (bs.size / 64) hLen]
  apply Array.ext
  · simp [Array.size_ofFn, List.toArray, List.length_map,
      List.length_range]
  · intro i hi1 hi2
    simp only [Array.getElem_ofFn, Array.getElem_map, List.getElem_toArray,
      List.getElem_map, List.getElem_range]
    show toSpecBlock _ = _
    unfold bytesToBitMessage
    rw [show i * 512 = 8 * (i * 64) from by omega,
        show (512 : Nat) = 8 * 64 from rfl,
        flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8]
    have hSize64 : i < bs.size / 64 := by
      simp [Array.size_ofFn] at hi1; exact hi1
    have hTakeLen : ((bs.data.toList.drop (i * 64)).take 64).length = 64 := by
      simp [List.length_take, List.length_drop, hData]
      omega
    have hFlatLen : (((bs.data.toList.drop (i * 64)).take 64).flatMap byteToBits).length =
        32 * 16 := by
      rw [List.length_flatMap]
      rw [show (fun (a : UInt8) => (byteToBits a).length) = (fun _ => 8) from
        funext fun _ => byteToBits_length _]
      rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl,
        List.map_const, List.sum_replicate_nat, hTakeLen]
    rw [toChunks_eq_drop_take 32 (by omega) _ 16 hFlatLen]
    apply Vector.ext
    intro j hjLt
    have hLHS := toSpecBlock_toU32s_index
      (Vector.ofFn fun (k : Fin 64) => bs.get! (i * 64 + k.val)) ⟨j, hjLt⟩
    have hSizeLHS : j < 16 := hjLt
    rw [show (toSpecBlock (Impl.toU32s
            (Vector.ofFn fun (k : Fin 64) => bs.get! (i * 64 + k.val))))[j]'hjLt =
          (toSpecBlock (Impl.toU32s
            (Vector.ofFn fun (k : Fin 64) => bs.get! (i * 64 + k.val))))[j]! from
        (getElem!_pos _ j hSizeLHS).symm]
    rw [hLHS]
    -- RHS is `(Vector.ofFn ...)[j]`; reduce. After `Vector.getElem_ofFn`, the
    -- index becomes `⟨j, hjLt⟩ : Fin 16`. Chase through the `getElem?`/`getD`
    -- to the concrete `List.range` element.
    rw [Vector.getElem_ofFn]
    simp only [Fin.getElem?_fin]
    rw [Array.getElem?_eq_getElem (by simp [List.length_map, List.length_range]; exact hjLt)]
    simp only [Option.getD_some, List.getElem_toArray, List.getElem_map, List.getElem_range]
    congr 1
    rw [show j * 32 = 8 * (4 * j) from by omega,
        show (32 : Nat) = 8 * 4 from rfl,
        flatMap_byteToBits_drop_8, flatMap_byteToBits_take_8]
    unfold fourBytesBits
    have hSizeBs : i * 64 + 4 * j + 4 ≤ bs.size := by
      have : 64 * (i + 1) ≤ 64 * (bs.size / 64) := Nat.mul_le_mul_left 64 hSize64
      have : bs.size = 64 * (bs.size / 64) := by omega
      omega
    rw [fourBytes_take_drop bs i j hSizeBs hjLt]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    simp only [Vector.getElem_ofFn]
    rw [get!_eq_toList_getElem bs (i * 64 + 4 * j) (by omega),
        show i * 64 + (4 * j + 1) = i * 64 + 4 * j + 1 from by omega,
        get!_eq_toList_getElem bs (i * 64 + 4 * j + 1) (by omega),
        show i * 64 + (4 * j + 2) = i * 64 + 4 * j + 2 from by omega,
        get!_eq_toList_getElem bs (i * 64 + 4 * j + 2) (by omega),
        show i * 64 + (4 * j + 3) = i * 64 + 4 * j + 3 from by omega,
        get!_eq_toList_getElem bs (i * 64 + 4 * j + 3) (by omega)]
    simp [List.append_assoc]

/-- The headline of this file: lifting `implPaddedBlocks` through
`toSpecBlock ∘ Impl.toU32s` equals the spec's `parse (pad msg)` of the
input bit-message.  Routes through `parseBytes` as the intermediate
byte-level form.  Consumed by `Pipeline.lean`'s `implPaddedBlocks_lift`
rewrite. -/
theorem implPaddedBlocks_lift_eq_parsePad (data : ByteArray)
    (h : data.size < 2 ^ 61) :
    (implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU32s b)) =
      SHS.SHA256.parse (SHS.SHA1.pad (bytesToBitMessage data)) := by
  rw [← bytesToBitMessage_implPaddedBytes data h]
  rw [implPaddedBlocks_eq_parseBytes]
  exact parseBytes_eq_parse _ (size_implPaddedBytes_mod data)

end SHS.Equiv.SHA256.Padding.Parsing
