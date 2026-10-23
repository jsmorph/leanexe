import Library.Hashing.Sha2.Equiv.SHA512.Padding.Layout
import Library.Hashing.Sha2.Equiv.SHA512.Padding.ByteDecoding
import Library.Hashing.Sha2.Equiv.SHA512.Padding.Parsing
import Library.Hashing.Sha2.Equiv.SHA512.ToU64s
import Library.Hashing.Sha2.Equiv.Common.ArrayFold

/-! # SHA-512 padding: streaming refactor of `Impl.sha512`

Parallel to `equiv/SHA256/Padding/Equiv.lean` at 128-byte blocks.

The headline equivalence between the implementation's imperative
streaming `Impl.sha512` and a clean block-list re-statement
(`implSha512Refactored`) that mirrors the spec's shape.  Both compute
the same digest, proved by case-splitting on `data.size % 128 < 112`
and peeling the last (or last two) iterations of the impl's
`Fin.foldl`.

The byte→bit decoding lemmas live in `Padding/ByteDecoding`; the
byte-level / bit-level parse bridge lives in `Padding/Parsing`.  This
file only handles the streaming-vs-block-list refactor of the impl,
and is shared (under different IVs and digest widths) by the four
SHA-512 family hashes. -/

open SHS.Equiv.ArrayFold
open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Padding.Layout

open SHS.SHA512

namespace SHS.Equiv.SHA512.Padding.Equiv

open scoped SHS.SHA512

/-- IV-generic block-list re-statement of `Impl.sha512State`: fold
`Impl.compress` over `implPaddedBlocks data` starting from `H0`.
Shared core for all four SHA-512 family refactorings (different IVs:
`H0_512`, `H0_384`, `H0_512_256`, `H0_512_224`). -/
def implSha512StateRefactored (data : ByteArray) (H0 : Impl.State) : Impl.State :=
  (implPaddedBlocks data).foldl (fun s b => Impl.compress s (Impl.toU64s b)) H0

/-- Block-list re-statement of `Impl.sha512`: SHA-512 fold from
`H0_512`, prior to the 64-byte digest emission. -/
def implSha512Refactored (data : ByteArray) : Impl.State :=
  implSha512StateRefactored data Impl.H0_512

/-- Definitional unfolding of `implSha512Refactored` as the underlying
`Array.foldl`-shaped fold. -/
theorem implSha512Refactored_eq_foldl (data : ByteArray) :
    implSha512Refactored data =
      (implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_512 := rfl

private theorem impl_sha512State_eq_extract (data : ByteArray) (H0 : Impl.State) :
    Impl.sha512State data H0 =
      let blocks := data.size / 128
      let remaining := data.size % 128
      let totalBits : UInt64 := data.size.toUInt64 <<< 3
      let state : Impl.State := Fin.foldl blocks (fun state (i : Fin blocks) =>
        let block : Vector UInt8 128 := Vector.ofFn fun j : Fin 128 =>
          data.get! (i.val * 128 + j.val)
        Impl.compress state (Impl.toU64s block)) H0
      let finalBlockA : Vector UInt8 128 := Vector.ofFn fun i : Fin 128 =>
        if i.val < remaining then data.get! (blocks * 128 + i.val)
        else if i.val = remaining then 0x80
        else 0
      let (state, finalBlockB) :=
        if remaining < 112 then (state, finalBlockA)
        else
          (Impl.compress state (Impl.toU64s finalBlockA),
           Vector.ofFn (fun _ : Fin 128 => (0 : UInt8)))
      let finalBlockC : Vector UInt8 128 := Vector.ofFn fun i : Fin 128 =>
        if i.val < 112 then finalBlockB[i]
        else if i.val < 120 then 0
        else ((totalBits >>> (((127 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8
      Impl.compress state (Impl.toU64s finalBlockC) := by
  unfold Impl.sha512State
  -- Bridge the fast-path `toU64sFromBytes` reads (used in the impl
  -- definition) to the `toU64s ∘ Vector.ofFn` shape the spec
  -- equivalence is stated against.
  simp only [SHS.Equiv.SHA512.ToU64s.toU64sFromBytes_eq_toU64s]

/-- IV-generic refactor: `Impl.sha512State` (the shared SHA-2-512 core)
equals folding `Impl.compress` over `implPaddedBlocks data` from `H0`.
The `< 112` / `≥ 112` case-split mirrors `sha512State`'s own
conditional emission of one vs two final blocks. -/
theorem impl_sha512State_eq_refactored (data : ByteArray) (H0 : Impl.State) :
    Impl.sha512State data H0 = implSha512StateRefactored data H0 := by
  rw [impl_sha512State_eq_extract _ H0]
  unfold implSha512StateRefactored
  rw [implPaddedBlocks_foldl]
  by_cases h : data.size % 128 < 112
  · rw [totalBlocks_lt112 _ h]
    simp only [h, ↓reduceIte]
    rw [Fin.foldl_succ_last]
    have hFoldEq :
      Fin.foldl (data.size / 128)
        (fun (state : Impl.State) (i : Fin (data.size / 128)) =>
          Impl.compress state (Impl.toU64s
            (Vector.ofFn fun j : Fin 128 => data.get! (i.val * 128 + j.val))))
        H0
        =
      Fin.foldl (data.size / 128)
        (fun (s : Impl.State) (i : Fin (data.size / 128)) =>
          Impl.compress s (Impl.toU64s (paddedBlock data i.castSucc.val)))
        H0 := by
      apply fin_foldl_ext
      intro s i
      have := paddedBlock_complete data i.val i.isLt
      rw [show i.castSucc.val = i.val from rfl, ← this]
    have hBlockEq :
      (Vector.ofFn fun i : Fin 128 =>
        if i.val < 112 then
          (Vector.ofFn fun i : Fin 128 =>
            if i.val < data.size % 128 then data.get! (data.size / 128 * 128 + i.val)
            else if i.val = data.size % 128 then (0x80 : UInt8)
            else 0)[i]
        else if i.val < 120 then 0
        else (data.size.toUInt64 <<< 3 >>> (((127 - i.val) * 8).toUInt64) &&& 0xff).toUInt8)
        = paddedBlock data (Fin.last (data.size / 128)).val := by
      show _ = paddedBlock data (data.size / 128)
      rw [paddedBlock_final_lt112 data h]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      by_cases hi112 : i < 112
      · simp [hi112]
      · simp [hi112]
    rw [hFoldEq, hBlockEq]
  · rw [totalBlocks_ge112 _ h]
    simp only [h, ↓reduceIte]
    rw [Fin.foldl_succ_last]
    conv_rhs => rw [Fin.foldl_succ_last]
    have hFoldEq :
      Fin.foldl (data.size / 128)
        (fun (state : Impl.State) (i : Fin (data.size / 128)) =>
          Impl.compress state (Impl.toU64s
            (Vector.ofFn fun j : Fin 128 => data.get! (i.val * 128 + j.val))))
        H0
        =
      Fin.foldl (data.size / 128)
        (fun (s : Impl.State) (i : Fin (data.size / 128)) =>
          Impl.compress s (Impl.toU64s (paddedBlock data i.castSucc.castSucc.val)))
        H0 := by
      apply fin_foldl_ext
      intro s i
      have := paddedBlock_complete data i.val i.isLt
      rw [show i.castSucc.castSucc.val = i.val from rfl, ← this]
    have hBlockA :
      (Vector.ofFn fun i : Fin 128 =>
          if i.val < data.size % 128 then data.get! (data.size / 128 * 128 + i.val)
          else if i.val = data.size % 128 then (0x80 : UInt8)
          else 0)
        = paddedBlock data (Fin.last (data.size / 128)).castSucc.val := by
      show _ = paddedBlock data (data.size / 128)
      rw [paddedBlock_finalA_ge112 data h]
    have hBlockB :
      (Vector.ofFn fun i : Fin 128 =>
          if i.val < 112 then (Vector.ofFn (fun _ : Fin 128 => (0 : UInt8)))[i]
          else if i.val < 120 then 0
          else (data.size.toUInt64 <<< 3 >>> (((127 - i.val) * 8).toUInt64) &&& 0xff).toUInt8)
        = paddedBlock data (Fin.last (data.size / 128 + 1)).val := by
      show _ = paddedBlock data (data.size / 128 + 1)
      rw [paddedBlock_finalB_ge112 data h]
      apply Vector.ext
      intro i hi
      simp only [Vector.getElem_ofFn]
      by_cases hi112 : i < 112
      · have hi120 : i < 120 := by omega
        simp [hi112, hi120]
      · simp [hi112]
    rw [hFoldEq, hBlockA, hBlockB]

/-- `Impl.sha512` agrees with its block-list refactoring composed with
the 64-byte BE digest emission.  The `data.size < 2 ^ 61` hypothesis
discharges the runtime size guard at the top of `Impl.sha512` (see
FIPS 180-4 §5.1.2). -/
theorem impl_sha512_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha512 data =
      let final := implSha512Refactored data
      Vector.ofFn fun i : Fin 64 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((final[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8 := by
  unfold Impl.sha512
  rw [if_neg (Nat.not_le.mpr hsize)]
  show (Vector.ofFn fun i : Fin 64 => _) = _
  unfold implSha512Refactored
  rw [impl_sha512State_eq_refactored]

/-! ## SHA-384, SHA-512/256, SHA-512/224 refactor

Each variant uses the same `implSha512StateRefactored` core at a
different IV (`H0_384` / `H0_512_256` / `H0_512_224`), with a different
digest-emission width (48 / 32 / 28 bytes).  Proof shapes are
identical to `impl_sha512_eq_refactored`. -/

/-- Block-list re-statement of `Impl.sha384`: SHA-512 fold from the
SHA-384 IV, prior to 48-byte digest emission. -/
def implSha384Refactored (data : ByteArray) : Impl.State :=
  implSha512StateRefactored data Impl.H0_384

/-- `Impl.sha384` agrees with the block-list refactoring composed with
48-byte BE digest emission.  Same proof shape as
`impl_sha512_eq_refactored`. -/
theorem impl_sha384_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha384 data =
      let final := implSha384Refactored data
      Vector.ofFn fun i : Fin 48 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((final[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8 := by
  unfold Impl.sha384
  rw [if_neg (Nat.not_le.mpr hsize)]
  show (Vector.ofFn fun i : Fin 48 => _) = _
  unfold implSha384Refactored
  rw [impl_sha512State_eq_refactored]

/-- Block-list re-statement of `Impl.sha512_256`: SHA-512 fold from the
SHA-512/256 IV, prior to 32-byte digest emission. -/
def implSha512_256Refactored (data : ByteArray) : Impl.State :=
  implSha512StateRefactored data Impl.H0_512_256

/-- `Impl.sha512_256` agrees with the block-list refactoring composed
with 32-byte BE digest emission.  Same proof shape as
`impl_sha512_eq_refactored`. -/
theorem impl_sha512_256_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha512_256 data =
      let final := implSha512_256Refactored data
      Vector.ofFn fun i : Fin 32 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((final[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8 := by
  unfold Impl.sha512_256
  rw [if_neg (Nat.not_le.mpr hsize)]
  show (Vector.ofFn fun i : Fin 32 => _) = _
  unfold implSha512_256Refactored
  rw [impl_sha512State_eq_refactored]

/-- Block-list re-statement of `Impl.sha512_224`: SHA-512 fold from the
SHA-512/224 IV, prior to 28-byte digest emission. -/
def implSha512_224Refactored (data : ByteArray) : Impl.State :=
  implSha512StateRefactored data Impl.H0_512_224

/-- `Impl.sha512_224` agrees with the block-list refactoring composed
with 28-byte BE digest emission.  Same proof shape as
`impl_sha512_eq_refactored`. -/
theorem impl_sha512_224_eq_refactored (data : ByteArray) (hsize : data.size < 2 ^ 61) :
    Impl.sha512_224 data =
      let final := implSha512_224Refactored data
      Vector.ofFn fun i : Fin 28 =>
        let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
        let byteIdx := i.val % 8
        ((final[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8 := by
  unfold Impl.sha512_224
  rw [if_neg (Nat.not_le.mpr hsize)]
  show (Vector.ofFn fun i : Fin 28 => _) = _
  unfold implSha512_224Refactored
  rw [impl_sha512State_eq_refactored]

end SHS.Equiv.SHA512.Padding.Equiv
