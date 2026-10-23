import Library.Hashing.Sha2.Equiv.SHA512.Pipeline

/-! # SHA-512 spec ↔ implementation — main user-facing theorems

This file contains the headline equivalences for the SHA-512 family:

* `compress_correct`     — per-block: `Impl.compress` ↔ `SHS.SHA512.compress`.
* `sha512_correct`       — top-level: `Impl.sha512` ↔ `SHS.SHA512.sha512`.
* `sha384_correct`       — top-level: `Impl.sha384` ↔ `SHS.SHA512.sha384`.
* `sha512_256_correct`   — top-level: `Impl.sha512_256` ↔ `SHS.SHA512.sha512_256`.
* `sha512_224_correct`   — top-level: `Impl.sha512_224` ↔ `SHS.SHA512.sha512_224`.

The four top-level theorems all share the same proof structure (a
chain of rewrites through the impl-refactored / extract / fold-lift /
parse-pad / spec-unfold ladder, followed by an 8-way `H[i]! = H[i]'hi`
bump).  Only the IV (`H0_{512,384,512_256,512_224}`) and the digest
width (`digestBitVec{512,384,512_256,512_224}`) differ across the four.

`sha512_224_correct` is unusual: its 28-byte digest crosses a 64-bit
word boundary (3 full words plus the top 32 bits of word 4), so it
routes through the SHA-512/256 32-byte digest and applies `leftmost
224` via the width-generic `fromBits_leftmost` identity. -/

open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Compress.Impl
open SHS.Equiv.SHA512.Compress.Match
open SHS.Equiv.SHA512.Foldl.Fused
open SHS.Equiv.SHA512.Digest
open SHS.Equiv.SHA512.Padding.Equiv
open SHS.Equiv.SHA512.Padding.ByteDecoding
open SHS.Equiv.SHA512.Padding.Parsing
open SHS.Equiv.SHA512.Pipeline

open SHS.SHA512

namespace SHS.Equiv.SHA512

open scoped SHS.SHA512

/-- `Impl.compress` agrees with the spec's per-block `SHS.SHA512.compress`
once both inputs are viewed in the spec's `BitVec 64` representation. -/
theorem compress_correct (state : Impl.State) (block : Impl.Block) :
    toSpecState (Impl.compress state block) =
      SHS.SHA512.compress (toSpecState state) (toSpecBlock block) := by
  rw [← impl_compress_eq_foldl,
      toSpecState_implCompressFoldl,
      ← spec_compress_eq_fused]

/-- `Impl.sha512` agrees with the spec's bitwise `sha512`, viewing the
64-byte digest as a 512-bit big-endian BitVec. -/
theorem sha512_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec512 (Impl.sha512 data) =
      SHS.SHA512.sha512 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  -- impl_sha512_eq_refactored exposes `Impl.sha512 = Vector.ofFn (extract bytes)`
  -- with the refactored state; rewrite to that, then push `digestBitVec512`
  -- through `extractDigest512`.
  have hImpl : Impl.sha512 data = extractDigest512 (implSha512Refactored data) := by
    rw [impl_sha512_eq_refactored _ h]
    rfl
  rw [hImpl, digestBitVec512_extract]
  unfold implSha512Refactored implSha512StateRefactored
  rw [foldl_compress_lift]
  rw [implPaddedBlocks_lift_eq_parsePad data h]
  -- Spec emits `H[i]` (bounded), our chain emits `H[i]!`.  Bridge each.
  unfold SHS.SHA512.sha512
  simp only
  set H := (SHS.SHA512.parse (SHS.SHA512.pad (bytesToBitMessage data))).foldl
    SHS.SHA512.compress SHS.SHA512.H0_512
  have hH (i : Nat) (hi : i < 8) : H[i]! = H[i]'hi :=
    SHS.Equiv.VecBridge.getElem_bang_eq_getElem H i hi
  rw [hH 0 (by decide), hH 1 (by decide), hH 2 (by decide), hH 3 (by decide),
      hH 4 (by decide), hH 5 (by decide), hH 6 (by decide), hH 7 (by decide)]

/-! ## SHA-384 and SHA-512/256 -/

/-- `Impl.sha384` agrees with the spec's `sha384`, viewing the 48-byte
digest as a 384-bit big-endian BitVec.  Parallel proof shape to
`sha512_correct`; the only differences are the IV (`H0_384`) and the
6-word digest concatenation. -/
theorem sha384_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec384 (Impl.sha384 data) =
      SHS.SHA512.sha384 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  have hImpl : Impl.sha384 data = extractDigest384 (implSha384Refactored data) := by
    rw [impl_sha384_eq_refactored _ h]
    rfl
  rw [hImpl, digestBitVec384_extract]
  unfold implSha384Refactored implSha512StateRefactored
  rw [foldl_compress_lift_384]
  rw [implPaddedBlocks_lift_eq_parsePad data h]
  unfold SHS.SHA512.sha384
  simp only
  set H := (SHS.SHA512.parse (SHS.SHA512.pad (bytesToBitMessage data))).foldl
    SHS.SHA512.compress SHS.SHA512.H0_384
  have hH (i : Nat) (hi : i < 8) : H[i]! = H[i]'hi :=
    SHS.Equiv.VecBridge.getElem_bang_eq_getElem H i hi
  rw [hH 0 (by decide), hH 1 (by decide), hH 2 (by decide), hH 3 (by decide),
      hH 4 (by decide), hH 5 (by decide)]

/-- `Impl.sha512_256` agrees with the spec's `sha512_256`. -/
theorem sha512_256_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec512_256 (Impl.sha512_256 data) =
      SHS.SHA512.sha512_256 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  have hImpl : Impl.sha512_256 data = extractDigest512_256 (implSha512_256Refactored data) := by
    rw [impl_sha512_256_eq_refactored _ h]
    rfl
  rw [hImpl, digestBitVec512_256_extract]
  unfold implSha512_256Refactored implSha512StateRefactored
  rw [foldl_compress_lift_512_256]
  rw [implPaddedBlocks_lift_eq_parsePad data h]
  unfold SHS.SHA512.sha512_256
  simp only
  set H := (SHS.SHA512.parse (SHS.SHA512.pad (bytesToBitMessage data))).foldl
    SHS.SHA512.compress SHS.SHA512.H0_512_256
  have hH (i : Nat) (hi : i < 8) : H[i]! = H[i]'hi :=
    SHS.Equiv.VecBridge.getElem_bang_eq_getElem H i hi
  rw [hH 0 (by decide), hH 1 (by decide), hH 2 (by decide), hH 3 (by decide)]

/-! ## SHA-512/224

The 28-byte digest crosses a 64-bit word boundary: the spec emits
`(H[0] ++ H[1] ++ H[2] ++ H[3]).leftmost 224`, keeping 3 full words plus
the high 32 bits of the fourth.  We route through SHA-512/256's 32-byte
emission and apply `leftmost 224` via the universal
`fromBits_leftmost` identity in `equiv/Common/FromBits.lean`. -/

theorem sha512_224_correct (data : ByteArray) (h : data.size < 2 ^ 61) :
    digestBitVec512_224 (Impl.sha512_224 data) =
      SHS.SHA512.sha512_224 (bytesToBitMessage data) (bitLen_lt_of_size_lt data h) := by
  have hImpl : Impl.sha512_224 data = extractDigest512_224 (implSha512_224Refactored data) := by
    rw [impl_sha512_224_eq_refactored _ h]
    rfl
  -- Replace 224 emission with leftmost-of-256.
  rw [hImpl, digestBitVec512_224_extract]
  -- Reduce 256-bit emission to spec's `H[0] ++ ... ++ H[3]` (via
  -- digestBitVec512_256_extract), then push `leftmost 224` through.
  show (digestBitVec512_256 (extractDigest512_256
      (implSha512_224Refactored data))).leftmost 224 = _
  rw [digestBitVec512_256_extract]
  unfold implSha512_224Refactored implSha512StateRefactored
  rw [foldl_compress_lift_512_224]
  rw [implPaddedBlocks_lift_eq_parsePad data h]
  unfold SHS.SHA512.sha512_224
  simp only
  set H := (SHS.SHA512.parse (SHS.SHA512.pad (bytesToBitMessage data))).foldl
    SHS.SHA512.compress SHS.SHA512.H0_512_224
  have hH (i : Nat) (hi : i < 8) : H[i]! = H[i]'hi :=
    SHS.Equiv.VecBridge.getElem_bang_eq_getElem H i hi
  rw [hH 0 (by decide), hH 1 (by decide), hH 2 (by decide), hH 3 (by decide)]

end SHS.Equiv.SHA512
