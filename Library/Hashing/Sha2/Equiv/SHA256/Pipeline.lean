import Library.Hashing.Sha2.Equiv.SHA256.Compress.Impl
import Library.Hashing.Sha2.Equiv.SHA256.Compress.Match
import Library.Hashing.Sha2.Equiv.SHA256.Padding.Equiv
import Library.Hashing.Sha2.Equiv.SHA256.Padding.ByteDecoding
import Library.Hashing.Sha2.Equiv.SHA256.Padding.Parsing

/-! # Pipeline composition helpers

Lemmas that compose the per-block bridges (`Compress/Impl.lean` +
`Compress/Match.lean`) with the parse-and-pad bridge
(`Padding/Parsing.lean`) into the chain steps consumed by `Main.lean`'s
top-level `sha256_correct` rewrite.

## When to read this file

Open `Pipeline.lean` after `Compress/{Impl,Match}.lean` (single-block
bridge) and `Padding/Parsing.lean` (parse-of-pad bridge) are understood,
and *before* reading `Main.lean`'s `sha256_correct`.  Each lemma here is
exactly one link of that final rewrite chain:

* `bitLen_lt_of_size_lt` lifts the byte-size bound to the bit-length
  bound consumed by the spec.
* `foldl_compress_lift_gen` / `foldl_compress_lift` push the per-block
  compress bridge across `Array.foldl`, in two flavors (any IV /
  the SHA-256 IV).
* `SHA256_sha256_eq_concat` exposes the spec's `sha256` as `parse ∘ pad`
  threaded through the fold, plus a final 8-way `++`.

Once these four lemmas are in place, `sha256_correct` is the linear
chain `[refactored, extractDigest, digestBitVec, foldl, padding, concat]`. -/

open SHS.Equiv.SHA256.Lift
open SHS.Equiv.SHA256.Compress.Impl
open SHS.Equiv.SHA256.Compress.Match
open SHS.Equiv.SHA256.Foldl.Schedule
open SHS.Equiv.SHA256.Foldl.Sequential
open SHS.Equiv.SHA256.Foldl.Fused
open SHS.Equiv.SHA256.Padding.Layout
open SHS.Equiv.SHA256.Padding.Equiv
open SHS.Equiv.SHA256.Padding.ByteDecoding
open SHS.Equiv.SHA256.Padding.Parsing
open SHS.Equiv.Bytes

open SHS.SHA256

namespace SHS.Equiv.SHA256.Pipeline

open scoped SHS.SHA256

/-- The bit-length precondition derived from the byte-length one:
`data.size < 2^61` implies `(bytesToBitMessage data).length < 2^64`. -/
theorem bitLen_lt_of_size_lt (data : ByteArray) (h : data.size < 2 ^ 61) :
    (bytesToBitMessage data).length < 2 ^ 64 := by
  -- Each byte contributes exactly 8 bits, so total bit length is `8 * data.size`.
  have hLen : (bytesToBitMessage data).length = 8 * data.size := by
    simp only [bytesToBitMessage, byteToBits, List.length_flatMap, List.length_map,
      List.length_reverse, List.length_range]
    rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl]
    rw [List.map_const, List.sum_replicate_nat]
    show data.data.toList.length * 8 = 8 * data.size
    rw [Array.length_toList, Nat.mul_comm]; rfl
  -- `8 * 2^61 = 2^64`, so `data.size < 2^61 → 8 * data.size < 2^64`.
  have h264 : (8 : Nat) * 2 ^ 61 = 2 ^ 64 := by decide
  omega

/-- Generalised fold-lift: starting from any impl state, folding
`Impl.compress` over impl blocks lifts to folding `SHS.SHA256.compress`
over the spec-side block-lift.

Pure induction; the per-block bridge is inlined via the three-link
compress ladder (so this file does not depend on `compress_correct`). -/
theorem foldl_compress_lift_gen (blocks : Array (Vector UInt8 64))
    (s : Impl.State) :
    toSpecState (blocks.foldl (fun s b => Impl.compress s (Impl.toU32s b)) s) =
      (blocks.map (fun b => toSpecBlock (Impl.toU32s b))).foldl
        SHS.SHA256.compress (toSpecState s) := by
  rw [Array.foldl_map]
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  induction blocks.toList generalizing s with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    -- Reverse the per-block compress bridge on the RHS so both sides start
    -- from `toSpecState (Impl.compress s (Impl.toU32s hd))`, then close by IH.
    rw [spec_compress_eq_fused]
    rw [← toSpecState_implCompressFoldl]
    rw [impl_compress_eq_foldl]
    exact ih _

/-- Folding `Impl.compress` over `implPaddedBlocks data` (lifted) matches
folding spec `compress` over the spec-side block-list, starting from
the lifted IV `H0_256`. -/
theorem foldl_compress_lift (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU32s b)) Impl.H256_256) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU32s b))).foldl
        SHS.SHA256.compress SHS.SHA256.H0_256 := by
  rw [← toSpecState_H256_256]
  exact foldl_compress_lift_gen _ _

/-- Definitional unfolding of `SHS.SHA256.sha256` exposing the
fold-and-concat structure that the top-level rewrite chain lands at. -/
theorem SHA256_sha256_eq_concat (M : SHS.Message) (h : M.length < 2 ^ 64) :
    SHS.SHA256.sha256 M h =
      let H := (SHS.SHA256.parse (SHS.SHA1.pad M)).foldl
        SHS.SHA256.compress SHS.SHA256.H0_256
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! ++ H[7]! := rfl

/-! ## SHA-224 fold-lift and spec-side unfolding

Parallel to the SHA-256 helpers above but at the SHA-224 IV: same
generic `foldl_compress_lift_gen` instantiated at `H256_224`, plus the
spec-side `parse ∘ pad ∘ fold ∘ truncate-7` unfolding. -/

/-- SHA-224 variant of `foldl_compress_lift`: same shape, IV `H256_224`
lifts to `H0_224` via `toSpecState_H256_224`. -/
theorem foldl_compress_lift_224 (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU32s b)) Impl.H256_224) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU32s b))).foldl
        SHS.SHA256.compress SHS.SHA256.H0_224 := by
  rw [← toSpecState_H256_224]
  exact foldl_compress_lift_gen _ _

/-- Definitional unfolding of `SHS.SHA256.sha224` mirroring
`SHA256_sha256_eq_concat`; the spec emits only seven of the eight
hash words. -/
theorem SHA256_sha224_eq_concat (M : SHS.Message) (h : M.length < 2 ^ 64) :
    SHS.SHA256.sha224 M h =
      let H := (SHS.SHA256.parse (SHS.SHA1.pad M)).foldl
        SHS.SHA256.compress SHS.SHA256.H0_224
      H[0]! ++ H[1]! ++ H[2]! ++ H[3]! ++ H[4]! ++ H[5]! ++ H[6]! := rfl

end SHS.Equiv.SHA256.Pipeline
