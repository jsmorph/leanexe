import Library.Hashing.Sha2.Equiv.SHA512.Compress.Impl
import Library.Hashing.Sha2.Equiv.SHA512.Compress.Match
import Library.Hashing.Sha2.Equiv.SHA512.Padding.Equiv
import Library.Hashing.Sha2.Equiv.SHA512.Padding.ByteDecoding
import Library.Hashing.Sha2.Equiv.SHA512.Padding.Parsing
import Library.Hashing.Sha2.Equiv.SHA512.Digest
import Library.Hashing.Sha2.Spec.SHA512tHash

/-! # SHA-512 pipeline composition helpers

Parallel to `equiv/SHA256/Pipeline.lean` at 80 rounds, 1024-bit blocks,
and a 128-bit length suffix (FIPS 180-4 §5.1.2).  Composes the per-block
compress bridge (`Compress/{Impl,Match}.lean`) with the parse-and-pad
bridge (`Padding/Parsing.lean`) into the chain steps consumed by
`Main.lean`'s `sha512_correct` / `sha384_correct` / `sha512_256_correct`
/ `sha512_224_correct` rewrites.

## When to read this file

Open `Pipeline.lean` after `Compress/{Impl,Match}.lean` (per-block
bridge) and `Padding/Parsing.lean` (parse-of-pad bridge), and *before*
reading `Main.lean`'s four top-level correctness theorems.  Each lemma
here is one link of those rewrite chains:

* `bitLen_lt_of_size_lt` lifts the byte-size bound `data.size < 2^61`
  to the bit-length bound `< 2^128` consumed by `SHS.SHA512.sha512`.
* `foldl_compress_lift_gen` is the IV-generic fold lift; the
  per-variant `foldl_compress_lift{_384,_512_256,_512_224}` are
  one-line corollaries instantiating the generic lift at the
  variant's IV. -/

open SHS.Equiv.SHA512.Lift
open SHS.Equiv.SHA512.Compress.Impl
open SHS.Equiv.SHA512.Compress.Match
open SHS.Equiv.SHA512.Foldl.Schedule
open SHS.Equiv.SHA512.Foldl.Sequential
open SHS.Equiv.SHA512.Foldl.Fused
open SHS.Equiv.SHA512.Padding.Layout
open SHS.Equiv.SHA512.Padding.Equiv
open SHS.Equiv.SHA512.Padding.ByteDecoding
open SHS.Equiv.SHA512.Padding.Parsing
open SHS.Equiv.SHA512.Digest
open SHS.Equiv.Bytes

open SHS.SHA512

namespace SHS.Equiv.SHA512.Pipeline

open scoped SHS.SHA512

/-- The bit-length precondition derived from the byte-length one:
`data.size < 2^61` implies `(bytesToBitMessage data).length < 2^128`,
the bound consumed by `SHS.SHA512.sha512`. -/
theorem bitLen_lt_of_size_lt (data : ByteArray) (h : data.size < 2 ^ 61) :
    (bytesToBitMessage data).length < 2 ^ 128 := by
  -- Each byte contributes exactly 8 bits, so total bit length is `8 * data.size`.
  have hLen : (bytesToBitMessage data).length = 8 * data.size := by
    simp only [bytesToBitMessage, byteToBits, List.length_flatMap, List.length_map,
      List.length_reverse, List.length_range]
    rw [show (fun (_ : UInt8) => 8) = Function.const UInt8 8 from rfl]
    rw [List.map_const, List.sum_replicate_nat]
    show data.data.toList.length * 8 = 8 * data.size
    rw [Array.length_toList, Nat.mul_comm]; rfl
  -- `8 * 2^61 = 2^64 ≪ 2^128`, so the bound holds with room to spare.
  have h2128 : (8 : Nat) * 2 ^ 61 < 2 ^ 128 := by decide
  omega

/-- Generalised fold-lift: starting from any impl state, folding
`Impl.compress` over impl blocks lifts to folding `SHS.SHA512.compress`
over the spec-side block-lift.

Pure induction; the per-block bridge is inlined via the three-link
compress ladder (so this file does not depend on `compress_correct`). -/
theorem foldl_compress_lift_gen (blocks : Array (Vector UInt8 128))
    (s : Impl.State) :
    toSpecState (blocks.foldl (fun s b => Impl.compress s (Impl.toU64s b)) s) =
      (blocks.map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress (toSpecState s) := by
  rw [Array.foldl_map]
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  induction blocks.toList generalizing s with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl]
    -- Reverse the per-block compress bridge on the RHS so both sides start
    -- from `toSpecState (Impl.compress s (Impl.toU64s hd))`, then close by IH.
    rw [spec_compress_eq_fused]
    rw [← toSpecState_implCompressFoldl]
    rw [impl_compress_eq_foldl]
    exact ih _

/-- Folding `Impl.compress` over `implPaddedBlocks data` (lifted) matches
folding spec `compress` over the spec-side block-list, starting from
the lifted IV `H0_512`. -/
theorem foldl_compress_lift (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_512) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress SHS.SHA512.H0_512 := by
  rw [← toSpecState_H0_512]
  exact foldl_compress_lift_gen _ _

/-! ## SHA-384, SHA-512/256, SHA-512/224 fold-lift

Each is the same one-line corollary of `foldl_compress_lift_gen`,
instantiated at the variant's IV (`H0_384`, `H0_512_256`, `H0_512_224`)
via the corresponding `toSpecState_H0_*` lift lemma from `Lift.lean`. -/

/-- SHA-384 variant of `foldl_compress_lift`: IV `H0_384` lifts to
`SHS.SHA512.H0_384` via `toSpecState_H0_384`. -/
theorem foldl_compress_lift_384 (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_384) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress SHS.SHA512.H0_384 := by
  rw [← toSpecState_H0_384]
  exact foldl_compress_lift_gen _ _

/-- SHA-512/256 variant of `foldl_compress_lift`: IV `H0_512_256` lifts
to `SHS.SHA512.H0_512_256` via `toSpecState_H0_512_256`. -/
theorem foldl_compress_lift_512_256 (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_512_256) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress SHS.SHA512.H0_512_256 := by
  rw [← toSpecState_H0_512_256]
  exact foldl_compress_lift_gen _ _

/-- SHA-512/224 variant of `foldl_compress_lift`: IV `H0_512_224` lifts
to `SHS.SHA512.H0_512_224` via `toSpecState_H0_512_224`. -/
theorem foldl_compress_lift_512_224 (data : ByteArray) :
    toSpecState ((implPaddedBlocks data).foldl
        (fun s b => Impl.compress s (Impl.toU64s b)) Impl.H0_512_224) =
      ((implPaddedBlocks data).map (fun b => toSpecBlock (Impl.toU64s b))).foldl
        SHS.SHA512.compress SHS.SHA512.H0_512_224 := by
  rw [← toSpecState_H0_512_224]
  exact foldl_compress_lift_gen _ _

end SHS.Equiv.SHA512.Pipeline
