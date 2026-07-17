# Lean String Support

This document is an unimplemented design proposal.  Runtime Lean `String` remains outside the accepted subset, and the [Development Plan](../plan.md) determines whether this work enters the active queue.  The [Language Specification](spec.md) and [LeanExe User Manual](manual.md) define the current text boundary.

## Current Boundary

LeanExe does not compile runtime Lean `String` values today.  It accepts ASCII `String` expressions only when extraction can consume them at compile time, such as through `String.toUTF8`, `String.length`, `String.isEmpty`, `String.append`, append notation, `==`, and `!=`.  The compiler rejects non-ASCII literal bytes in that path, because the lowered value becomes ordinary `ByteArray` data rather than a runtime `String`.

Runtime text currently uses `ByteArray` and `LeanExe.AsciiString`.  `ByteArray` is the public boundary for command input and output, while `AsciiString` is an ordinary source-level structure over `ByteArray` with an explicit ASCII invariant.  This design supports JSON field names, decimal text, unescaped ASCII strings, simple error messages, and generated protocol text without implementing Lean `Char`, UTF-8 decoding, or `String.Pos`.

This boundary should remain valid after runtime `String` support exists.  `AsciiString` is still the right type for byte-indexed ASCII protocols and formats that reject non-ASCII text by design.  Lean `String` should mean valid UTF-8 text with Lean-compatible character and position semantics, not an ASCII-only value with the official type name.

## Design Principle

Runtime `String` support should implement a subset of official Lean `String`, using checked Lean source as the semantic reference.  The compiler can support a small API first, but the representation and invariants should not conflict with later `Char` and `String.Pos` operations.  A program that uses accepted `String` operations should produce the same observable result under standard Lean and under generated WASM.

The compiler should reject unsupported `String` operations exactly.  It should not silently reinterpret `String` as raw bytes when the source operation depends on Unicode scalar values, UTF-8 character boundaries, or Lean's position rules.  It should also preserve the current ability to compile fixed ASCII strings into byte arrays without requiring runtime string allocation.

The first useful subset should reuse the existing heap and ownership machinery.  A runtime string can use a heap-owned UTF-8 byte buffer with a validity invariant, and public strings can share the pointer-length ABI shape used by `ByteArray` once input validation rules are explicit.  The implementation should prefer fresh owned buffers for early substring and conversion operations until borrowed-slice ownership for strings is specified.

## Representation

The simplest runtime representation is a validated UTF-8 byte sequence stored in the existing heap.  Internally, `String` can carry an owner, pointer, and byte length, using the same lifetime mechanics as `ByteArray`.  The value invariant is stronger than `ByteArray`: every runtime `String` must contain valid UTF-8, and operations that construct a `String` from arbitrary bytes must validate before returning `some`.

The public ABI can initially mirror `ByteArray`: pointer and byte length for parameters and results.  For parameters, the command adapter or library-call entry wrapper must validate the bytes before constructing a source-level `String`; invalid input should either reject at the adapter boundary or flow through a source-level `Option`/`Except` conversion API, depending on the selected entry shape.  For results, the host can read returned UTF-8 bytes by pointer and length, with the same memory lifetime rules used for byte arrays.

String literals need two lowering paths.  A literal used as a runtime `String` should allocate or reference a valid UTF-8 string value.  A literal consumed by compile-time `.toUTF8` should keep the current compile-time lowering, because those programs asked for bytes rather than a runtime string.

## First Runtime Slice

The first runtime slice should compile operations that treat a `String` as an immutable valid UTF-8 byte sequence without exposing `Char` iteration.  Good initial operations are string literals as runtime values, equality, append, append notation, `String.isEmpty`, byte-size or equivalent byte-count operations if the Lean API exposes the checked form, and `String.toUTF8`.  `String.fromUTF8?`, or a project-local wrapper with the same behavior, should validate arbitrary `ByteArray` input and return `Option String`.

This slice would make source programs less awkward without committing the compiler to the full character API immediately.  It would let command programs accept bytes, validate them as strings, combine fixed and runtime text, compare text, and emit bytes.  It would also give JSON and protocol examples a path for returned text values while preserving `AsciiString` for byte-indexed parser internals.

The slice should avoid `String.get`, `String.next`, `String.prev`, `String.foldl`, and `for c in s` until `Char` and position semantics are implemented.  Those operations do not mean byte indexing in Lean.  Accepting them before the compiler has a correct Unicode-scalar decoder would create a wrong subset.

## Char and Positions

Lean `Char` represents a Unicode scalar value, not a byte.  Supporting `Char` requires a runtime scalar representation, likely one `UInt32`-sized value with validation that excludes surrogate code points and values above `0x10FFFF`.  Character literals, equality, comparisons if accepted, and conversion between decoded UTF-8 sequences and `Char` must agree with Lean.

Lean string positions are byte positions into the UTF-8 representation, but valid operations must respect character boundaries.  A `String.Pos` can point to a byte offset, and operations such as `next`, `prev`, `get`, and extraction use the UTF-8 encoding to move or decode.  The compiler therefore needs boundary checks, decoding logic for one-byte through four-byte sequences, and exact behavior for end positions and invalid positions.

This is the main difference between useful byte-oriented text and real Lean `String`.  ByteArray and `AsciiString` can index by byte and keep parser loops simple.  Lean `String` indexing must decode Unicode scalar values and preserve Lean's position discipline, so it belongs in a later slice with dedicated tests.

## Compiler Work

The type classifier must accept `String` as a supported runtime type in selected positions.  It should continue to reject `Char` until the `Char` slice exists, and it should continue to reject unsupported string operations even when `String` values themselves have a layout.  The report command should distinguish accepted runtime string operations from compile-time-only string expressions.

The extractor needs primitive lowering for the accepted API.  Equality can scan UTF-8 bytes after checking lengths, append can allocate a new valid string by concatenating two already-valid byte sequences, and `toUTF8` can produce a byte array that shares or copies the string buffer according to the ownership rule chosen for the slice.  `fromUTF8?` needs a validator over `ByteArray` that returns `none` for malformed UTF-8 and `some` with an owned string for valid input.

The WASM lowering can reuse existing byte-copy loops, allocation, retain, and release paths.  The main new code is UTF-8 validation and, later, UTF-8 decoding for `Char`.  The implementation should make ownership conservative at first: allocate fresh results for append and validation, and avoid borrowed string slices until the ownership report can explain them.

## Testing Requirements

Every accepted `String` case should compare standard Lean execution with generated WASM under Wasmtime.  The first slice should test literals, append, equality, empty checks, conversion from valid bytes, rejection of invalid bytes through `fromUTF8?`, conversion back to bytes, branch-selected strings, structure fields containing strings, arrays of strings if the array element layout supports heap-bearing fields, and `Option` or `Except` results that carry strings.

UTF-8 validation tests need edge cases.  They should include ASCII, two-byte, three-byte, and four-byte valid characters; truncated sequences; continuation bytes without a starter; overlong encodings; surrogate encodings; and code points above the Unicode limit.  These tests should live in the standard Lean comparison corpus when the source-level API exists, with separate direct byte expectations for invalid encodings.

The later `Char` slice needs separate tests for decoding and position movement.  It should cover `get`, `next`, end-position behavior, extraction across multibyte characters, equality of strings with different byte lengths, and loops that count characters rather than bytes.  Those tests should not be added until the compiler has a documented `Char` representation.

## Recommended Sequence

| Step | Work | Acceptance criterion |
| ---- | ---- | -------------------- |
| 1 | Document runtime `String` layout and ABI | `spec.md` states the owner-pointer-length representation, validation invariant, and public boundary rules. |
| 2 | Add runtime `String` type classification | Entries and helpers can mention `String` only where the first runtime slice permits it; unsupported operations reject with string-specific diagnostics. |
| 3 | Lower literals, equality, append, `isEmpty`, and `toUTF8` | Standard Lean comparison tests pass for scalar, byte, and command-style outputs. |
| 4 | Add `fromUTF8?` validation | Valid byte arrays produce `some String`; malformed UTF-8 produces `none` without trapping. |
| 5 | Add heap-bearing containers | Structures, `Option`, `Except`, and arrays can carry strings when their layout rules match other heap-backed values. |
| 6 | Add `Char` and `String.Pos` | `get`, `next`, `prev`, extraction, and character iteration compile with UTF-8 boundary tests. |

The first five steps give useful runtime text support while avoiding the hardest Unicode operations.  Step six is the point where the compiler starts supporting Lean's character model rather than string-as-validated-bytes operations.  That separation keeps the early slice useful and gives the later slice a clear semantic target.
