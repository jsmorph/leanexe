# Hashing

The hash functions take a message of `n` bytes as an `Array UInt64` holding eight bytes per word in little-endian order, together with the byte count `n`.  Byte `i` is bits `8 (i % 8)` to `8 (i % 8) + 7` of word `i / 8`, the layout of Wasm memory, so a file read as little-endian words is a message.  A digest uses the same packing in a structure of words, so that a call returns its digest as several WebAssembly results and allocates nothing.  [The word module](Words/Program.lean) defines the structures, `bswap`, and the rotation helper, and [the byte module](Words/Bytes.lean) defines the bytes that packed words denote, which the correctness theorems use to state their arguments and results.

| Family | Functions | Proved results |
|---|---|---|
| [SHA-256](Sha256/README.md) | SHA-256 and SHA-224 of FIPS 180-4 | For messages of fewer than `2^61` bytes, each export returns without a trap the digest of a Lean transcription of FIPS 180-4, and the emitted file holds the module. |
| [SHA-512](Sha512/README.md) | SHA-512, SHA-384, SHA-512/256, and SHA-512/224 of FIPS 180-4 | The same, for the four functions of the SHA-512 compression. |

[`Sha2`](Sha2/NOTICE) holds material copied from fips-180-4-lean: the transcription of FIPS 180-4 in `Spec`, an implementation on bytes in `Impl`, and its equivalence proofs in `Equiv`.  The NOTICE gives the source, the license, and the changes made to build under Lean 4.34.  The SHA-256 and SHA-512 proofs relate their programs to `Impl` and use `Equiv`'s theorems about it.  The NIST test vectors are in [`data/hashing`](../../data/hashing/sha2/NOTICE).
