# SHA-256 and SHA-224

The module `sha256` computes SHA-256 and SHA-224 of FIPS 180-4 [1].  Each export takes a message of `n` bytes packed eight to a word in an `Array UInt64`, as [the hashing guide](../README.md) describes, and returns the digest in the same packing as four words.  For every message of fewer than `2^61` bytes, a call returns without a trap and without allocating, and it leaves the message borrowed and every region of the caller's heap unchanged.  The digest's bytes, read most significant bit first, are the digest that [the transcription of FIPS 180-4](../Sha2/Spec/HashAlgorithms.lean) gives for the message's bits.  [The file theorems](File.lean) state that `build/verified/sha256.wasm` holds the module.

## Specification

The specification is the transcription of FIPS 180-4 that [the SHA-512 guide](../Sha512/README.md#specification) describes, with 32-bit words: padding in §5.1.1, parsing in §5.2.1, the initial values in §5.3.2 and §5.3.3, and the hash computation in §6.2 and §6.3.  The statements interpret the arguments and results through `bytes`, `Words4.bytes`, `bytesToBitMessage`, and `digestBitVec` or `digestBitVec224`, as that guide's table describes.

| Export | Function | Result | Call theorem |
|---|---|---|---|
| `sha256` | 11 | Four words: the digest of §6.2. | `sha256_call` |
| `sha224` | 12 | Four words whose first 28 bytes are the digest of §6.3.  The last four bytes are zero. | `sha224_call` |

Each export takes the message array and then the byte count `n`.  The theorems require `n < 2^61`, the limit of FIPS 180-4 §5.1.1 for whole bytes, under which the bit length `8 n` fits the 64-bit length field.  A count beyond the array's bytes is accepted, and the missing bytes read as zero in both the program and `bytes`.

## Implementation

The verified compiler's integers are `UInt64`, so [the program](Program.lean) holds each 32-bit word of the algorithm in the low half of a `UInt64` and ignores the high half.  Truncation to 32 bits commutes with addition and the bitwise operations, so only the shifts to the right and the rotations clear the high half first, with one mask for each of the functions `Σ_0`, `Σ_1`, `σ_0`, and `σ_1`.  `paddedWord` reads each 32-bit word of the padded and parsed message from the packed message: the high or low half of a byte-swapped message word, the word that holds the last message bytes and the byte `0x80`, zero, or a half of the bit length.  The compression keeps the message schedule in a window of sixteen words, so the loop state of the compression is 24 words, held in locals.  The additions follow the order of FIPS 180-4, and `pair` packs two digest words into one result word.  `hashFrom` hashes the rest of a message from the hash value of a prefix of whole blocks, and its length field counts the prefix, so that HMAC can hash the key block and the message without copying them.  SHA-256 and SHA-224 start from the initial value with no prefix.  `verified_compile` in [the compilation module](Compiled.lean) gives each export the theorem `ImplementsTables false`, so a call cannot trap and needs no premise about free memory.

## Proof

| Module | Content |
|---|---|
| [`WordProof.lean`](WordProof.lean) | 32-bit truncations of the helpers: `rot_toUInt32` and `shr_toUInt32` for a masked operand, `ch_toUInt32`, `maj_toUInt32`, and four sigma functions.  `bswap_high` and `bswap_low` give the two 32-bit words that a byte-swapped word holds, and `byteOf_pair_low` and `byteOf_pair_high` the bytes of a digest word. |
| [`PaddingProof.lean`](PaddingProof.lean) | `paddedWord_eq`: the 32-bit word of padded word `i` is the big-endian word of bytes `4 i` to `4 i + 3` of `implPaddedBytes`, the padding of the copied implementation. |
| [`CompressProof.lean`](CompressProof.lean) | `window`: after `t` rounds the window holds words `t` to `t + 15` of the specification's schedule.  `compress_spec`: `compress` is the specification's compression on the 32-bit words.  `compress_toVec32`: it is `Impl.compress`. |
| [`Proof.lean`](Proof.lean) | `hashFrom_toVec32`: after a prefix of whole blocks, the 32-bit state after every block of the rest of the message is the implementation's.  `foldl_append` splits the implementation's fold at the prefix, and `hashFrom_iv` covers the message without a prefix.  `sha256_bytes` and `sha224_bytes`: the digest bytes are those of `Impl.sha256` and `Impl.sha224`.  `sha256_spec` and `sha224_spec`: the digest is the transcription's. |
| [`Bytes.lean`](Bytes.lean) | `sha256_call`, `sha224_call`, and `sha256_module`, from the generated `implements` theorems through `Verified.ImplementsTables.call` and the equalities of `Proof.lean`. |
| [`File.lean`](File.lean) | `sha256_file` and `sha256_file_decode`: the emitted file holds the module's encoding and decodes to the module. |

The compression is proved against the specification's round and 64-word schedule, since the copied implementation keeps its schedule in a ring buffer.  `SHS.Equiv.SHA256.compress_correct` then gives equality with `Impl.compress`, because lifting a state to the specification's words is injective.  `sha256_spec` composes the program's equality with the implementation and `SHS.Equiv.SHA256.sha256_correct`.  Every theorem listed above depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  `sha256_bytes_collision` in [the Merkle–Damgård module](../MerkleDamgard.lean) shows that two distinct messages with equal digests give a collision of `SHS.SHA256.compress`.

## Tests

[The vector test](../../../tests/TestSupport/Hashing/Sha2Vectors.lean) hashes the NIST CAVP byte-oriented vectors [2] in [`data/hashing/sha2`](../../../data/hashing/sha2/NOTICE) with the native program and with the transcription.  For both functions, both agree with all 65 short and 64 long messages, and the program reproduces the 100 checkpoints of the Monte Carlo test of SHAVS §6.4 [3].

[The module cases](../../../tests/TestSupport/Hashing/Sha256Cases.lean) compare 145 calls in Wasmtime with native Lean.  They cover message lengths of 0 to 17, 50 to 70, and 110 to 130 bytes, which cross the boundaries at 56 and 64 bytes, and longer messages up to 4,096 bytes.  They also cover byte counts beyond the array and nonzero bytes after a message.  Every case requires that the call keep one block, the host's message, and make no allocation of its own.

```sh
tools/leanrun --timeout 2h lake build Library.Hashing.Sha256.Bytes
tools/leanrun --timeout 6h lake env lean --run tests/TestSupport/Hashing/Sha2Vectors.lean --only SHA256,SHA224
tests/verified/run.sh --cases sha256
tools/leanrun --timeout 10m lake env lean Library/Hashing/Sha256/File.lean
```

## References

1. National Institute of Standards and Technology, [*Secure Hash Standard (SHS)*](https://csrc.nist.gov/pubs/fips/180-4/final), FIPS PUB 180-4, 2015.
2. NIST Cryptographic Algorithm Validation Program, [Secure Hashing](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing), section "Test Vectors".
3. L. E. Bassham III and T. A. Hall, [*The Secure Hash Algorithm Validation System (SHAVS)*](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/SHAVS.pdf), NIST, updated May 21, 2014.
