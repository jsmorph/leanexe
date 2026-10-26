# SHA-512, SHA-384, SHA-512/256, and SHA-512/224

The module `sha512` computes the four hash functions of FIPS 180-4 [1] that share the SHA-512 compression.  Each export takes a message of `n` bytes packed eight to a word in an `Array UInt64`, as [the hashing guide](../README.md) describes, and returns the digest in the same packing as eight, six, or four words.  For every message of fewer than `2^61` bytes, a call returns without a trap and without allocating, and it leaves the message borrowed and every region of the caller's heap unchanged.  The digest's bytes, read most significant bit first, are the digest that [the transcription of FIPS 180-4](../Sha2/Spec/HashAlgorithms.lean) gives for the message's bits.  [The file theorems](File.lean) state that `build/verified/sha512.wasm` holds the module.

## Specification

The specification is [`Library/Hashing/Sha2/Spec`](../Sha2/Spec.lean), a literate Lean transcription of FIPS 180-4 by the author of fips-180-4-lean [2], copied with the changes that [the NOTICE](../Sha2/NOTICE) lists.  Its messages are lists of bits, its words are `BitVec 64`, and each definition follows a numbered section of the standard: padding in §5.1.2, parsing in §5.2.2, the initial values in §5.3, and the hash computation in §6.4 to §6.7.  The statements interpret the program's arguments and results through four definitions.  `bytes` is in [the packed-byte module](../../Bytes/Packed.lean), the digest definitions are in [the digest module](../Words/Bytes.lean), and the other two come with the copied proofs.

| Definition | Meaning |
|---|---|
| `bytes msg n` | The first `n` bytes of `msg`.  Byte `i` is bits `8 (i % 8)` to `8 (i % 8) + 7` of word `i / 8`, and a word past the end of the array reads as zero, as a read past the end does in the compiled code. |
| `Words8.bytes`, `Words6.bytes`, `Words4.bytes k` | The digest's 64, 48, or first `k` bytes in the same packing. |
| `bytesToBitMessage` | A byte array as the bit list of FIPS 180-4, each byte's most significant bit first. |
| `digestBitVec512`, `digestBitVec384`, `digestBitVec512_256`, `digestBitVec512_224` | A digest's bytes as one bit vector, the first byte most significant, the type of the transcription's digests. |

| Export | Function | Result | Call theorem |
|---|---|---|---|
| `sha512` | 13 | Eight words: the digest of §6.4. | `sha512_call` |
| `sha384` | 14 | Six words: the digest of §6.5. | `sha384_call` |
| `sha512_256` | 15 | Four words: the digest of §6.7. | `sha512_256_call` |
| `sha512_224` | 16 | Four words whose first 28 bytes are the digest of §6.6.  The last four bytes are zero. | `sha512_224_call` |

Each export takes the message array and then the byte count `n`.  The theorems require `n < 2^61`, under which the bit length `8 n` fits the low word of the 128-bit length field; the copied padding proof assumes that bound, and FIPS 180-4 permits up to `2^128 - 1` bits.  A count beyond the array's bytes is accepted, and the missing bytes read as zero in both the program and `bytes`.  The transcription defines messages of any bit length, and these theorems cover messages of whole bytes.

## Implementation

[The program](Program.lean) reads each word of the padded and parsed message with `paddedWord`, which returns a byte-swapped message word, the word that holds the last message bytes and the byte `0x80`, zero, or a word of the bit length.  No padded copy of the message exists.  The compression keeps the message schedule in a window of sixteen words that advances by one word in each of the 80 rounds, so the loop state of the compression is 24 words, held in locals.  The round constants are a table in a data segment, which the exports pass to the functions that read them.  `hashFrom` hashes the rest of a message from the hash value of a prefix of whole blocks, and its length field counts the prefix, so that HMAC can hash the key block and the message without copying them.  SHA-512 and its companions start from the initial value with no prefix.  The additions follow the order of the copied implementation `SHS.SHA512.Impl`, so that the program's round, schedule recurrence, and final addition equal the implementation's by definition.

`verified_compile` in [the compilation module](Compiled.lean) gives each export the theorem `ImplementsTables false`: the call cannot trap, so no premise about free memory is needed.  The flag is false because the message is borrowed, no function builds or updates an array, and the results are structures of words.

## Proof

| Module | Content |
|---|---|
| [`Words/Proof.lean`](../Words/Proof.lean) | `bswap_eq`: `bswap` reverses the bytes of a word.  `byteOf_marked` gives the bytes of the word that holds the last message bytes and `0x80`. |
| [`PaddingProof.lean`](PaddingProof.lean) | `paddedWord_eq`: word `i` of the padded message is the big-endian word of bytes `8 i` to `8 i + 7` of `implPaddedBytes`, the padding of the copied implementation. |
| [`CompressProof.lean`](CompressProof.lean) | `window`: after `t` rounds the window holds schedule words `t` to `t + 15`.  `compress_toVec`: `compress` is `Impl.compress`. |
| [`Proof.lean`](Proof.lean) | `hashFrom_toVec`: after a prefix of whole blocks, the state after every block of the rest of the message is the implementation's.  `foldl_append` splits the implementation's fold at the prefix, and `hashFrom_iv` covers the message without a prefix.  `sha512_bytes` and its companions: the digest bytes are those of `Impl.sha512`.  `sha512_spec` and its companions: the digest is the transcription's. |
| [`Bytes.lean`](Bytes.lean) | The four call theorems and `sha512_module`, from the generated `implements` theorems and the equalities of `Proof.lean`. |
| [`File.lean`](File.lean) | `sha512_file` and `sha512_file_decode`: the emitted file holds the module's encoding and decodes to the module. |

`sha512_spec` composes the program's equality with the copied implementation and `SHS.Equiv.SHA512.sha512_correct`, which equates that implementation with the transcription.  Every theorem listed above depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  `sha512_bytes_collision` in [the Merkle–Damgård module](../MerkleDamgard.lean) shows that two distinct messages with equal digests give a collision of `SHS.SHA512.compress`.  The copied proofs, ported to Lean 4.34, are under [`Library/Hashing/Sha2/Equiv`](../Sha2/Equiv/SHA512/Main.lean).

## Tests

[The vector test](../../../tests/TestSupport/Hashing/Sha2Vectors.lean) hashes the NIST CAVP byte-oriented vectors [3] in [`data/hashing/sha2`](../../../data/hashing/sha2/NOTICE) with the native program and with the transcription.  For each of the four functions, both agree with all 129 short and 128 long messages, and the program reproduces the 100 checkpoints of the Monte Carlo test of SHAVS §6.4 [4].  The whole test takes about six minutes.  The packed messages are followed by a word of nonzero bytes, which the digest must ignore.

[The module cases](../../../tests/TestSupport/Hashing/Sha512Cases.lean) compare 405 calls in Wasmtime with native Lean.  They cover message lengths of 0 to 17, 100 to 140, and 230 to 260 bytes, which cross the boundaries at 112 and 128 bytes, and longer messages up to 4,096 bytes.  They also cover byte counts beyond the array and nonzero bytes after a message.  Every case requires that the call keep one block, the host's message, and make no allocation of its own.

```sh
tools/leanrun --timeout 2h lake build Library.Hashing.Sha512.Bytes
tools/leanrun --timeout 6h lake env lean --run tests/TestSupport/Hashing/Sha2Vectors.lean
tests/verified/run.sh --cases sha512
tools/leanrun --timeout 10m lake env lean Library/Hashing/Sha512/File.lean
```

The vector test takes `--no-monte` to skip the Monte Carlo checkpoints and `--no-spec` to skip the transcription.  The case run writes `build/verified/sha512.wasm`, which the file theorems then read.

## References

1. National Institute of Standards and Technology, [*Secure Hash Standard (SHS)*](https://csrc.nist.gov/pubs/fips/180-4/final), FIPS PUB 180-4, 2015.
2. remix7531, [fips-180-4-lean](https://github.com/remix7531/fips-180-4-lean/tree/0018b08f3458553ad511e92a96336979c1e0c45a), a literate Lean transcription of FIPS 180-4 with an implementation and equivalence proofs.
3. NIST Cryptographic Algorithm Validation Program, [Secure Hashing](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing) test vectors.
4. L. E. Bassham III and T. A. Hall, [*The Secure Hash Algorithm Validation System (SHAVS)*](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/SHAVS.pdf), NIST, updated May 21, 2014.
