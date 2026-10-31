# HMAC-SHA-256 and HMAC-SHA-512

The modules `hmac_sha256` and `hmac_sha512` compute HMAC of FIPS 198-1 [1] with SHA-256 and SHA-512 of FIPS 180-4 [2].  Each export takes a key of `kn` bytes and a message of `n` bytes, each packed eight to a word in an `Array UInt64` as [the hashing guide](../README.md) describes, and returns the MAC in the same packing as four or eight words.  For a key of fewer than `2^61` bytes and a message with `n + B < 2^61`, where `B` is the block size of 64 or 128 bytes, a call returns without a trap and without allocating, and it leaves both arrays borrowed and every region of the caller's heap unchanged.  The MAC's bytes, read most significant bit first, are the MAC that [the transcription of FIPS 198-1](Spec.lean) gives for the bits of the key and the message.  The file theorems [`File256.lean`](File256.lean) and [`File512.lean`](File512.lean) state that `build/verified/hmac_sha256.wasm` and `build/verified/hmac_sha512.wasm` hold the modules.

## Specification

[`Spec.lean`](Spec.lean) transcribes §2.3 and Table 1 of FIPS 198-1 on the bit strings of [the FIPS 180-4 transcription](../Sha2/Spec/HashAlgorithms.lean).  `keyBlock` is steps 1 to 3 of Table 1: a key of `B` bytes is `K_0`, a longer key is replaced by its digest followed by zero bits, and a shorter key is followed by zero bits.  `hmac` is steps 4 to 9, `H((K_0 ⊕ opad) || H((K_0 ⊕ ipad) || text))`, with `ipad` and `opad` the bytes `0x36` and `0x5c` repeated `B` times.  The standard counts `B` and the digest length `L` in bytes, and the transcription counts `L` in bits.  FIPS 180-4 defines SHA-256 and SHA-512 only for messages of fewer than `2^64` and `2^128` bits, so the transcription's `sha256` and `sha512` give zero outside those domains, which the theorems' hypotheses exclude.  A key is a string of whole bytes.  A MAC truncated as in §5 of FIPS 198-1 is a prefix of the returned bytes.

| Module | Export | Function | Result | Call theorem |
|---|---|---|---|---|
| `hmac_sha256` | `hmacSha256` | 13 | Four words: the 32-byte MAC. | `hmacSha256_call` |
| `hmac_sha512` | `hmacSha512` | 13 | Eight words: the 64-byte MAC. | `hmacSha512_call` |

Each export takes the key array, the key's byte count `kn`, the message array, and the message's byte count `n`.  The theorems require `kn < 2^61` and `n + B < 2^61`, under which the inner message `(K_0 ⊕ ipad) || text` satisfies the limit of FIPS 180-4 for whole bytes.  A count beyond an array's bytes is accepted, and the missing bytes read as zero in both the program and `bytes`.

## Implementation

[The program](Program.lean) forms `K_0` as one block of sixteen words.  A key of more than `B` bytes is hashed in place with `hashFrom`, and its digest words fill the first half of the block.  A shorter key is read a word at a time in big-endian order, and the word that holds the key's last bytes masks the bytes after them.  `xorBlock` XORs every word of the block with the pad byte repeated across a word.  The inner hash compresses `K_0 ⊕ ipad` and continues with the message through `hashFrom`, whose length field counts the key block, so the message is never copied.  The outer hash compresses `K_0 ⊕ opad` and then one block that holds the inner digest, the byte `0x80`, and the bit length of the outer message: 768 for SHA-256 and 1,536 for SHA-512.  No call allocates.  Each module holds the compression and block loop of its own hash function.  Both families name their functions `compress`, `hashFrom`, and so on, and the verified compiler names each export by the last component of its definition's name, so one module cannot hold both.

## Proof

| Module | Content |
|---|---|
| [`Bits.lean`](Bits.lean) | Bits of byte strings: `bits_append`, `bits_appendZeros`, `bits_xorBytes`, and `bitsOf_fromBits`.  The bytes of a digest and of a short key block, and `xorBlock_get`. |
| [`Proof256.lean`](Proof256.lean) | `implHmac256_spec`: HMAC built on the copied implementation `SHS.SHA256.Impl.sha256` is the transcription on bits.  `keyBlock256_get`: the program's key block is `K_0`.  `inner_toVec32` and `outer_toVec32`: the program's inner and outer hash values are the implementation's states.  `hmacSha256_bytes` and `hmacSha256_spec`: the MAC bytes are those of `implHmac256` and the transcription's. |
| [`Proof512.lean`](Proof512.lean) | Same for SHA-512, with blocks of 128 bytes and words of eight bytes. |
| [`Bytes.lean`](Bytes.lean) | `hmacSha256_call`, `hmacSha512_call`, `hmacSha256_module`, and `hmacSha512_module`, from the generated `implements` theorems, `Verified.ImplementsTables.call`, `hmacSha256_spec`, and `hmacSha512_spec`. |
| [`File256.lean`](File256.lean), [`File512.lean`](File512.lean) | File theorems: the emitted files hold the modules' encodings and decode to the modules. |

The proofs reuse the prefix theorems of the two families: `hashFrom_toVec32` and `hashFrom_toVec` state the hash value after a prefix of whole blocks, and `foldl_append` splits the copied implementation's fold at the prefix.  The inner message's prefix is the one block `K_0 ⊕ ipad`, and the outer message is the block `K_0 ⊕ opad` followed by the 32 or 64 digest bytes, whose padding fills one more block.  Every theorem listed above depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Tests

[The vector test](../../../tests/TestSupport/Hashing/HmacVectors.lean) checks the native programs and the transcription against the seven test cases of RFC 4231 §4 [3], whose case 5 gives the first 16 bytes of each MAC.  It then compares the programs with the transcription for keys of 0 to 140 bytes and of 200, 255, 256, and 1,000 bytes, against messages of 0, 1, 55, 56, 63, 64, 111, 112, 127, 128, and 300 bytes, which put the inner message on each side of the padding boundaries of both hash functions: 1,595 pairs for each function.  Keys and messages are followed by a word of nonzero bytes, which the MAC must ignore.

[The module cases](../../../tests/TestSupport/Hashing/HmacCases.lean) compare 136 calls of each module in Wasmtime with native Lean.  They cover key lengths of 0, 1, 8, 31, 32, 63, 64, 65, 127, 128, 129, and 200 bytes against the eleven message lengths above, and key counts beyond the key array.  Every case requires that the call keep two blocks, the host's key and message, and make no allocation of its own.

```sh
tools/leanrun --timeout 2h lake build Library.Hashing.Hmac.Bytes TestSupport.Hashing.Packing
tools/leanrun --timeout 30m lake env lean --run tests/TestSupport/Hashing/HmacVectors.lean
tests/verified/run.sh --cases hmac_sha256
tests/verified/run.sh --cases hmac_sha512
tools/leanrun --timeout 10m lake env lean Library/Hashing/Hmac/File256.lean
tools/leanrun --timeout 10m lake env lean Library/Hashing/Hmac/File512.lean
```

## References

1. National Institute of Standards and Technology, [*The Keyed-Hash Message Authentication Code (HMAC)*](https://csrc.nist.gov/pubs/fips/198-1/final), FIPS PUB 198-1, 2008.
2. National Institute of Standards and Technology, [*Secure Hash Standard (SHS)*](https://csrc.nist.gov/pubs/fips/180-4/final), FIPS PUB 180-4, 2015.
3. M. Nystrom, [*Identifiers and Test Vectors for HMAC-SHA-224, HMAC-SHA-256, HMAC-SHA-384, and HMAC-SHA-512*](https://www.rfc-editor.org/rfc/rfc4231), RFC 4231, 2005.
