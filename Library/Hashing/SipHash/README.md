# SipHash

The module `siphash` computes SipHash-2-4 and SipHash-1-3 of the SipHash paper by Aumasson and Bernstein [1].  Each export takes a 128-bit key as two words, the little-endian words of its 16 bytes, and a message of `n` bytes packed eight to a word as [the hashing guide](../README.md) describes.  It returns without a trap one word, the 64-bit value that [the transcription](Spec.lean) gives for the key and the message.  The reference implementation [2] and OpenSSL write that value as eight bytes, least significant first, which is the packing of the result word.  The message stays borrowed, and every region of the caller's heap keeps its bytes.  The file theorems of [`File.lean`](File.lean) state that `build/verified/siphash.wasm` holds the module.

## Specification

[`Spec.lean`](Spec.lean) transcribes §2 of the paper, the definition of SipHash-c-d for every `c` and `d`, on 64-bit words of type `UInt64` with addition modulo `2^64`, XOR, and rotation to the left from `BitVec.rotateLeft`.  `sipRound` performs the operations of SipRound row by row, the left column before the right, as Fig. 2.2 draws them.  `messageWords` reads the message, null bytes, and a last byte of `b mod 256` as `⌈(b + 1)/8⌉` little-endian words, and `sipHash c d k m` follows the three steps of §2.  §2 calls `b mod 256` a positive integer, which it is not when `b` is a multiple of 256.  The byte is then zero, as in the reference implementation.  An independent review compared the transcription with §2 and the reference code and found no discrepancy in its definitions.

SipHash-2-4 is the paper's proposal, and CPython 3.11 and later hash `str` and `bytes` with SipHash-1-3 [4].  §2 defines both as members of the family.  The reference implementation's README also describes a 128-bit output, which the paper does not define, and the module computes the 64-bit output alone.  A count beyond an array's bytes is accepted, and the missing bytes read as zero in both the program and the theorems.

| Export | Function | Arguments | Result | Call theorem |
|---|---|---|---|---|
| `siphash24` | 7 | `k0`, `k1`, the message array, and `n`. | SipHash-2-4 of the key and the `n` bytes. | `siphash24_call` |
| `siphash13` | 8 | `k0`, `k1`, the message array, and `n`. | SipHash-1-3 of the key and the `n` bytes. | `siphash13_call` |

## Implementation

[The program](Program.lean) holds the state in the transcription's structure of four words and computes a rotation as two shifts and an OR.  `sipRound` writes SipRound's fourteen operations as nine bindings, and `rounds` iterates it with `LeanExe.loop`.  The packing makes word `i` of the message array the message word `m_i` of §2 for `i < n / 8`, so `sipHashWith` reads those words in place.  `lastWord` masks the remaining `n mod 8` bytes of the next word and places `n` shifted left by 56 bits in the top byte, which keeps `n mod 256`.  `siphash24` and `siphash13` call `sipHashWith` with their round counts.  No function allocates, as `compiled.sipHashWith.bound_eq` states.

## Proof

| Module | Content |
|---|---|
| [`Proof.lean`](Proof.lean) | `rotl_13` to `rotl_32`, the program's rotations at SipRound's amounts; `sipRound_eq`, `rounds_eq`, and `compress_eq`; `le64_bytes`, which reads a word's eight bytes as the word; `lastWord_toNat` and `messageWords_eq` for the message words; and `sipHashWith_eq`, `siphash24_spec`, and `siphash13_spec`. |
| [`Compiled.lean`](Compiled.lean) | Verified compilation of the program's functions, from `sipRound` to `siphash13`. |
| [`Bytes.lean`](Bytes.lean) | Two export facts and two call theorems, from the generated `implements` theorems through `Verified.ImplementsTables.call` and the theorems above. |
| [`File.lean`](File.lean) | File theorems: the emitted file holds the module's encoding and decodes to the module. |

`messageWords_eq` describes the padded string of §2 byte by byte: a message byte below `n`, the length byte at the last position, and zero elsewhere.  The full words then read as the array's words by `le64_bytes`, and the last word reads as `lastWord` by sums of base-256 digits.  The key's bytes are the bytes of the array `#[k0, k1]`, packed as a message is.  Every theorem listed above depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Tests

The executable `siphash-vectors`, built from [the vector check](../../../tests/TestSupport/Hashing/SipHashVectors.lean), runs the example of Appendix A of the paper and requires the transcription to reach each of the appendix's intermediate states.  The transcription and the programs then run [the vectors](../../../data/hashing/siphash/NOTICE) of `data/hashing/siphash`: the 64 SipHash-2-4 vectors of the reference implementation, for messages of 0 to 63 bytes, and the SipHash-2-4 and SipHash-1-3 tags that OpenSSL [3] computes for pseudorandom keys and messages of every length to 256 bytes and of ten lengths to 4,097 bytes.  `generate.py` checks OpenSSL against the reference vectors and the appendix before it writes them.  All 331 messages agree.

[The module cases](../../../tests/TestSupport/Hashing/SipHashCases.lean) compare 266 calls in Wasmtime with native Lean: the two functions under four keys for messages around multiples of 8 and 256, counts beyond the array, and SipRound of two states.  Each hash case requires that the call keep the host's message and allocate nothing of its own.

```sh
tools/leanrun --timeout 1h lake build Library.Hashing.SipHash.Bytes siphash-vectors
tools/leanrun --timeout 10m .lake/build/bin/siphash-vectors
tests/verified/run.sh --cases siphash
tools/leanrun --timeout 10m lake env lean Library/Hashing/SipHash/File.lean
```

## References

1. J.-P. Aumasson and D. J. Bernstein, [*SipHash: a fast short-input PRF*](https://cr.yp.to/siphash/siphash-20120918.pdf), INDOCRYPT 2012, version of 2012-09-18.
2. J.-P. Aumasson and D. J. Bernstein, [*SipHash reference implementation*](https://github.com/veorq/SipHash).
3. The OpenSSL Project, [*EVP_MAC-Siphash*](https://docs.openssl.org/3.5/man7/EVP_MAC-Siphash/), OpenSSL 3.5.
4. Python Software Foundation, [*What's New In Python 3.11*](https://docs.python.org/3/whatsnew/3.11.html), the entry for bpo-29410.
