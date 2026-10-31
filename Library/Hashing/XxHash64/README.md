# XXH64

The module `xxhash64` computes XXH64 of the xxHash specification [1].  Its export takes a message of `n` bytes packed eight to a word as [the hashing guide](../README.md) describes and a 64-bit seed.  It returns without a trap one word, the 64-bit value that [the transcription](Spec.lean) gives for the message and the seed.  Step 7 of the specification writes that value most significant byte first for display, and the result word is the value itself.  The message stays borrowed, and every region of the caller's heap keeps its bytes.  The file theorems of [`File.lean`](File.lean) state that `build/verified/xxhash64.wasm` holds the module.

## Specification

[`Spec.lean`](Spec.lean) transcribes the "XXH64 Algorithm Description" of version 0.2.0 of the specification on 64-bit words of type `UInt64`, with addition, subtraction, and multiplication modulo `2^64`, shifts, XOR, and rotation to the left from `BitVec.rotateLeft`.  Input is read little-endian.  `xxh64 m seed` follows the seven steps: the four accumulators, the stripes of 32 bytes with their four lanes, the convergence with `mergeAccumulator`, the length, the remaining input in lanes of 8 bytes, at most one lane of 4 bytes, and single bytes, and the avalanche.  An input of fewer than 32 bytes starts from the single accumulator `seed + PRIME64_5` instead of steps 1 to 3.  The loops of step 2 and of the lanes of 8 bytes take 32 or 8 bytes from the input while that many remain, as the specification's pseudocode does.  An independent review compared the transcription with the specification and found no discrepancy in its definitions.  A count beyond an array's bytes is accepted, and the missing bytes read as zero in both the program and the theorems.

| Export | Function | Arguments | Result | Call theorem |
|---|---|---|---|---|
| `xxh64` | 5 | Message array, `n`, and seed. | XXH64 of the `n` bytes with the seed. | `xxh64_call` |

## Implementation

[The program](Program.lean) holds the four accumulators in the transcription's structure and computes a rotation as two shifts and an OR.  The packing makes lane `t` of stripe `j` word `4 j + t` of the array, the lanes of 8 bytes of step 5 the words from `4 ⌊n/32⌋` to `⌊n/8⌋ - 1`, the lane of 4 bytes the low half of word `⌊n/8⌋`, and each remaining byte a byte of that word.  The program reads every lane and byte in place.  `start`, `lanes8`, `lane4`, and `bytes` are inline phases of `xxh64`, and `stripeAt`, `converge`, and `avalanche` compile as functions.  No function allocates, as `compiled.xxh64.bound_eq` states.

## Proof

| Module | Content |
|---|---|
| [`Proof.lean`](Proof.lean) | `rotl_1` to `rotl_31`, the program's rotations at the amounts that XXH64 uses; `round_eq`, `converge_eq`, and `avalanche_eq`; `lane_le`, `half_le`, and `byte_eq`, which read the message's lanes, half lanes, and bytes from the array; `stripes_from` and `lanes8_from` for the two loops; `start_eq`, `lanes8_eq`, `lane4_eq`, and `bytes_eq` for the phases; and `xxh64_eq`. |
| [`Compiled.lean`](Compiled.lean) | Verified compilation of `stripeAt`, `converge`, `avalanche`, and `xxh64`. |
| [`Bytes.lean`](Bytes.lean) | `xxh64_export` and `xxh64_call`, from the generated `implements` theorem through `Verified.ImplementsTables.call` and `xxh64_eq`. |
| [`File.lean`](File.lean) | File theorems: the emitted file holds the module's encoding and decodes to the module. |

`stripes_from` and `lanes8_from` proceed by induction on the number of stripes or lanes that remain, and `lane_le` reads the eight bytes of a lane as a word by the little-endian lemmas of [`LittleEndian.lean`](../../Bytes/LittleEndian.lean).  After the loops the remaining input is the message from position `8 ⌊n/8⌋`, and after the lane of 4 bytes it is the message from position `n - n mod 4`, which `bytes` reads.  Every theorem listed above depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Tests

The executable `xxhash64-vectors`, built from [the vector check](../../../tests/TestSupport/Hashing/XxHash64Vectors.lean), checks the transcription and the program on [the vectors](../../../data/hashing/xxhash64/NOTICE) of the xxHash repository's sanity test [2].  Each vector hashes the first bytes of the test's pseudorandom buffer, for every length from 0 to 4,160 bytes with the seeds 0 and `0x9E3779B1`, and the transcription and the program agree on all 8,322.

[The module cases](../../../tests/TestSupport/Hashing/XxHash64Cases.lean) compare 166 calls in Wasmtime with native Lean: messages of 0 to 40 bytes, which reach every case of step 5 and the first stripes, lengths around multiples of 32 and of 4,096, three seeds, and counts beyond the array.  Each case requires that the call keep the host's message and allocate nothing of its own.

```sh
tools/leanrun --timeout 1h lake build Library.Hashing.XxHash64.Bytes xxhash64-vectors
tools/leanrun --timeout 10m .lake/build/bin/xxhash64-vectors
tests/verified/run.sh --cases xxhash64
tools/leanrun --timeout 10m lake env lean Library/Hashing/XxHash64/File.lean
```

## References

1. Y. Collet, [*xxHash fast digest algorithm*](https://github.com/Cyan4973/xxHash/blob/dev/doc/xxhash_spec.md), version 0.2.0, 2023.
2. Y. Collet, [*xxHash*](https://github.com/Cyan4973/xxHash), `tests/sanity_test_vectors.h` and `tests/sanity_test.c`.
