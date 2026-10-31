# SHA-3 and SHAKE

The module `sha3` computes SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, and SHAKE256 of FIPS 202 [1].  Each export takes a message of `n` bytes packed eight to a word as [the hashing guide](../README.md) describes.  For `n < 2^61`, a hash export returns without a trap and without allocating the digest in the same packing, and the digest's bytes, read least significant bit first, are the digest that [the transcription of FIPS 202](Spec.lean) gives for the message's bits in the same order.  That order is the one in which Appendix B.1 of the standard converts bytes to strings.  A SHAKE export also takes an output length `d < 2^61` in bytes, and with room in the heap for `8 ⌈d/8⌉ + 56` bytes it returns an owned array of `⌈d/8⌉` words whose first `d` bytes are the transcription's output of `8 d` bits and whose other bytes are zero.  The message stays borrowed, and every region of the caller's heap keeps its bytes.  The file theorems of [`File.lean`](File.lean) state that `build/verified/sha3.wasm` holds the module.

## Specification

[`Spec.lean`](Spec.lean) transcribes §2.3, §3 to §6, and Appendix B.1 of FIPS 202 on strings of bits, `List Bool` with `X[0]` first.  KECCAK-p is generic over the seven widths `b = 25 · 2^ℓ`, and the SHA-3 functions use `ℓ = 6` and 24 rounds.  A state array is a function of its coordinates `x`, `y`, and `z`, and θ, π, and χ give their output bit by bit, as their algorithms' steps over all triples do.  ρ separates the walk of Algorithm 2 over the lanes, which `rhoSteps_table2` checks against Table 2, from its assignment, and ι separates the lane value `RC` of steps 2 and 3 of Algorithm 6 from steps 1 and 4.  The standard's `m mod n` takes negative integers in θ, ρ, and pad10*1 to `[0, n)`, as the integer `emod` does.  The squeeze of Algorithm 8 takes at most `d / r + 1` passes, which reach `d` bits for a rate `r > 0` and outputs of at least `r` bits.

Compiled code computes KECCAK-p as `keccakPRun`, which holds the state between rounds as the array of its bits and computes each round's `RC` once.  The `csimp` theorem `keccakP_eq_run` proves it equal to `keccakP`, Algorithm 7 on state arrays.  An independent review compared the transcription with the standard and found no discrepancy.  Step 1 of Algorithm 10 reads `0 ≤ i < 2m − 1`, which omits the last digit that the displayed string and step 2a use, and `h2b` reads all `2m` digits.  A count beyond an array's bytes is accepted, and the missing bytes read as zero in both the program and the theorems.  FIPS 202 §7 allows a conforming implementation to restrict the message and output lengths it supports, and the module takes whole bytes of each.

| Export | Function | Arguments | Result | Call theorem |
|---|---|---|---|---|
| `sha3_224` | 12 | Message array and `n`. | `Words4`: the 28-byte digest, with the last four bytes zero. | `sha3_224_call` |
| `sha3_256` | 13 | Message array and `n`. | `Words4`: the 32-byte digest. | `sha3_256_call` |
| `sha3_384` | 14 | Message array and `n`. | `Words6`: the 48-byte digest. | `sha3_384_call` |
| `sha3_512` | 15 | Message array and `n`. | `Words8`: the 64-byte digest. | `sha3_512_call` |
| `shake128` | 19 | Message array, `n`, and `d`. | Owned array of `⌈d/8⌉` words. | `shake128_call` |
| `shake256` | 20 | Message array, `n`, and `d`. | Owned array of `⌈d/8⌉` words. | `shake256_call` |

## Implementation

[The program](Program.lean) holds the state in a structure of 25 lanes, field `a(x + 5y)` for lane `(x, y)`.  Word `i` of the packed message holds bits `64 i` to `64 i + 63` of the message's string, which are lane `i`, so message words enter the state and the digest leaves it without a byte swap.  `thetaL`, `rhoPiL`, `chiL`, and `iotaL` give the step mappings on lanes, with ρ and π in one function that rotates each lane by its offset of Table 2 modulo 64.  They compile as functions, whose record parameter is borrowed, and the structure holds no array, so a call copies nothing.  `keccakF` is 24 calls of `round` with the lane values of `RC` as literals.

`paddedWord` reads each word of the padded message from the packed message: the message's bytes, the byte at position `n` that holds the suffix and the padding's first bit, `0x06` for the hash functions and `0x1F` for SHAKE, and the padding's last bit at the top of the last word.  `absorb` XORs each block into the first `rw` lanes and permutes, with `rw` of 18, 17, 13, and 9 lanes for the hash functions and 21 and 17 for SHAKE128 and SHAKE256.  A digest is the first lanes, which every rate exceeds.  `shakeWith` fills one block of its output in place per pass of the squeeze, permutes between passes, and masks the bytes past `d` in the last word.  The hash functions allocate nothing, and SHAKE's allocation bound, `compiled.shakeWith.bound_eq`, is one block of `⌈d/8⌉` words.

## Proof

| Module | Content |
|---|---|
| [`RoundProof.lean`](RoundProof.lean) | `toState`, which reads the lanes as a state array; `thetaL_spec`, `rhoPiL_spec`, `chiL_spec`, and `iotaL_spec` for the step functions; the 24 constants against `roundConstant 6 k`; and `keccakF_spec`, the 24 rounds of Algorithm 7. |
| [`SpongeProof.lean`](SpongeProof.lean) | `toStateArray_toBits`, which shows that §3.1.2 inverts §3.1.3; `keccakP_lanes`; `xorBlock_spec` for step 6 of Algorithm 8; `padded_eq`, which equates the message, its suffix, and pad10*1 with the bits of `paddedWord`; and `absorb_spec`. |
| [`Proof.lean`](Proof.lean) | `sponge_absorb`, `squeeze_one`, and `sha3_224_spec` to `sha3_512_spec`: the bits of the digest's bytes are the transcription's digest. |
| [`ShakeProof.lean`](ShakeProof.lean) | `squeeze_stream`, which reads the squeeze as the first `d` bits of the rate prefixes of the iterated states; the invariant of the squeezing loop; and `shake128_spec`, `shake256_spec`, `shakeWith_size`, and `shakeWith_tail`. |
| [`Compiled.lean`](Compiled.lean) | Verified compilation of the program's functions, from `thetaL` to `shake256`. |
| [`Bytes.lean`](Bytes.lean) | Six export facts and six call theorems, from the generated `implements` and `trapFree` theorems through `Verified.ImplementsTables.call` and the theorems above. |
| [`File.lean`](File.lean) | File theorems: the emitted file holds the module's encoding and decodes to the module. |

`padded_eq` splits the padded string into the message, the byte that holds the suffix, and the padding after it, and `pad101_zeros` gives the zeros of pad10*1 in closed form.  The squeeze of a hash function takes one pass, since every digest is shorter than its rate.  Every theorem listed above depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Tests

The executable `sha3-vectors`, built from [the vector check](../../../tests/TestSupport/Hashing/Sha3Vectors.lean), checks the transcription and the programs on the NIST CAVP vectors in [`data/hashing/sha3`](../../../data/hashing/sha3/NOTICE) [2].  The transcription agrees with all 12,560 vectors: the short and long messages of the six functions, the variable outputs of the two SHAKE functions, and 8,518 bit-oriented short messages, which reach every length.  The bit-oriented files write a message of `Len` bits as `h2b(Msg, Len)` of Appendix B.1, which SHA3VS [3] does not state and which the files match.  The check of the transcription takes about three hours in one process, and `--only` runs one function per process.  The programs agree with the 4,642 byte-oriented vectors, the 100 checkpoints of each Monte Carlo test among them, in a few seconds.

[The module cases](../../../tests/TestSupport/Hashing/Sha3Cases.lean) compare 384 calls in Wasmtime with native Lean: the four digests of messages whose lengths reach the ends of the blocks of every rate, SHAKE outputs of lengths around the rates, counts beyond the array, and KECCAK-p of two states.  A hash case requires that the call keep the host's message and allocate nothing of its own, and a SHAKE case that it keep the message and its output and allocate nothing else.

```sh
tools/leanrun --timeout 2h lake build Library.Hashing.Sha3.Bytes sha3-vectors
tools/leanrun --timeout 30m .lake/build/bin/sha3-vectors --no-spec
tools/leanrun --timeout 4h .lake/build/bin/sha3-vectors --no-program
tests/verified/run.sh --cases sha3
tools/leanrun --timeout 10m lake env lean Library/Hashing/Sha3/File.lean
```

## References

1. National Institute of Standards and Technology, [*SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf), FIPS PUB 202, 2015.
2. National Institute of Standards and Technology, [*Cryptographic Algorithm Validation Program: Secure Hashing*](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing), section "Test Vectors", FIPS 202.
3. National Institute of Standards and Technology, [*The Secure Hash Algorithm 3 Validation System (SHA3VS)*](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha3vs.pdf), 2016.
