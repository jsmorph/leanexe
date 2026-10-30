# Library

The library groups reusable implementations and their proofs by algorithm family.  Native
definitions use the accepted Lean dialect.  Separate modules compile those definitions and state
the properties of the resulting WebAssembly.

## Algorithms

| Area | Forms | Contents |
|---|---|---|
| [Random generators](Random) | L V S C | LCG, Park–Miller, xorshift64, SplitMix64, word-to-float conversion, and shared orbit lemmas. |
| [Sorting](Sorting/README.md) | V C A | Insertion sort on arrays of `UInt64`. |
| [Arrays](Arrays/README.md) | V S C | Counting, first-match search, ordered removal, bounded filtering, prefix clearing, repetition, and word scaling. |
| [Lists](Lists/README.md) | V C | Word-list range, sum, reversal, and increment. |
| [Trees](Trees/README.md) | V C | A binary tree of words, structural operations, and search-tree insertion. |
| [Arithmetic](Numerics/Arithmetic) | L V S C | Software FMA, limb arithmetic, unrounded scaling, GCD, factor counting, and bounded integer square root. |
| [Binary64 functions](Numerics/Float64) | V S F C | Elementary and special functions with their accuracy proofs. |
| [Decimal conversion](Numerics/Decimal) | V S F C | Parsing and shortest-decimal printing. |
| [Fourier transforms](Numerics/Fourier) | V C | DFT, inverse transform, and power spectrum. |
| [Reductions](Numerics/Reductions/README.md) | V C | Word and binary64 folds, including pairwise summation. |
| [Linear algebra](Numerics/LinearAlgebra/README.md) | V C | Vector and matrix operations in binary64 and binary32. |
| [Statistics](Numerics/Statistics) | L | Mean and sum of squares. |
| [Arithmetic bounds](Numerics/Bounds/README.md) | V S C | Checked outward-rounded operations and their real bounds. |
| [Limiters](Numerics/Limiters/README.md) | V S C | Minmod and its real slope and face properties. |
| [Packed bytes](Bytes/Packed.lean) | – | Byte strings held eight bytes to a word, as the libraries that take byte strings state their arguments. |
| [Little-endian values](Bytes/LittleEndian.lean) | – | The values of byte strings read least significant byte first, and of the bytes of a word, which the SipHash and XXH64 proofs use. |
| [Hashing](Hashing/README.md) | V S F C A B | SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224, and SHA-512/256, with the FIPS 180-4 transcription and equivalence proofs they use, HMAC-SHA-256 and HMAC-SHA-512 with a transcription of FIPS 198-1, SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, and SHAKE256 with a transcription of FIPS 202, CRC-32 and CRC-32C with a transcription of ITU-T V.42 and RFC 3720, SipHash-2-4 and SipHash-1-3 with a transcription of the SipHash paper, and XXH64 with a transcription of the xxHash specification. |
| [Regular expressions](Regex/README.md) | V S F C | A matcher for regular expressions over bytes given at run time, by the position automaton, with Glushkov's theorem and a specification on Mathlib's languages. |

The Forms column gives the union of the codes of an area's entries in [the algorithm index](../index.md), whose key defines the codes and whose rows give each entry's codes, including those that other modules contribute.  The index also states the mathematical results and domains of the families.  A dash marks an area of definitions that the libraries use and that no module compiles on its own.

## Modules and imports

Each family's `Program` module defines its native functions.  `Library.Native` imports the native
implementations together.  For example:

```lean
import Library.Sorting.Insertion.Program
import Library.Numerics.Arithmetic.CeilSqrt.Program
```

`Compiled`, or `Verified` in the LCG, Park–Miller, and xorshift families, contains a verified-compiler module and its generated execution, allocation, and
trap-free theorems, with its native theorems when the module translates to C.  `Module` and `Verify` contain a LeanExe compilation and its program-specific
proofs in families that use that compiler.  `Proof` and the larger families' named theorem modules
state mathematical properties.  `Library` imports the implementations and the main proof targets.

The [compiler examples](../Examples) and [application demos](../Demos/README.md) import library
functions while retaining their own compilation arrangements and tests.  Execution tests and
reference calculators use [test support](../tests/TestSupport).

## Proof scope

The generated compiler theorems state that the module computes its Lean definition under the
representation, ownership, memory, and recursion premises.  Mathematical theorems state further
properties: period, rounding error, or an equation with an independent specification.
The named statements determine each function's guarantees.

Insertion sort currently has compiler correctness and an allocation bound in its worked example.
Its sortedness and permutation theorems remain future work.  The word-tree implementation has
compilation proofs.  Search-tree ordering and membership theorems remain future work.  The
reduction and linear-algebra implementations preserve their operation order, wrapping word
arithmetic, default reads from short arrays, and floating-point exceptional cases.

## Builds and tests

```sh
tools/source-layout
tools/check-doc-links.mjs
tools/leanrun --timeout 30m lake build Library.Native
tools/leanrun --timeout 30m lake build Library.Sorting.Insertion.Compiled
```

The static checks cover import boundaries, registry paths, and local documentation links.
`Library.Native` builds the native definitions.  The [full-check procedure](../docs/leanexe-manual.md#the-full-check)
gives the complete library build and its resource settings.  Its [cold-cache procedure](../docs/leanexe-manual.md#memory-heavy-numerical-proofs)
stages the memory-heavy proofs before the parallel aggregate.  The verified test
driver reads the checked module registries, emits and validates the modules, compares their
cases with native Lean, and checks numerical file theorems and accuracy tests.  The full check
also covers the LeanExe compiler and GPU tests.
