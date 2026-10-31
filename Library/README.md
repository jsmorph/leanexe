# Library

The library groups reusable implementations and their proofs by algorithm family.  Native
definitions use the dialect that the verified compiler accepts.  Separate modules compile those
definitions and state the properties of the resulting WebAssembly.

## Algorithms

| Area | Forms | Contents |
|---|---|---|
| [Random generators](../index.md#3-pseudorandom-number-generators) | V S F C | LCG, Park–Miller, xorshift64, SplitMix64, word-to-float conversion, and shared orbit lemmas. |
| [Sorting](Sorting/README.md) | V F C A | Insertion sort on arrays of `UInt64`. |
| [Arrays](Arrays/README.md) | V S F C | Counting, first-match search, ordered removal, bounded filtering, prefix clearing, repetition, and word scaling. |
| [Lists](Lists/README.md) | V F C | Word-list range, sum, reversal, and increment. |
| [Trees](Trees/README.md) | V F C | Binary tree of words, structural operations, and search-tree insertion. |
| [Arithmetic](../index.md#1-arithmetic) | V S F C | Software FMA, limb arithmetic, unrounded scaling, GCD, factor counting, and bounded integer square root. |
| [Binary64 functions](../index.md#6-elementary-and-special-functions) | V S F C | Elementary and special functions with their accuracy proofs. |
| [Decimal conversion](../index.md#9-conversion-between-decimal-strings-and-binary-floating-point) | V S F C | Parsing and shortest-decimal printing. |
| [Fourier transforms](Numerics/Fourier/README.md) | V F C | DFT, inverse transform, and power spectrum. |
| [Reductions](Numerics/Reductions/README.md) | V F C | Word and binary64 folds, including pairwise summation. |
| [Linear algebra](Numerics/LinearAlgebra/README.md) | V F C | Vector and matrix operations in binary64 and binary32. |
| [Statistics](../index.md#5-statistics) | V F C | Mean and sum of squares. |
| [Arithmetic bounds](Numerics/Bounds/README.md) | V S F C | Checked outward-rounded operations and their real bounds. |
| [Limiters](Numerics/Limiters/README.md) | V S F C | Minmod and its real slope and face properties. |
| [Packed bytes](Bytes/Packed.lean) | – | Byte strings held eight bytes to a word, as the libraries that take byte strings state their arguments. |
| [Little-endian values](Bytes/LittleEndian.lean) | – | Values of byte strings read least significant byte first, and of the bytes of a word, which the SipHash and XXH64 proofs use. |
| [Hashing](Hashing/README.md) | V S F C A B | SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224, and SHA-512/256, with the FIPS 180-4 transcription and equivalence proofs they use, HMAC-SHA-256 and HMAC-SHA-512 with a transcription of FIPS 198-1, SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, and SHAKE256 with a transcription of FIPS 202, CRC-32 and CRC-32C with a transcription of ITU-T V.42 and RFC 3720, SipHash-2-4 and SipHash-1-3 with a transcription of the SipHash paper, and XXH64 with a transcription of the xxHash specification. |
| [Regular expressions](Regex/README.md) | V S F C | Matcher for regular expressions over bytes given at run time, by the position automaton, with Glushkov's theorem and a specification on Mathlib's languages. |

The Forms column gives the union of the codes that [the algorithm index](../index.md) gives an area's entries outside parentheses, which are the forms of the library's own modules.  The index's key defines the codes, and its rows also name the forms that other programs contribute.  The index also states the mathematical results and domains of the families.  A dash marks an area of definitions that the libraries use and that no module compiles on its own.

## Modules and imports

Each family's `Program` module defines its native functions.  `Library.Native` imports every
`Program` module of the library.  `tools/source-layout` fails when a `Program` module is missing
from `Library.Native` or reaches a module of `Verified` through its imports.

`Compiled`, or `Verified` in the LCG, Park–Miller, and xorshift families, runs `verified_compile`
and holds the module with its generated execution, allocation, and trap-free theorems, and with its
native theorems when the module translates to C.  `File`, or a module whose name contains `File`,
states the file theorems of the module that `tests/verified/run.sh` writes to `build/verified/`.
`Proof` and the larger families' named theorem modules state mathematical properties.  `Library`
imports the implementations and the main proof targets.  [The examples](../Examples) and [the
application demos](../Demos/README.md) import library functions and compile them among their own
functions, with their own cases.  Execution tests and reference calculators use [test
support](../tests/TestSupport).

## Proof scope

The theorems that `verified_compile` generates state that the module computes its Lean definition
under the representation, ownership, memory, and recursion premises.  Mathematical theorems state
further properties: period, rounding error, or an equation with an independent specification.
The named statements determine each function's guarantees.

Insertion sort has the generated theorems of its module, and [the insertion
example](../Verified/Examples/Insert.lean) proves an allocation bound, `sortInsert_bound`, for its
own compilation of the function.  Sortedness and permutation theorems for insertion sort, and
ordering and membership theorems for search-tree insertion, remain future work.  The reduction and
linear-algebra implementations preserve their operation order, wrapping word arithmetic, default
reads from short arrays, and floating-point exceptional cases.

## Builds and tests

```sh
tools/source-layout
tools/check-doc-links.mjs
tools/leanrun --timeout 30m lake build Library.Native
tools/leanrun --timeout 30m lake build Library.Sorting.Insertion.Compiled
```

The static checks cover import boundaries, registry paths, and local documentation links.
`Library.Native` builds the native definitions.  [The full check](../docs/verified-manual.md#the-full-check)
gives the complete library build and its resource settings.  The [cold-cache procedure](../docs/verified-manual.md#memory-heavy-numerical-proofs)
stages the memory-heavy proofs before the parallel aggregate.  `tests/verified/run.sh` reads the
module registries, emits and validates the modules, compares their cases with native Lean, checks
the file theorems, and runs the accuracy checks.  The full check also runs the GPU tests.
