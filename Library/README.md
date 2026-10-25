# Library

The library groups reusable implementations and their proofs by algorithm family.  Native
definitions use the accepted Lean dialect.  Separate modules compile those definitions and state
the properties of the resulting WebAssembly.

## Algorithms

| Area | Contents |
|---|---|
| [Random generators](Random) | LCG, Park–Miller, xorshift64, SplitMix64, word-to-float conversion, and shared orbit lemmas. |
| [Sorting](Sorting/README.md) | Insertion sort on arrays of `UInt64`. |
| [Arrays](Arrays/README.md) | Counting, first-match search, ordered removal, bounded filtering, prefix clearing, repetition, and word scaling. |
| [Lists](Lists/README.md) | Word-list range, sum, reversal, and increment. |
| [Trees](Trees/README.md) | A binary tree of words, structural operations, and search-tree insertion. |
| [Arithmetic](Numerics/Arithmetic) | Software FMA, limb arithmetic, unrounded scaling, GCD, factor counting, and bounded integer square root. |
| [Binary64 functions](Numerics/Float64) | Elementary and special functions with their accuracy proofs. |
| [Decimal conversion](Numerics/Decimal) | Parsing and shortest-decimal printing. |
| [Fourier transforms](Numerics/Fourier) | DFT, inverse transform, and power spectrum. |
| [Reductions](Numerics/Reductions/README.md) | Word and binary64 folds, including pairwise summation. |
| [Linear algebra](Numerics/LinearAlgebra/README.md) | Vector and matrix operations in binary64 and binary32. |
| [Statistics](Numerics/Statistics) | Mean and sum of squares. |
| [Arithmetic bounds](Numerics/Bounds/README.md) | Checked outward-rounded operations and their real bounds. |
| [Limiters](Numerics/Limiters/README.md) | Minmod and its real slope and face properties. |
| [Packed bytes](Bytes/Packed.lean) | Byte strings held eight bytes to a word, as the libraries that take byte strings state their arguments. |
| [Hashing](Hashing/README.md) | SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224, and SHA-512/256, with the FIPS 180-4 transcription and equivalence proofs they use, HMAC-SHA-256 and HMAC-SHA-512 with a transcription of FIPS 198-1, SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, and SHAKE256 with a transcription of FIPS 202, and CRC-32 and CRC-32C with a transcription of ITU-T V.42 and RFC 3720. |
| [Regular expressions](Regex/README.md) | A matcher for regular expressions over bytes given at run time, by the position automaton, with Glushkov's theorem and a specification on Mathlib's languages. |

The [algorithm index](../index.md) states the mathematical results and domains of the families.

## Modules and imports

Each family's `Program` module defines its native functions.  `Library.Native` imports the native
implementations together.  For example:

```lean
import Library.Sorting.Insertion.Program
import Library.Numerics.Arithmetic.CeilSqrt.Program
```

`Compiled` contains a verified-compiler module and its generated execution, allocation, and
trap-free theorems.  `Module` and `Verify` contain a LeanExe compilation and its program-specific
proofs in families that use that compiler.  `Proof` and the larger families' named theorem modules
state mathematical properties.  `Library` imports the implementations and the main proof targets.

The [compiler examples](../Examples) and [application demos](../Demos/README.md) import library
functions while retaining their own compilation arrangements and tests.  Execution tests and
reference calculators use [test support](../tests/TestSupport).

## Proof scope

The generated compiler theorems state that the module computes its Lean definition under the
representation, ownership, memory, and recursion premises.  Mathematical theorems state further
properties: period, rounding error, sortedness, or an equation with an independent specification.
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
tools/leanrun --memory-high 10G --timeout 12h lake build Verified Library
tests/verified/run.sh
```

The static checks cover import boundaries, registry paths, and local documentation links.
`Library.Native` builds the native definitions.  The full library build includes the numerical
proofs, whose lgamma root-range proofs use a 10 GiB memory high limit and a 12 GiB maximum.  The
test driver reads the checked module registries, emits and validates the modules, compares their
cases with native Lean, and checks numerical file theorems and accuracy tests.  [The full-check
procedure](../docs/leanexe-manual.md#the-full-check) covers both compilers and the GPU tests.
