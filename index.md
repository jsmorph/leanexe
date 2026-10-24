# Algorithms, I/O, and applications

This index covers the reusable algorithms in [the library](Library/README.md), the [WASI stream API](docs/wasi.md), the applications in [the demos](Demos/README.md), and the algorithms retained as compiler examples.  Library families contain native definitions in `Program`, compilation modules in `Compiled`, `Module`, or `Verified`, and proofs in `Proof`, `Verify`, or named theorem modules.  [The native aggregate](Library/Native.lean) imports the algorithm implementations.  The [verified compiler manual](docs/verified-manual.md), [WASI manual](docs/wasi.md), and [LeanExe compiler manual](docs/leanexe-manual.md) describe compilation and proof premises.

The compiler's theorem for a module states that the module computes its Lean definition.  A byte theorem states execution or a further property, such as an accuracy bound, for the encoded module.  A file theorem states that an emitted file holds that encoding.  Execution theorems use Talos's semantics of WebAssembly with the deterministic floating-point profile.  They assume the allocator invariant and, for some functions, borrowed tables and bounds on memory and recursion depth.  An `implements` theorem can permit a trap at `unreachable`.  A trap-free theorem proves a return under its allocation and depth conditions.  Each linked guide states its domains, exceptional inputs, and host assumptions.  [The transcendental development record](transcendentals.md) gives the numerical proofs' history.

## Contents

- [1. Arithmetic](#1-arithmetic)
- [2. Arrays, lists, trees, and sorting](#2-arrays-lists-trees-and-sorting)
- [3. Pseudorandom number generators](#3-pseudorandom-number-generators)
- [4. Reductions](#4-reductions)
  - [4.1. Word reductions](#41-word-reductions)
  - [4.2. Binary64 reductions](#42-binary64-reductions)
- [5. Statistics](#5-statistics)
- [6. Elementary and special functions](#6-elementary-and-special-functions)
  - [6.1. Bessel functions](#61-bessel-functions)
- [7. Linear algebra](#7-linear-algebra)
- [8. Discrete Fourier transform](#8-discrete-fourier-transform)
- [9. Conversion between decimal strings and binary floating point](#9-conversion-between-decimal-strings-and-binary-floating-point)
- [10. Outward rounding and limiters](#10-outward-rounding-and-limiters)
- [11. WASI stream operations](#11-wasi-stream-operations)
- [12. Applications](#12-applications)
- [13. Compiler examples](#13-compiler-examples)

## 1. Arithmetic

[The limb representation](Library/Numerics/Arithmetic/Uscale/README.md) stores natural numbers in little-endian arrays of 32-bit limbs carried in `UInt64` words.  `val a` denotes the represented natural number, and `Limbs a` requires every element to be below `2^32`.  The limb theorems assume that property and their stated array-size, shift, and quotient bounds.  [The standalone compilation](Library/Numerics/Arithmetic/Uscale/Compiled.lean) proves execution of these definitions.  Decimal parsing and printing include the routines they call in their own modules.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `fma` | [Software fused multiply-add](Library/Numerics/Arithmetic/Fma/README.md) | Computes `a * b + c` with one nearest-even rounding, using 128-bit products and shifts implemented in 64-bit words. | [`FmaTheorem.fma_toBits`](Library/Numerics/Arithmetic/Fma/FmaTheorem.lean) proves equality with IEEE 754 fusedMultiplyAdd for all operands, including exceptional values.  The `erfc`, `tgamma`, and `lgamma` byte theorems include its calls. |
| `mulSmall` | [Limb multiplication with carry](Library/Numerics/Arithmetic/Uscale/Program.lean) | Returns limbs for `val a * m + c`, one limb longer than `a`. | [`mulSmall_spec`](Library/Numerics/Arithmetic/Uscale/UscaleBase.lean), for `m, c < 2^32` and `a.size < 2^64`. |
| `shl` | [Limb left shift](Library/Numerics/Arithmetic/Uscale/Program.lean) | Returns limbs for `val a * 2^k`. | [`shl_spec`](Library/Numerics/Arithmetic/Uscale/UscaleArith.lean), for `a.size < 2^32`. |
| `le` | [Limb comparison](Library/Numerics/Arithmetic/Uscale/Program.lean) | Compares `val a ≤ val b`. | [`le_spec`](Library/Numerics/Arithmetic/Uscale/UscaleArith.lean), for both array sizes below `2^32`. |
| `sub` | [Limb subtraction](Library/Numerics/Arithmetic/Uscale/Program.lean) | Returns `val a - val b` in an array of `a.size` limbs. | [`sub_spec`](Library/Numerics/Arithmetic/Uscale/UscaleArith.lean), for `val b ≤ val a`, `a.size < 2^32`, and `b.size < 2^64`. |
| `wordBits` | [Word bit length](Library/Numerics/Arithmetic/Uscale/Program.lean) | Counts the significant bits of a word, returning zero for zero. | [`wordBits_spec`](Library/Numerics/Arithmetic/Uscale/UscaleArith.lean) proves equality with `Nat.size`. |
| `bitLen` | [Limb bit length](Library/Numerics/Arithmetic/Uscale/Program.lean) | Counts the significant bits of `val a`. | [`bitLen_spec`](Library/Numerics/Arithmetic/Uscale/UscaleArith.lean) proves equality with `Nat.size`, for `a.size < 2^32`. |
| `divBits` | [Restoring limb division](Library/Numerics/Arithmetic/Uscale/Program.lean) | Returns a quotient word and remainder limbs for division of `val n` by `val d`. | [`divBits_spec`](Library/Numerics/Arithmetic/Uscale/UscaleDiv.lean), for positive `val d`, array sizes below `2^31`, `bits ≤ 63`, and `val n < val d * 2^bits`. |
| `scaledQuot` | [Cox's exact unrounded scaling](Library/Numerics/Arithmetic/Uscale/README.md) | Returns the floor of `val n * 2^sn / (val d * 2^sd)` and a flag for a nonzero remainder. | [`scaledQuot_spec`](Library/Numerics/Arithmetic/Uscale/UscaleDiv.lean), for positive `val d`, array sizes and shifts below `2^30`, `bits ≤ 63`, and a quotient below `2^bits`. |
| `mulPow10` | [Limb multiplication by a power of ten](Library/Numerics/Arithmetic/Uscale/Program.lean) | Returns limbs for `val a * 10^k`, multiplying in blocks of nine decimal digits. | [`mulPow10_spec`](Library/Numerics/Arithmetic/Uscale/UscaleDiv.lean), for `a.size < 2^31` and `k < 2^20`. |
| `pow10` | [A power of ten as limbs](Library/Numerics/Arithmetic/Uscale/Program.lean) | Returns limbs for `10^k`. | [`pow10_spec`](Library/Numerics/Arithmetic/Uscale/UscaleDiv.lean), for `k < 2^20`. |
| `gcd` | [Euclid's remainder recursion](Library/Numerics/Arithmetic/Gcd/README.md) | Computes the greatest common divisor of two words. | [`gcd_eq`](Library/Numerics/Arithmetic/Gcd/Proof.lean) proves equality with `Nat.gcd`.  [`gcd_bytes`](Library/Numerics/Arithmetic/Gcd/Verify.lean) states that result for the bytes. |
| Prime-factor count | [Trial division](Library/Numerics/Arithmetic/PrimeFactors/README.md) | Counts prime factors with multiplicity by trial division in increasing order. | [`compute_eq`](Library/Numerics/Arithmetic/PrimeFactors/Proof.lean) proves equality with the length of Mathlib's `Nat.primeFactorsList`.  [`primeFactors_bytes`](Library/Numerics/Arithmetic/PrimeFactors/Verify.lean) states that result for the bytes. |
| `sieve` | [The array-element example](Verified/Examples/Elements.lean) | Marks multiples of each prime `p` from `p²`, returning flags for composite numbers below `n`. | Generated compiler correctness.  The result uses the definition's word arithmetic. |
| `pow` | [The recursion example](Verified/Examples/Recursion.lean) | Computes `b^e` modulo `2^64` by repeated squaring. | Generated compiler correctness, with the example's guarded recursion premises. |
| `ceilSqrt` | [Bracket halving](Library/Numerics/Arithmetic/CeilSqrt/README.md) | Performs 17 bracket halvings to find an integer ceiling square root. | [`Sqrt.ceilSqrt_correct`](Library/Numerics/Arithmetic/CeilSqrt/Proof.lean) proves the least integer whose square is at least `n`, for `n ≤ 2^32`.  [The compilation](Library/Numerics/Arithmetic/CeilSqrt/Compiled.lean) proves execution of the word definition. |

## 2. Arrays, lists, trees, and sorting

These algorithms use `UInt64` words, counts, and indices, with arithmetic modulo `2^64`.  Each linked compilation supplies execution, allocation, and trap-free theorems under the verified compiler's representation, ownership, memory, and recursion premises.  [The array guide](Library/Arrays/README.md) states the common array conventions.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `count` | [Array search](Library/Arrays/Search/Program.lean) | Counts occurrences of a word. | [Generated execution proof](Library/Arrays/Search/Compiled.lean). |
| `firstAbove` | [Array search](Library/Arrays/Search/Program.lean) | Returns the first index whose element exceeds a limit and a Boolean success flag.  A miss returns `(0, false)`. | [Generated execution proof](Library/Arrays/Search/Compiled.lean). |
| `firstZero` | [Array search](Library/Arrays/Search/Program.lean) | Searches a specified prefix for zero.  Returns the prefix length on a miss.  Reads beyond the array return zero. | [`firstZero_cases`](Library/Arrays/Search/Proof.lean) proves the first-match property.  [Generated execution proof](Library/Arrays/Search/Compiled.lean). |
| `removeAll` | [Array filtering](Library/Arrays/Filter/Program.lean) | Removes matching words in order by repeated searches and shifts, taking quadratic time. | [Generated execution proof](Library/Arrays/Filter/Compiled.lean). |
| `below` | [Array filtering](Library/Arrays/Filter/Program.lean) | Collects, in order, at most a specified count of words below a limit. | [Generated execution proof](Library/Arrays/Filter/Compiled.lean). |
| `clearUntil` | [Array filtering](Library/Arrays/Filter/Program.lean) | Zeros the prefix before the first matching word, or the whole array when the word is absent. | [Generated execution proof](Library/Arrays/Filter/Compiled.lean). |
| `repeated` | [Array repetition](Library/Arrays/Repeat/Program.lean) | Concatenates a specified number of copies of an array. | [Generated execution proof](Library/Arrays/Repeat/Compiled.lean). |
| `evens` | [Even-word range](Library/Arrays/Range/Program.lean) | Builds `n` elements with element `i` equal to `2 * i`. | [Generated execution proof](Library/Arrays/Range/Compiled.lean). |
| `scaled` | [Word-array scaling](Library/Arrays/Word/Program.lean) | Multiplies each element by a word scalar. | [Generated execution proof](Library/Arrays/Word/Compiled.lean). |
| List `range` | [Word lists](Library/Lists/Word/Program.lean) | Builds the list `0` through `n - 1` in ascending order. | [Generated execution proof](Library/Lists/Word/Compiled.lean). |
| `listSum` | [Word lists](Library/Lists/Word/Program.lean) | Folds addition from zero over a word list. | [Generated execution proof](Library/Lists/Word/Compiled.lean). |
| List `sum` | [Word lists](Library/Lists/Word/Program.lean) | Adds each word to a supplied accumulator by tail recursion. | [Generated execution proof](Library/Lists/Word/Compiled.lean).  The compilation uses a tail loop. |
| `reverse` | [Word lists](Library/Lists/Word/Program.lean) | Reverses the input list onto a supplied accumulator list. | [Generated execution proof](Library/Lists/Word/Compiled.lean).  The compilation uses a tail loop. |
| List `increment` | [Word lists](Library/Lists/Word/Program.lean) | Adds one to every word. | [Generated execution proof](Library/Lists/Word/Compiled.lean), with guarded structural recursion. |
| `KeyTree.size` | [Word trees](Library/Trees/WordTree/Program.lean) | Counts the nodes modulo `2^64`. | [Generated execution proof](Library/Trees/WordTree/Compiled.lean), with guarded recursion. |
| `KeyTree.sum` | [Word trees](Library/Trees/WordTree/Program.lean) | Sums the keys modulo `2^64`. | [Generated execution proof](Library/Trees/WordTree/Compiled.lean), with guarded recursion. |
| `KeyTree.height` | [Word trees](Library/Trees/WordTree/Program.lean) | Returns zero at a leaf and one plus the maximum child height at a node, using word arithmetic. | [Generated execution proof](Library/Trees/WordTree/Compiled.lean), with guarded recursion. |
| `KeyTree.incr` | [Word trees](Library/Trees/WordTree/Program.lean) | Adds one to every key modulo `2^64`, preserving the tree's shape. | [Generated execution proof](Library/Trees/WordTree/Compiled.lean), with guarded recursion. |
| `KeyTree.setKey` | [Word trees](Library/Trees/WordTree/Program.lean) | Replaces the root key, leaving an empty tree empty. | [Generated execution proof](Library/Trees/WordTree/Compiled.lean). |
| `KeyTree.insert` | [Word trees](Library/Trees/WordTree/Program.lean) | Inserts left for a smaller key and right for a larger key.  Equality leaves the node unchanged. | [Generated execution proof](Library/Trees/WordTree/Compiled.lean), with guarded recursion.  Search-tree ordering and membership theorems remain future work. |
| `KeyTree.leftChild` | [Word trees](Library/Trees/WordTree/Program.lean) | Returns the root's left child, or an empty tree for an empty input. | [Generated execution proof](Library/Trees/WordTree/Compiled.lean). |
| `KeyTree.splitRoot` | [Word trees](Library/Trees/WordTree/Program.lean) | Returns the two children, or two empty trees for an empty input. | [Generated execution proof](Library/Trees/WordTree/Compiled.lean). |
| `sortInsert` | [Insertion sort](Library/Sorting/README.md) | Inserts each element at the count of smaller elements already accumulated.  The algorithm takes quadratic time. | [Generated execution proof](Library/Sorting/Insertion/Compiled.lean) and [the worked allocation-bound proof](Verified/Examples/Insert.lean).  Sortedness and permutation theorems remain future work. |

`KeyTree` has an empty constructor and nodes containing a word key and two children.  [Its encoding](Library/Trees/WordTree/Encoding.lean) uses null for empty and fixed-layout records for nodes.  [The list-tail cases](Verified/Examples/ListTailCases.lean) and [tree examples](Examples/Trees/README.md) check ownership, copying, header reuse, allocation counts, and the guarded recursion limit.  [The library case registry](tests/verified/library-cases.txt) reuses compiler-fixture cases for the extracted modules, with [supplementary native cases](tests/TestSupport/LibraryCases.lean).  Hashing remains a future library category.

## 3. Pseudorandom number generators

Each generator keeps its state in a `UInt64`.  The linked guides state the parameters, valid states, and memory conditions.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| Linear congruential generator | [LCG implementation and proofs](Library/Random/Lcg/README.md) | Applies `a * x + c` modulo `2^64`, with repeated-step and jump-ahead operations. | Period `2^64` from every state, with each word once per period.  Jump-ahead equals repeated steps.  Exact top-bit counts, hyperplane bounds, and spectral-test values for two to six successive states.  [`lcg_advance`](Library/Random/Lcg/Verified.lean) and [`lcg_jump`](Library/Random/Lcg/Verified.lean). |
| Park–Miller | [Park–Miller implementation and proofs](Library/Random/ParkMiller/README.md) | Applies `16807 * x % (2^31 - 1)`.  The seed operation maps every word to a valid state. | Period `2^31 - 2` from every state in `[1, 2^31 - 2]`, with each state once per period.  [`parkMiller_advance`](Library/Random/ParkMiller/Verified.lean). |
| Xorshift64 | [Xorshift implementation and proofs](Library/Random/Xorshift/README.md) | Applies Marsaglia's shifts `(13, 7, 17)`, with repeated-step and jump-ahead operations. | Period `2^64 - 1` from every nonzero state, with each nonzero word once per period.  Jump-ahead equals repeated steps.  Exact top-bit counts and a 36,920-byte heap-growth bound for jump-ahead.  [`xorshift_advance`](Library/Random/Xorshift/Verified.lean) and [`xorshift_jump`](Library/Random/Xorshift/Verified.lean). |
| SplitMix64 | [SplitMix64 implementation and proofs](Library/Random/SplitMix64/README.md) | Adds a fixed odd increment, then applies Vigna's xorshift and multiplication rounds to produce an output word. | [`prng_bytes`](Library/Random/SplitMix64/Verify.lean) proves the Lean definition's state and output word and preservation of the store. |
| `unitFloat` | [Word-to-binary64 conversion](Library/Random/SplitMix64/Program.lean) | Maps `x` to `(x >>> 11) / 2^53` in `[0, 1)`. | [`prng_bytes`](Library/Random/SplitMix64/Verify.lean) covers the conversion.  `unitFloat_pure` supplies a reusable store-preserving execution proof. |

The reusable `splitMix_pure` proof permits calls from other compiled modules, as [the SplitMix64 guide](Library/Random/SplitMix64/README.md) and [the LTG entry](ltg/entries/splitmix64/README.md) describe.  [The orbit lemmas](Library/Random/Orbit/README.md) supply shared results about iteration, minimal periods, unique visits, and top-bit counts.

## 4. Reductions

Each compilation proves execution of the stated fold under the compiler's representation and memory premises.

### 4.1. Word reductions

Word reductions use `UInt64` arithmetic modulo `2^64`.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `sumArray` | [Word reductions](Library/Numerics/Reductions/Word/Program.lean) | Folds addition left to right from zero. | [Generated execution proof](Library/Numerics/Reductions/Word/Compiled.lean). |
| `productArray` | [Word reductions](Library/Numerics/Reductions/Word/Program.lean) | Folds multiplication left to right from one. | [Generated execution proof](Library/Numerics/Reductions/Word/Compiled.lean). |
| `xorArray` | [Word reductions](Library/Numerics/Reductions/Word/Program.lean) | Folds exclusive or left to right from zero. | [Generated execution proof](Library/Numerics/Reductions/Word/Compiled.lean). |
| Word `dot` | [The array compiler example](Verified/Examples/Arrays.lean) | Sums products over the first array's length.  Missing entries of the second array read as zero. | Generated compiler correctness for the word definition. |

### 4.2. Binary64 reductions

Binary64 operations follow the stated order, including the definitions' NaNs and signed zeros.  Numerical-error bounds remain future work.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `total` | [Binary64 reductions](Library/Numerics/Reductions/Float64/Program.lean) | Sums left to right from zero. | [Generated execution proof](Library/Numerics/Reductions/Float64/Compiled.lean). |
| `sumRange` | [Binary64 reductions](Library/Numerics/Reductions/Float64/Program.lean) | Sums `[lo, hi)` by recursive halves for `lo ≤ hi`.  An empty range gives zero, and missing entries read as zero. | [Generated execution proof](Library/Numerics/Reductions/Float64/Compiled.lean), under the generated recursion and allocation conditions. |
| `select` | [Binary64 reductions](Library/Numerics/Reductions/Float64/Program.lean) | Sums flagged entries left to right over the numeric array.  Missing flags read as false. | [Generated execution proof](Library/Numerics/Reductions/Float64/Compiled.lean). |
| `largest` | [Binary64 reductions](Library/Numerics/Reductions/Float64/Program.lean) | Applies Lean's `max` left to right from negative infinity, which is also the empty-input result. | [Generated execution proof](Library/Numerics/Reductions/Float64/Compiled.lean). |

## 5. Statistics

Mean and sum of squares are reusable library functions.  The other entries remain compiler examples or application functions.  Their execution proofs preserve each definition's operation order.  Numerical-error bounds remain future work.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `sumSquares` | [Sum-of-squares implementation and proof](Library/Numerics/Statistics/SumSquares/README.md) | Accumulates squares left to right from zero, with separate multiplication and addition. | [`sumSquares_bytes`](Library/Numerics/Statistics/SumSquares/Verify.lean) proves bit-for-bit execution, including exceptional results. |
| `mean` | [Mean implementation and proof](Library/Numerics/Statistics/Mean/README.md) | Divides the left-to-right sum by the length converted to binary64.  An empty array gives NaN. | [`mean_bytes`](Library/Numerics/Statistics/Mean/Verify.lean) proves bit-for-bit execution. |
| `median` | [The selection compiler example](Verified/Examples/Select.lean) | Selects the middle of three words by comparisons. | Generated compiler correctness for the comparison definition. |
| `histogram` | [The array-update compiler example](Verified/Examples/Updates.lean) | Counts residues modulo the requested bucket count.  Counts wrap modulo `2^64`.  Zero buckets produce an empty array. | Generated compiler correctness for the array-update definition. |
| `layerNorm` | [Binary64 GPT normalization](Demos/Gpt/Program.lean) | Computes the mean and population variance from left-to-right sums, adds the supplied epsilon to the variance, then normalizes and applies gain and bias. | [The GPT byte theorem](Demos/Gpt/Bytes.lean) proves execution of the rounded calculation. |
| `layerNorm32` | [Binary32 GPT normalization](Demos/Gpt32/Program.lean) | Normalizes `d` values using the supplied binary32 divisor `nf`, epsilon `0.00001`, gain, and bias.  Each output recomputes the left-to-right mean and variance.  `nf = d` gives the intended population divisor. | [The verified compilation](Demos/Gpt32/Verified.lean) proves Wasm execution.  [The dispatch proofs](Demos/Gpt32/Proofs.lean) prove the modeled GPU result and race freedom. |

[The statistics plan](devnotes.md#2026-10-22-statistics-work-and-the-generator-index) records variance and standard deviation, incremental and merged moments, generalized sample quantiles, weighted quantiles, covariance, correlation, and dispersion measures as future work.  Empty samples, exceptional values, probability and weight domains, and numerical-error bounds require specifications.

## 6. Elementary and special functions

Arguments and results are binary64 values.  A bound of `k` steps means that the result lies within `k` positions of the nearest-even rounding of the exact result on the ordered line of binary64 values, which puts both zeros at one position and the infinities at its ends.  Each bound covers finite inputs in its stated domain, or every finite input when the row gives no restriction.  The linked guides state the exceptional-value results.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `exp` | [The exponential](Library/Numerics/Float64/Exp/README.md) | `e^x`, following Arm optimized-routines. | 1 step.  [`ExpTheorem.exp_bytes_accuracy`](Library/Numerics/Float64/Exp/ExpTheorem.lean). |
| `exp2` | [Base-2 exponentiation](Library/Numerics/Float64/Exp2/README.md) | `2^x`, following Arm optimized-routines. | 1 step.  [`Exp2Bytes.exp2_bytes_accuracy`](Library/Numerics/Float64/Exp2/Exp2Bytes.lean). |
| `exp10` | [Base-10 exponentiation](Library/Numerics/Float64/Exp2/README.md) | `10^x`, following Arm optimized-routines. | 1 step.  [`Exp2Bytes.exp10_bytes_accuracy`](Library/Numerics/Float64/Exp2/Exp2Bytes.lean). |
| `expm1` | [Exponential minus one](Library/Numerics/Float64/Tanh/README.md) | `e^x - 1`, following fdlibm. | 1 step.  [`TanhBytes.expm1_bytes_accuracy`](Library/Numerics/Float64/Tanh/TanhBytes.lean). |
| `log` | [The natural logarithm](Library/Numerics/Float64/Log/README.md) | `ln x`, following Arm optimized-routines. | 1 step for `x > 0`.  [`LogTheorem.log_bytes_accuracy`](Library/Numerics/Float64/Log/LogTheorem.lean). |
| `log2` | [The base-2 logarithm](Library/Numerics/Float64/Log2/README.md) | `log₂ x`, following Arm optimized-routines. | 1 step for `x > 0`.  Exact at representable powers of two by [`log2_power`](Library/Numerics/Float64/Log2/Log2Power.lean) and [`log2_one`](Library/Numerics/Float64/Log2/Log2Theorem.lean).  [`Log2Theorem.log2_bytes_accuracy`](Library/Numerics/Float64/Log2/Log2Theorem.lean). |
| `log10` | [The base-10 logarithm](Library/Numerics/Float64/Log10/README.md) | `log₁₀ x`, following fdlibm. | 1 step for `x > 0`.  Exact at `10^n` for `0 ≤ n ≤ 22` by [`log10_pow10`](Library/Numerics/Float64/Log10/Log10Theorem.lean).  [`Log10Theorem.log10_bytes_accuracy`](Library/Numerics/Float64/Log10/Log10Theorem.lean). |
| `log1p` | [Logarithm of one plus the input](Library/Numerics/Float64/Log1p/README.md) | `ln (1 + x)`, following fdlibm. | 1 step for `x > -1`.  [`Log1pBytes.log1p_bytes_accuracy`](Library/Numerics/Float64/Log1p/Log1pBytes.lean). |
| `pow` | [The power function](Library/Numerics/Float64/Pow/README.md) | `x^y`, following Arm optimized-routines. | 1 step for `x > 0`, for `x < 0` with integer `y`, and for `x = 0` with `y ≥ 0`.  [`PowBytes.pow_bytes_accuracy`](Library/Numerics/Float64/Pow/PowBytes.lean). |
| `sin` | [Sine](Library/Numerics/Float64/Trig/README.md) | Sine of `x` in radians, following fdlibm. | 1 step.  [`TrigTheorem.sin_bytes_accuracy`](Library/Numerics/Float64/Trig/TrigTheorem.lean). |
| `cos` | [Cosine](Library/Numerics/Float64/Trig/README.md) | Cosine of `x` in radians, following fdlibm. | 1 step.  [`TrigTheorem.cos_bytes_accuracy`](Library/Numerics/Float64/Trig/TrigTheorem.lean). |
| `tan` | [Tangent](Library/Numerics/Float64/Tan/README.md) | Tangent of `x` in radians, following fdlibm. | 1 step.  [`TanTheorem.tan_bytes_accuracy`](Library/Numerics/Float64/Tan/TanTheorem.lean). |
| `atan` | [The arctangent](Library/Numerics/Float64/Atan/README.md) | Arctangent of `x`, following fdlibm. | 1 step.  [`AtanBytes.atan_bytes_accuracy`](Library/Numerics/Float64/Atan/AtanBytes.lean). |
| `atan2` | [The two-argument arctangent](Library/Numerics/Float64/Atan/README.md) | The angle of `(x, y)`, with quadrant selection, following fdlibm. | 2 steps for `y ≠ 0`.  [`AtanBytes.atan2_bytes_accuracy`](Library/Numerics/Float64/Atan/AtanBytes.lean). |
| `asin` | [The arcsine](Library/Numerics/Float64/Asin/README.md) | Arcsine of `x`, following fdlibm. | 1 step for `-1 ≤ x ≤ 1`.  [`AsinBytes.asin_bytes_accuracy`](Library/Numerics/Float64/Asin/AsinBytes.lean). |
| `acos` | [The arccosine](Library/Numerics/Float64/Asin/README.md) | Arccosine of `x`, following fdlibm. | 1 step for `-1 ≤ x ≤ 1`.  [`AsinBytes.acos_bytes_accuracy`](Library/Numerics/Float64/Asin/AsinBytes.lean). |
| `sinpi` | [Pi-scaled sine](Library/Numerics/Float64/Sinpi/README.md) | `sin (πx)`, following FreeBSD msun. | 1 step.  [`SinpiTheorem.sinpi_bytes_accuracy`](Library/Numerics/Float64/Sinpi/SinpiTheorem.lean). |
| `cospi` | [Pi-scaled cosine](Library/Numerics/Float64/Sinpi/README.md) | `cos (πx)`, following FreeBSD msun. | 1 step.  [`SinpiTheorem.cospi_bytes_accuracy`](Library/Numerics/Float64/Sinpi/SinpiTheorem.lean). |
| `tanpi` | [Pi-scaled tangent](Library/Numerics/Float64/Sinpi/README.md) | `tan (πx)`, following FreeBSD msun. | 1 step outside the half-integers.  [`SinpiTheorem.tanpi_bytes_accuracy`](Library/Numerics/Float64/Sinpi/SinpiTheorem.lean). |
| `sinh` | [Hyperbolic sine](Library/Numerics/Float64/Sinh/README.md) | Hyperbolic sine of `x`, following fdlibm. | 3 steps.  [`SinhBytes.sinh_bytes_accuracy`](Library/Numerics/Float64/Sinh/SinhBytes.lean). |
| `cosh` | [Hyperbolic cosine](Library/Numerics/Float64/Sinh/README.md) | Hyperbolic cosine of `x`, following fdlibm. | 1 step.  [`SinhBytes.cosh_bytes_accuracy`](Library/Numerics/Float64/Sinh/SinhBytes.lean). |
| `tanh` | [Hyperbolic tangent](Library/Numerics/Float64/Tanh/README.md) | Hyperbolic tangent of `x`, following fdlibm. | 3 steps.  [`TanhBytes.tanh_bytes_accuracy`](Library/Numerics/Float64/Tanh/TanhBytes.lean). |
| `asinh` | [The inverse hyperbolic sine](Library/Numerics/Float64/Asinh/README.md) | Inverse hyperbolic sine of `x`, following fdlibm. | 2 steps.  [`AsinhBytes.asinh_bytes_accuracy`](Library/Numerics/Float64/Asinh/AsinhBytes.lean). |
| `acosh` | [The inverse hyperbolic cosine](Library/Numerics/Float64/Asinh/README.md) | Inverse hyperbolic cosine of `x`, following fdlibm. | 2 steps for `x ≥ 1`.  [`AsinhBytes.acosh_bytes_accuracy`](Library/Numerics/Float64/Asinh/AsinhBytes.lean). |
| `atanh` | [The inverse hyperbolic tangent](Library/Numerics/Float64/Asinh/README.md) | Inverse hyperbolic tangent of `x`, following fdlibm. | 2 steps for `-1 < x < 1`.  [`AsinhBytes.atanh_bytes_accuracy`](Library/Numerics/Float64/Asinh/AsinhBytes.lean). |
| `erf` | [The error function](Library/Numerics/Float64/Erf/README.md) | `erf x`, following fdlibm. | 1 step.  [`ErfTheorem.erf_bytes_accuracy`](Library/Numerics/Float64/Erf/ErfTheorem.lean). |
| `erfc` | [The complementary error function](Library/Numerics/Float64/Erf/README.md) | `1 - erf x`, following CORE-MATH. | 1 step.  [`ErfcBytes.erfc_bytes_accuracy`](Library/Numerics/Float64/Erfc/ErfcBytes.lean). |
| `tgamma` | [The gamma function](Library/Numerics/Float64/Tgamma/README.md) | `Γ(x)`, following CORE-MATH. | 1 step outside zero and the negative integers.  [`TgammaBytes.tgamma_bytes_accuracy`](Library/Numerics/Float64/Tgamma/TgammaBytes.lean). |
| `lgamma` | [The log-gamma function](Library/Numerics/Float64/Lgamma/README.md) | `ln \|Γ(x)\|`, following CORE-MATH. | 1 step outside zero and the negative integers.  [`LgammaBytes.lgamma_bytes_accuracy`](Library/Numerics/Float64/Lgamma/LgammaBytes.lean). |
| `lgammaR` | [Log-gamma with its sign](Library/Numerics/Float64/Lgamma/Program.lean) | `(lgamma x, signgam)`, with the sign represented by `±1.0`, following CORE-MATH. | [`lgammaR_sign`](Library/Numerics/Float64/Lgamma/LgammaSign.lean) proves the sign of `Γ(x)` for finite inputs outside zero and the negative integers.  [The compilation](Library/Numerics/Float64/Lgamma/Compiled.lean) proves execution of the pair-valued function. |

Sine, cosine, and tangent reduce large arguments by the method of Payne and Hanek in 64-bit word arithmetic, following Go's `math.trigReduce`.  [`TrigDistance.quadrant_distance`](Library/Numerics/Float64/Trig/TrigDistance.lean) bounds how close a binary64 value comes to a multiple of `π/2`.

### 6.1. Bessel functions

[The Bessel implementation](Library/Numerics/Float64/Bessel/README.md) follows fdlibm.  Let `u = 2^-53` and `M_n(x) = √(J_n(x)² + Y_n(x)²)`.  The modulus bounds measure absolute error in units of `u M_n`, which stays positive at the zeros of `J_n` and `Y_n`.  The order argument of `jn` and `yn` is a word whose low 32 bits encode a signed integer.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `j0` | [Order-zero Bessel function](Library/Numerics/Float64/Bessel/README.md) | `J₀(x)`. | `10 u M_0(\|x\|)` for every finite `x`.  [`BesselBytes.j0_bytes_accuracy`](Library/Numerics/Float64/Bessel/BesselBytes.lean). |
| `j1` | [Order-one Bessel function](Library/Numerics/Float64/Bessel/README.md) | `J₁(x)`. | `12 u M_1(\|x\|)` for every finite `x`.  [`BesselBytes.j1_bytes_accuracy`](Library/Numerics/Float64/Bessel/BesselBytes.lean). |
| `y0` | [Order-zero Bessel function of the second kind](Library/Numerics/Float64/Bessel/README.md) | `Y₀(x)`. | `11 u M_0(x)` for finite `x > 0`.  [`BesselBytes.y0_bytes_accuracy`](Library/Numerics/Float64/Bessel/BesselBytes.lean). |
| `y1` | [Order-one Bessel function of the second kind](Library/Numerics/Float64/Bessel/README.md) | `Y₁(x)`. | `12 u M_1(x)` for `x ≥ 2^-1022`, and 1 step for `0 < x < 2^-54 (1 + 2^-20)`.  Together these cover finite `x > 0`.  [`BesselBytes.y1_bytes_accuracy`](Library/Numerics/Float64/Bessel/BesselBytes.lean). |
| `jn` | [Integer-order Bessel function](Library/Numerics/Float64/Bessel/README.md) | `J_n(x)`. | `(23 + 12 \|n\|) u M_\|n\|(\|x\|)` for every finite `x` outside the open range below.  [`BesselBytes.jn_bytes_accuracy`](Library/Numerics/Float64/Bessel/BesselBytes.lean). |
| `yn` | [Integer-order Bessel function of the second kind](Library/Numerics/Float64/Bessel/README.md) | `Y_n(x)`. | `(250 + 12 \|n\|) u M_\|n\|(x)` for finite results, with the overflow alternative below, for finite `x > 0` outside the open range.  [`BesselBytes.yn_bytes_accuracy`](Library/Numerics/Float64/Bessel/BesselBytes.lean). |

Both integer-order theorems exclude `2 ≤ |x| < 2^302` with `|n| > |x|/2`.  That range remains open: a proof needs a bound on `M_k(x)` for every order `k` through the turning point `k = x`.  For `yn`, the theorem permits the infinity with the sign of `Y_n(x)` only when `|Y_n(x)| > 2^1023`, and [`BesselYnTheorem.yn_overflow`](Library/Numerics/Float64/Bessel/BesselYnTheorem.lean) states that the result is that infinity when `|Y_n(x)| ≥ 2^1025`.  Between those thresholds the result is either that infinity or a finite value within the bound.  [`BesselBytes.bessel_module_accuracy`](Library/Numerics/Float64/Bessel/BesselBytes.lean) combines the byte results.  [The file theorems](Library/Numerics/Float64/Bessel/BesselFile.lean) identify the encoding in `build/verified/bessel.wasm`.

## 7. Linear algebra

[The linear-algebra library](Library/Numerics/LinearAlgebra/README.md) supplies vector and matrix operations used by both GPT demos.  Matrices are row-major flat arrays.  Dimensions and indices use `UInt64` arithmetic modulo `2^64`, and missing entries read as zero.  Multiplication and addition round separately, and dot products accumulate left to right from zero.  The compilation theorems preserve that order under the generated memory and recursion conditions.  Numerical-error bounds remain future work.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `dot` (binary64) | [Binary64 dot product](Library/Numerics/LinearAlgebra/Float64/Program.lean) | Sums products over the first array's length. | [Generated execution proof](Library/Numerics/LinearAlgebra/Float64/Compiled.lean). |
| `axpy` (binary64) | [Binary64 vector update](Library/Numerics/LinearAlgebra/Float64/Program.lean) | Updates `ys[i]` with `a * xs[i] + ys[i]` over `ys.size`. | [Generated execution proof](Library/Numerics/LinearAlgebra/Float64/Compiled.lean). |
| `grid` (binary64) | [Binary64 grid construction](Library/Numerics/LinearAlgebra/Float64/Program.lean) | Builds `n` values `x0 + Float(i) * dx`. | [Generated execution proof](Library/Numerics/LinearAlgebra/Float64/Compiled.lean). |
| `matVec` (binary64) | [Binary64 matrix-vector product](Library/Numerics/LinearAlgebra/Float64/Program.lean) | Multiplies a `rows × cols` matrix by a vector, returning `rows` values. | [Generated execution proof](Library/Numerics/LinearAlgebra/Float64/Compiled.lean). |
| `matMul` (binary64) | [Binary64 matrix product](Library/Numerics/LinearAlgebra/Float64/Program.lean) | Multiplies an `n × k` matrix by a `k × m` matrix, returning `n * m` row-major values. | [Generated execution proof](Library/Numerics/LinearAlgebra/Float64/Compiled.lean). |
| `matMulT` (binary64) | [Binary64 product with a transposed matrix](Library/Numerics/LinearAlgebra/Float64/Program.lean) | Multiplies an `n × k` matrix by the transpose of an `m × k` matrix, returning `n * m` row-major values. | [Generated execution proof](Library/Numerics/LinearAlgebra/Float64/Compiled.lean). |
| `add` (binary64) | [Binary64 vector addition](Library/Numerics/LinearAlgebra/Float64/Program.lean) | Adds elementwise over the first array's length. | [Generated execution proof](Library/Numerics/LinearAlgebra/Float64/Compiled.lean). |
| `scale32` | [Binary32 vector scaling](Library/Numerics/LinearAlgebra/Binary32/Program.lean) | Multiplies each element of `x` by `a`, returning `x.size` values. | [Generated execution proof](Library/Numerics/LinearAlgebra/Binary32/Compiled.lean). |
| `axpyArray32` | [Binary32 vector multiply-add](Library/Numerics/LinearAlgebra/Binary32/Program.lean) | Builds `a * x[i] + y[i]` over `x.size`. | [Generated execution proof](Library/Numerics/LinearAlgebra/Binary32/Compiled.lean). |
| `matVec32` | [Binary32 matrix-vector product](Library/Numerics/LinearAlgebra/Binary32/Program.lean) | Multiplies a `rows × cols` matrix by a vector, returning `rows` values. | [Generated execution proof](Library/Numerics/LinearAlgebra/Binary32/Compiled.lean). |
| `add32` | [Binary32 vector addition](Library/Numerics/LinearAlgebra/Binary32/Program.lean) | Adds elementwise over the first array's length. | [Generated execution proof](Library/Numerics/LinearAlgebra/Binary32/Compiled.lean). |
| `linear32` | [Binary32 biased linear transform](Library/Numerics/LinearAlgebra/Binary32/Program.lean) | Multiplies a row of `k` values by a `k × m` matrix, returning `m` values.  Each output adds `b[c]` after its column dot product. | [Generated execution proof](Library/Numerics/LinearAlgebra/Binary32/Compiled.lean). |

## 8. Discrete Fourier transform

A complex signal is a flat binary64 array with real and imaginary parts interleaved.  The direct transform takes quadratic time and ignores an odd final float.  Transform and spectrum error bounds remain open.  Its trigonometric factors use the sine and cosine implementations in [Section 6](#6-elementary-and-special-functions).

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `twiddle` | [Fourier implementation](Library/Numerics/Fourier/Program.lean) | Returns `(cos θ, sin θ)` for the rounded angle `θ = 2π * (m/n)`. | [Generated execution proof](Library/Numerics/Fourier/Compiled.lean). |
| `dft` | [Fourier implementation](Library/Numerics/Fourier/Program.lean) | Computes the direct discrete Fourier transform using `n²` complex products. | [Generated execution proof](Library/Numerics/Fourier/Compiled.lean). |
| `inverse` | [Fourier implementation](Library/Numerics/Fourier/Program.lean) | Computes the inverse-sign transform, then divides each component by `n`. | [Generated execution proof](Library/Numerics/Fourier/Compiled.lean). |
| `powerSpectrum` | [Fourier implementation](Library/Numerics/Fourier/Program.lean) | Transforms real samples and returns `\|X_k\|²` for `0 ≤ k ≤ n/2`.  An empty input returns an empty array. | [Generated execution proof](Library/Numerics/Fourier/Compiled.lean). |

[The native accuracy test](tests/TestSupport/Numerics/FourierAccuracy.lean) compares its test signals with a reference transform computed using exact integer sums and 300-bit approximations to the trigonometric factors, then rounded to binary64.  It reports the largest error relative to its test tolerance.

## 9. Conversion between decimal strings and binary floating point

The parsers take one byte per `UInt64` array element and select either RFC 8259's number grammar or the documented superset in the manner of C's `strtod`.  The proofs cover strings of fewer than `2^32` bytes.  Binary32 encodings occupy the low 32 bits of a word.  The printers return arrays of byte-valued words.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `parse64` | [Decimal-to-binary conversion](Library/Numerics/Decimal/ParseFloat/README.md) | Parses a binary64 value with Clinger's fast path for short decimal inputs, then exact rounding through Cox's unrounded scaling when the fast path does not apply. | [`ParseFloatBytes.parse64_bytes_accuracy`](Library/Numerics/Decimal/ParseFloat/ParseFloatBytes.lean): nearest-even rounding of the denoted number, or rejection outside the selected grammar. |
| `parse32` | [Decimal-to-binary conversion](Library/Numerics/Decimal/ParseFloat/README.md) | Parses a binary32 encoding through exact rounding with Cox's unrounded scaling. | [`ParseFloatBytes.parse32_bytes_accuracy`](Library/Numerics/Decimal/ParseFloat/ParseFloatBytes.lean): nearest-even rounding of the denoted number, or rejection outside the selected grammar. |
| `print64` | [Binary-to-decimal conversion](Library/Numerics/Decimal/PrintFloat/README.md) | Prints a binary64 encoding in scientific layout, using exact scaled-quotient comparisons to select decimal digits. | [`PrintFloatBytes.print64_bytes_accuracy`](Library/Numerics/Decimal/PrintFloat/PrintFloatBytes.lean): round trip, RFC 8259 grammar for finite values, and the shortest-decimal property below. |
| `print64Ecma` | [Binary-to-decimal conversion](Library/Numerics/Decimal/PrintFloat/README.md) | Prints a binary64 encoding with ECMA-262's Number::toString layout. | [`PrintFloatBytes.print64Ecma_bytes_accuracy`](Library/Numerics/Decimal/PrintFloat/PrintFloatBytes.lean): round trip, RFC 8259 grammar for finite values, and the shortest-decimal property below. |
| `print32` | [Binary-to-decimal conversion](Library/Numerics/Decimal/PrintFloat/README.md) | Prints a binary32 encoding in scientific layout, using exact scaled-quotient comparisons to select decimal digits. | [`PrintFloatBytes.print32_bytes_accuracy`](Library/Numerics/Decimal/PrintFloat/PrintFloatBytes.lean): round trip, RFC 8259 grammar for finite values, and the shortest-decimal property below. |
| `print32Ecma` | [Binary-to-decimal conversion](Library/Numerics/Decimal/PrintFloat/README.md) | Prints a binary32 encoding with ECMA-262's Number::toString layout. | [`PrintFloatBytes.print32Ecma_bytes_accuracy`](Library/Numerics/Decimal/PrintFloat/PrintFloatBytes.lean): round trip, RFC 8259 grammar for finite values, and the shortest-decimal property below. |

Parsing a printer's output recovers the input, with a NaN replaced by the canonical NaN.  For a finite nonzero input, the output has the fewest significant digits among decimals that round to the input, the least distance from the input among those, and an even last digit at a tie.  The search finds the largest power of ten with a multiple in the input's rounding interval, using [the exact limb arithmetic](#1-arithmetic).  [`ParseFloatFile.parse_file`](Library/Numerics/Decimal/ParseFloat/ParseFloatFile.lean) and [`PrintFloatFile.print_file`](Library/Numerics/Decimal/PrintFloat/PrintFloatFile.lean) identify the emitted module encodings.

## 10. Outward rounding and limiters

[The checked operations](Library/Numerics/Bounds/README.md) return `Checked`: status zero accepts a finite endpoint, and status one rejects it.  The direction flag selects a lower or upper bound.  [The flat encoding](Library/Numerics/Bounds/Encoding.lean) stores status and value.  The checked arithmetic operations test their inputs, the rounded result, and the endpoint before acceptance.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `absBits` | [Binary64 magnitude bits](Library/Numerics/Bounds/Program.lean) | Clears the sign bit of a word. | [Generated execution proof](Library/Numerics/Bounds/Compiled.lean). |
| `finite` | [Binary64 finiteness test](Library/Numerics/Bounds/Program.lean) | Tests whether the magnitude bits are below the infinity encoding. | [Generated execution proof](Library/Numerics/Bounds/Compiled.lean) and [the word-level correspondence proofs](Library/Numerics/Bounds/Proof.lean). |
| `nextUpBits` | [Adjacent binary64 word](Library/Numerics/Bounds/Program.lean) | For a finite input word, returns the encoding of the next larger binary64 value.  Either signed-zero encoding maps to the encoding of `2^-1074`. | [Generated execution proof](Library/Numerics/Bounds/Compiled.lean).  The adjacent-real interpretation requires finite input and output, as [the endpoint proof](Library/Numerics/Bounds/Proof.lean) states. |
| `nextDownBits` | [Adjacent binary64 word](Library/Numerics/Bounds/Program.lean) | For a finite input word, returns the encoding of the next smaller binary64 value.  Either signed-zero encoding maps to the encoding of `-2^-1074`. | [Generated execution proof](Library/Numerics/Bounds/Compiled.lean).  The adjacent-real interpretation requires finite input and output, as [the endpoint proof](Library/Numerics/Bounds/Proof.lean) states. |
| `endpoint` | [Checked adjacent endpoint](Library/Numerics/Bounds/Program.lean) | Moves a rounded binary64 result one adjacent value in the selected direction.  Rejects nonfinite results or endpoints. | [`endpoint_word`](Library/Numerics/Bounds/Proof.lean) identifies the word-level operation.  [Generated execution proof](Library/Numerics/Bounds/Compiled.lean). |
| `outAdd` | [Checked outward addition](Library/Numerics/Bounds/Program.lean) | Adds two finite inputs and returns an outward endpoint when the result and endpoint are finite. | [`outAdd_accepted`](Library/Numerics/Bounds/Proof.lean) proves a real lower or upper bound on the exact sum.  [Generated execution proof](Library/Numerics/Bounds/Compiled.lean). |
| `outSub` | [Checked outward subtraction](Library/Numerics/Bounds/Program.lean) | Subtracts two finite inputs and returns an outward endpoint when the result and endpoint are finite. | [`outSub_accepted`](Library/Numerics/Bounds/Proof.lean) proves a real lower or upper bound on the exact difference.  [Generated execution proof](Library/Numerics/Bounds/Compiled.lean). |
| `outMul` | [Checked outward multiplication](Library/Numerics/Bounds/Program.lean) | Multiplies two finite inputs and returns an outward endpoint when the result and endpoint are finite. | [`outMul_accepted`](Library/Numerics/Bounds/Proof.lean) proves a real lower or upper bound on the exact product.  [Generated execution proof](Library/Numerics/Bounds/Compiled.lean). |
| `outDiv` | [Checked outward division](Library/Numerics/Bounds/Program.lean) | Divides finite inputs, rejects a zero denominator, and returns an outward endpoint when the result and endpoint are finite. | [`outDiv_accepted`](Library/Numerics/Bounds/Proof.lean) proves a real lower or upper bound on the exact quotient.  [Generated execution proof](Library/Numerics/Bounds/Compiled.lean). |
| `outSqrt` | [Checked outward square root](Library/Numerics/Bounds/Program.lean) | Checks a finite nonnegative input and returns an outward endpoint when the result and endpoint are finite. | [`outSqrt_accepted`](Library/Numerics/Bounds/Proof.lean) proves a real lower or upper bound on the square root.  [Generated execution proof](Library/Numerics/Bounds/Compiled.lean). |
| `minmod` | [Minmod implementation and real theory](Library/Numerics/Limiters/README.md) | Returns the input with smaller word magnitude when sign bits agree, and zero when they differ. | [`real_minmod`](Library/Numerics/Limiters/Minmod/Proof.lean) relates the implementation through `CodeLib.IEEE64.value` to [real minmod](Library/Numerics/Limiters/Minmod/Real.lean).  The real theory proves symmetry, sign reversal, bounds, a Lipschitz bound, and constant- and linear-profile reconstruction properties.  [Generated execution proof](Library/Numerics/Limiters/Minmod/Compiled.lean). |

[The Euler enclosure proofs](Demos/Euler/Enclosure.lean) use the checked operations.  [The reconstruction analysis](Demos/Euler/ReconstructionAccuracy.lean) uses minmod to bound the differences and faces computed from rounded inputs.

## 11. WASI stream operations

`LeanExe.Wasi` provides native action descriptions and an interpreter.  `verified_compile_wasi` compiles accepted actions to core WebAssembly with three Preview 1 imports.  Its exported-entry proofs preserve the native result or terminal outcome, committed world, and joint ordered trace under the host, representation, ownership, and scratch premises.  Conditional total execution requires a typed resource-prefix bound and assumptions about reached host operations.  [The WASI manual](docs/wasi.md) gives the exact API and proof scope.  Implementation and acceptance testing remain in progress.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| `readSome` | [Stdin action](LeanExe/Wasi/Action.lean) | Requests at most a UInt64 capacity from stdin.  Every valid request, including zero capacity, makes one read after any required allocation succeeds.  Capacity at least `2^32` returns errno 61 without I/O.  Error returns empty bytes. | [Read-wrapper correctness](Verified/Wasi/ReadFunction.lean) proves exact successful bytes, owned results, cleanup after error or empty success, and preserved caller regions outside scratch.  Committed input effects on error remain in the trace and world. |
| `writeStdoutSome` | [Stdout action](LeanExe/Wasi/Action.lean) | Makes one stdout write.  Success returns the transferred count, possibly short or zero.  Error returns errno and count zero. | [Write-wrapper correctness](Verified/Wasi/Write.lean) proves the source transfer and preservation of borrowed bytes and caller regions outside scratch.  Count zero on error supplies no zero-progress guarantee. |
| `writeStderrSome` | [Stderr action](LeanExe/Wasi/Action.lean) | Makes one stderr write with the same short-transfer and errno rules. | [Write-wrapper correctness](Verified/Wasi/Write.lean) covers descriptor 2.  A shared event journal preserves order with stdout, including hosts where both refer to the same destination. |
| `exit` | [Terminal action](LeanExe/Wasi/Action.lean) | Requests exit with the low 32 bits of a UInt64 status.  No continuation executes. | [Exit correctness](Verified/Wasi/Exit.lean) distinguishes accepted exit with its recorded status from rejected exit as a host trap.  Both preserve prior I/O.  [The manual](docs/wasi.md#wasmtime-host) states Wasmtime 44's accepted status range. |
| `LeanExe.Wasi.loop` | [Bounded effectful loop](LeanExe/Wasi/Action.lean) | Carries state through at most a UInt64 count of effectful steps, with a pure early-stop test and UInt64 index.  Exit or trap terminates the action. | [Loop correctness](Verified/Wasi/CommandLoopSpec.lean) and [cost-aware loop correctness](Verified/Wasi/CostLoopSpec.lean) preserve state, ordered effects, ownership, and resource-prefix bounds. |
| `Action.runStdio` | [Native stream interpreter](LeanExe/Wasi/Interpreter.lean) | Runs actions against Lean's stdio.  Writes flush and report full count on success.  Exit returns an outcome to Lean.  Stream errors propagate as `IO.Error`. | [Native interpreter cases](tests/wasi/Interpreter.lean) test this adapter policy.  OS-stream behavior and adapter conformance to the formal host assumptions remain outside the compiler theorem. |

## 12. Applications

Application definitions and proofs live in `Demos`, with shared algorithms imported from `Library`.  The linked guides state the domains, execution premises, and host assumptions.  GPU theorems concern the modeled device and host commands.  Execution tests cover the host processes, file I/O, engines, and device arithmetic described in the guides.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| Euler solvers | [Euler application and proofs](Demos/Euler/README.md) | The finite-volume solvers use Rusanov fluxes for the two-dimensional Euler equations, with minmod reconstruction in the second solver. | [Execution](Demos/Euler/Verify.lean) and [total execution within 1,407 pages](Demos/Euler/Total.lean) for the LeanExe module under its fresh-store and cap premises.  The solver proofs establish admissibility, hyperbolicity, conservation with rounding residuals, flux and update error bounds, and a reconstructed CFL bound.  [The verified compilation](Demos/Euler/Verified.lean) computes the same solvers under its generated bounds.  Convergence to a continuous solution remains open. |
| Binary64 GPT-2 | [Binary64 model and proofs](Demos/Gpt/README.md) | Computes full-sequence inference and cached generation with layer normalization, causal attention, an MLP, and top-k sampling using SplitMix64. | [The byte theorem](Demos/Gpt/Bytes.lean) proves execution of the Lean model.  [`forward_causal`](Demos/Gpt/Causal.lean) proves causality, [`steps_exact`](Demos/Gpt/Exact.lean) proves bit-for-bit equivalence of cached steps and full inference, and [the generation proof](Demos/Gpt/Generation.lean) composes the host's calls.  [The verified compilation](Demos/Gpt/Verified.lean) adds generated allocation and trap-free theorems under their bounds. |
| Binary32 GPT-2 | [Binary32 model and proofs](Demos/Gpt32/README.md) | Runs thirteen kernels for a cached generation step, compiled to Wasm and WGSL, with a modeled host program. | [The dispatch proofs](Demos/Gpt32/Proofs.lean) and [`generate_host`](Demos/Gpt32/Compose.lean) prove the native step's scores and race-free dispatch under strict binary32 device semantics and shape, buffer, and token bounds.  [The verified compilation](Demos/Gpt32/Verified.lean) proves Wasm execution and supplies the proved WGSL path.  [Its host theorem](Demos/Gpt32/VerifiedHost.lean) reuses the application proof. |
| Drone planner | [Drone application and proofs](Demos/Drone/README.md) | Uses dynamic programming over station altitudes and speeds to minimize duration, then excess altitude. | [The byte theorems](Demos/Drone/Verify.lean) prove optimality and safety in the ideal point-mass model for valid terrain.  [Total execution](Demos/Drone/Total.lean) uses at most 70 pages under its initial-allocator and cap premises.  [The verified compilation](Demos/Drone/Verified.lean) transports the safety and optimality results and proves trap-free execution under its bounds. |
| Order book | [Order-book application and proofs](Demos/Clob/README.md) | Inserts and cancels levels, fills market orders, computes depth, and processes three-word commands over word arrays. | [The byte and command-stream theorems](Demos/Clob/Verify.lean) prove the fifteen functions' execution, equivalence when a chunk boundary falls between commands, and equality of the books returned by `runOut` and `runCommands`.  [The verified version](Demos/Clob/Verified.lean) has its own typed definitions and command-stream proofs, using [the shared command lemmas](Demos/Clob/Commands.lean). |

## 13. Compiler examples

These algorithms remain in `Examples` or `Verified/Examples` as demonstrations of language forms, ownership, and proof procedures.  Execution theorems relate compiled programs to their Lean definitions under the compiler's premises.  Word arithmetic wraps modulo `2^64`.  The WGSL dispatch results assume the device model's shape, buffer, and invocation bounds.

| Algorithm | Implementation | Behavior | Proved results and limits |
|---|---|---|---|
| Fixed-table lookup | [The lookup example](Examples/Lookup/README.md) | Returns the first matching value among ten key-value pairs encoded after a query in 21 words.  A miss or another input length gives `[0, 0]`. | [`lookup_bytes`](Examples/Lookup/Verify.lean) proves equality with the independent specification. |
| Fixed-tree lookup | [The tree-lookup example](Examples/TreeLookup/README.md) | Traverses a seven-node tree in a 15-word array through three levels.  A miss or another input length gives `[0, 0]`. | [`treeLookup_bytes`](Examples/TreeLookup/Verify.lean) proves equality with the specified traversal. |
| Bounded filtering | [The below-100 example](Examples/Below100/README.md) | Keeps words below 100 in their original order for an input of at most eight words.  Longer inputs give an empty array. | [`below100_bytes`](Examples/Below100/Verify.lean) proves equality with the filtering specification. |
| Bounded increment | [The increment example](Examples/Increment/README.md) | Adds one to each word for an input of at most eight words.  Longer inputs give an empty array. | [`increment_bytes`](Examples/Increment/Verify.lean) proves the specification.  [`increment_total`](Examples/Increment/Verify.lean) proves trap-free execution under the stated 16-page memory premises. |
| First-zero removal | [The removal example](Examples/RemoveZero/README.md) | Removes the first zero from at most eight words while preserving the other words' order.  An input without a zero is unchanged, and a longer input gives an empty array. | [`removeZero_bytes`](Examples/RemoveZero/Verify.lean) proves the independent specification. |
| Byte identity | [The packed-byte examples](Verified/Examples/Bytes.lean) | Moves the input buffer to the result. | `compiled.identity.implements` and `compiled.bytes` prove execution, owned results, and heap preservation. |
| Byte duplication | [The packed-byte examples](Verified/Examples/Bytes.lean) | Returns two independently owned copies of the byte value. | `compiled.duplicate.implements` and `compiled.bytes`, with disjoint result allocations. |
| Byte selection | [The packed-byte examples](Verified/Examples/Bytes.lean) | Returns the selected buffer and releases the other. | `compiled.choose.implements` and `compiled.bytes`. |
| Byte cleanup | [The packed-byte examples](Verified/Examples/Bytes.lean) | Returns 7 after consuming the input buffer and discarding an intermediate byte result. | `compiled.discard.implements` and `compiled.bytes`.  [Execution cases](tests/wasi/bytes.tsv) check allocated-empty cleanup. |
| Byte swapping | [The packed-byte examples](Verified/Examples/Bytes.lean) | Returns two input buffers in reverse order. | `compiled.swap.implements` and `compiled.bytes`, with owned results. |
| Empty bytes | [The packed-byte examples](Verified/Examples/Bytes.lean) | Returns a null root and length zero without allocating. | `compiled.emptyBuffer.implements` and `compiled.bytes`. |
| Byte length | [The packed-byte examples](Verified/Examples/Bytes.lean) | Returns the buffer's length as a UInt64. | `compiled.readSize.implements` and `compiled.ownedSize.implements` prove execution and cleanup of an owned input. |
| Byte indexing | [The packed-byte examples](Verified/Examples/Bytes.lean) | Returns the indexed byte as a UInt64, or zero past the end. | `compiled.readByte.implements`, `compiled.ownedByte.implements`, and `compiled.bytes`.  [Execution cases](tests/wasi/bytes.tsv) cover 255, empty input, and the maximum UInt64 index. |
| Byte construction | [The packed-byte examples](Verified/Examples/Bytes.lean) | Builds a packed buffer from the low eight bits of a UInt64 callback at each index. | `compiled.buildPattern.implements`, `compiled.copyByBuild.implements`, `compiled.nestedBuild.implements`, and `compiled.bytes`.  The [construction proof](Verified/BytesBuildCorrect.lean) covers zero count, checked narrowing, allocation, nested callbacks, and capture cleanup. |
| Byte literals | [The byte-literal examples](Verified/Examples/Literals.lean) | Copies a deduplicated static byte sequence into a fresh owned buffer at each evaluation.  Empty literals allocate nothing. | [Literal-copy correctness](Verified/Bytes/Literal.lean) and the examples' generated execution theorems cover nested pure helpers, callbacks, branches, loops, and guarded recursion under static-pool premises. |
| Scalar `axpy` | [The binary64 arithmetic example](Examples/Axpy/README.md) | Computes `a * x + y` with separate multiplication and addition. | [`axpy_bytes`](Examples/Axpy/Verify.lean) proves bit-for-bit execution. |
| `hypot` | [The binary64 compiler examples](Verified/Examples/Floats.lean) | Computes `sqrt (x * x + y * y) / s`. | Generated compiler correctness.  The sum of squares can overflow even when the exact result is finite. |
| `newtonSqrt` | [The bounded-repeat compiler examples](Verified/Examples/Repeat.lean) | Starts from `a` and applies `x ↦ (x + a/x)/2` while `10^-12 a < \|x² - a\|`, for at most 64 steps. | Generated compiler correctness.  A numerical-error bound remains future work. |
| `scaleByPower` | [The binary64 compiler examples](Verified/Examples/Floats.lean) | Multiplies by `2^k`, built from the binary64 exponent field, for `0 ≤ k ≤ 1023`. | Generated compiler correctness for the word-and-float definition. |
| Mean of indices | [The binary64 compiler examples](Verified/Examples/Floats.lean) | Computes `(0 + 1 + ⋯ + (n - 1))/n` in binary64, with NaN for `n = 0`. | Generated compiler correctness.  A numerical-error bound remains future work. |
| `harmonic` | [The binary64 compiler examples](Verified/Examples/Floats.lean) | Accumulates `1/1 + 1/2 + ⋯ + 1/n` left to right.  The binary64 denominator stops increasing at `2^53`. | Generated compiler correctness.  A numerical-error bound remains future work. |
| `fall` | [The bounded-repeat compiler examples](Verified/Examples/Repeat.lean) | Advances a falling body by explicit Euler steps under gravity while height is positive, for at most 100,000 steps. | Generated compiler correctness for the rounded update. |
| Histogram bucket | [The bucket example](Examples/Bucket/README.md) | Computes `((x - lo) / width).toUInt64` with Lean's saturating conversion. | [`bucket_bytes`](Examples/Bucket/Verify.lean) proves execution. |
| `axpy32` | [The binary32 arithmetic example](Examples/Binary32/Program.lean) | Computes `a * x + y` with separate binary32 multiplication and addition. | [`axpy32_implements`](Examples/Binary32/Verify.lean) and [`binary32_bytes`](Examples/Binary32/Verify.lean). |
| `hypot32` | [The binary32 arithmetic example](Examples/Binary32/Program.lean) | Computes `sqrt (x * x + y * y)` in binary32. | [`hypot32_implements`](Examples/Binary32/Verify.lean) and [`binary32_bytes`](Examples/Binary32/Verify.lean). |
| `ratio32` | [The binary32 arithmetic example](Examples/Binary32/Program.lean) | Computes `(a - b) / c` in binary32. | [`ratio32_implements`](Examples/Binary32/Verify.lean) and [`binary32_bytes`](Examples/Binary32/Verify.lean). |
| `piecewise32` | [The binary32 arithmetic example](Examples/Binary32/Program.lean) | Selects a binary32 expression from comparisons with `lo` and `hi`, using negation, absolute value, `min`, and `max`. | [`piecewise32_implements`](Examples/Binary32/Verify.lean) and [`binary32_bytes`](Examples/Binary32/Verify.lean). |
| `condMix32` | [The conditional binary32 kernel](Examples/Binary32/Program.lean) | For `x[i] < lo`, returns its group-of-four mirror when that index is below `n`, and `max lo x[i]` otherwise.  For remaining inputs, returns `hi` when `hi ≤ x[i]`, and `max lo x[i]` otherwise. | [`condMixKernel_dispatch`](Examples/Binary32/Wgsl.lean) proves the modeled GPU result and race freedom.  A WebAssembly execution theorem remains open. |
| WGSL `scale` | [The verified kernel examples](Verified/Examples/Wgsl.lean) | Multiplies each binary32 array element by a gain. | Generated Wasm correctness and [`scale_dispatch`](Verified/Examples/WgslProof.lean): the native result and race-free modeled dispatch. |
| WGSL `branchSum` | [The verified kernel examples](Verified/Examples/Wgsl.lean) | Builds `n` outputs.  Below `limit`, each output multiplies the input by the left-to-right sum of the first `limit` inputs.  Other outputs negate the input. | Generated Wasm correctness and [`branch_dispatch`](Verified/Examples/WgslProof.lean): the native result and race-free modeled dispatch. |
| WGSL `flags` | [The verified kernel examples](Verified/Examples/Wgsl.lean) | Builds `n` Boolean values, inverting each input when requested.  Missing values read as false. | Generated Wasm correctness and [the proved WGSL lowering](Verified/WGSL/Compile.lean). |
| WGSL `wordScan` | [The verified kernel examples](Verified/Examples/Wgsl.lean) | Starts output `i` from input `i`, then applies `acc ↦ 3 * acc + xs[j]` for `0 ≤ j < i % 4`. | Generated Wasm correctness and [the proved WGSL lowering](Verified/WGSL/Compile.lean). |
| WGSL `roundRoot` | [The verified kernel examples](Verified/Examples/Wgsl.lean) | Rounds each binary32 input to the nearest-even integer, then takes its square root. | Generated Wasm correctness and [the proved WGSL lowering](Verified/WGSL/Compile.lean). |
| `triangle` | [The counted-loop compiler examples](Verified/Examples/Loops.lean) | Sums the words `0` through `n - 1`. | Generated compiler correctness. |
| `fib` | [The counted-loop compiler examples](Verified/Examples/Loops.lean) | Advances a Fibonacci pair from `(0, 1)` for `n` iterations and returns its first word. | Generated compiler correctness. |
| `power` | [The counted-loop compiler examples](Verified/Examples/Loops.lean) | Multiplies an accumulator by `x` for `n` iterations, starting from one. | Generated compiler correctness. |
| `sumPowers` | [The counted-loop compiler examples](Verified/Examples/Loops.lean) | Sums `x^i` for `0 ≤ i < n`, using the counted-loop power function. | Generated compiler correctness. |
| `fibPair` | [The recursion compiler examples](Verified/Examples/Recursion.lean) | Advances a supplied Fibonacci pair by a specified number of steps. | Generated compiler correctness, with this example's guarded recursion. |
| `collatz` | [The counted-loop compiler examples](Verified/Examples/Loops.lean) | Applies the word Collatz map a specified number of times. | Generated compiler correctness. |
| `collatzSteps` | [The bounded-repeat compiler examples](Verified/Examples/Repeat.lean) | Counts word Collatz steps while the state exceeds one, stopping after at most 1,000 steps. | Generated compiler correctness. |

[The LeanExe worked examples](docs/leanexe-manual.md#worked-examples) and [the verified compiler examples](docs/verified-manual.md#examples) index further language and ownership examples: scalar tuples and sums, records, arrays, calls, module composition, lists, and recursive types.
