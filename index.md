# Algorithms and applications

This index covers the reusable algorithms in [the library](Library/README.md), the applications in [the demos](Demos/README.md), and the algorithms retained as compiler examples.  It lists their implementations, proved results, and open mathematical work.  Library families contain native definitions in `Program`, compilation modules in `Compiled`, `Module`, or `Verified`, and proofs in `Proof`, `Verify`, or named theorem modules.  [The native aggregate](Library/Native.lean) imports the implementations.  The [verified compiler manual](docs/verified-manual.md) and [LeanExe compiler manual](docs/leanexe-manual.md) describe their compilation and proof premises.

The compiler's theorem for a module states that the module computes its Lean definition.  A byte theorem states execution or a further property, such as an accuracy bound, for the encoded module.  A file theorem states that an emitted file holds that encoding.  Execution theorems use Talos's semantics of WebAssembly with the deterministic floating-point profile.  They assume the allocator invariant and, for some functions, borrowed tables and bounds on memory and recursion depth.  An `implements` theorem can permit a trap at `unreachable`.  A trap-free theorem proves a return under its allocation and depth conditions.  Each linked document states these premises, the exceptional inputs, and the assumptions about the host.  [The transcendental development record](transcendentals.md) gives the history of the proofs and the open range of the Bessel theorems of [Section 1.1](#11-bessel-functions).

## Contents

- [1. Elementary and special functions](#1-elementary-and-special-functions)
  - [1.1. Bessel functions](#11-bessel-functions)
- [2. Conversion between decimal strings and binary floating point](#2-conversion-between-decimal-strings-and-binary-floating-point)
- [3. Arithmetic](#3-arithmetic)
- [4. Discrete Fourier transform](#4-discrete-fourier-transform)
- [5. Pseudorandom number generators](#5-pseudorandom-number-generators)
- [6. Floating-point folds](#6-floating-point-folds)
  - [6.1. Word reductions](#61-word-reductions)
  - [6.2. Statistics](#62-statistics)
- [7. Sorting, arrays, lists, and trees](#7-sorting-arrays-lists-and-trees)
- [8. Linear algebra](#8-linear-algebra)
- [9. Outward rounding and limiters](#9-outward-rounding-and-limiters)
- [10. Applications](#10-applications)
- [11. Compiler examples](#11-compiler-examples)

## 1. Elementary and special functions

Arguments and results are binary64 values, and `jn` and `yn` of [Section 1.1](#11-bessel-functions) take an additional order word whose low 32 bits encode a signed integer.  A bound of `k` steps means that the result lies within `k` positions of the nearest-even rounding of the exact result on the ordered line of binary64 values, which puts both zeros at one position and the infinities at its ends.  The bounds cover finite inputs in the domains listed after the table, and each function's document states its theorems for exceptional inputs.

| Functions | Document | Origin | Bound | Byte theorems |
|---|---|---|---|---|
| `exp` | [The exponential](Library/Numerics/Float64/Exp/README.md) | Arm optimized-routines | 1 step | [`ExpTheorem.exp_bytes_accuracy`](Library/Numerics/Float64/Exp/ExpTheorem.lean) |
| `exp2`, `exp10` | [Exponentials in bases 2 and 10](Library/Numerics/Float64/Exp2/README.md) | Arm optimized-routines | 1 step | [`Exp2Bytes.exp2_bytes_accuracy`](Library/Numerics/Float64/Exp2/Exp2Bytes.lean), `exp10_bytes_accuracy` |
| `expm1`, `tanh` | [`expm1` and `tanh`](Library/Numerics/Float64/Tanh/README.md) | fdlibm | 1 step, 3 steps | [`TanhBytes.expm1_bytes_accuracy`](Library/Numerics/Float64/Tanh/TanhBytes.lean), `tanh_bytes_accuracy` |
| `sinh`, `cosh` | [`sinh` and `cosh`](Library/Numerics/Float64/Sinh/README.md) | fdlibm | 3 steps, 1 step | [`SinhBytes.sinh_bytes_accuracy`](Library/Numerics/Float64/Sinh/SinhBytes.lean), `cosh_bytes_accuracy` |
| `log` | [The logarithm](Library/Numerics/Float64/Log/README.md) | Arm optimized-routines | 1 step | [`LogTheorem.log_bytes_accuracy`](Library/Numerics/Float64/Log/LogTheorem.lean) |
| `log2` | [The base-2 logarithm](Library/Numerics/Float64/Log2/README.md) | Arm optimized-routines | 1 step | [`Log2Theorem.log2_bytes_accuracy`](Library/Numerics/Float64/Log2/Log2Theorem.lean) |
| `log10` | [The base-10 logarithm](Library/Numerics/Float64/Log10/README.md) | fdlibm | 1 step | [`Log10Theorem.log10_bytes_accuracy`](Library/Numerics/Float64/Log10/Log10Theorem.lean) |
| `log1p` | [`log1p`](Library/Numerics/Float64/Log1p/README.md) | fdlibm | 1 step | [`Log1pBytes.log1p_bytes_accuracy`](Library/Numerics/Float64/Log1p/Log1pBytes.lean) |
| `pow` | [The power function](Library/Numerics/Float64/Pow/README.md) | Arm optimized-routines | 1 step | [`PowBytes.pow_bytes_accuracy`](Library/Numerics/Float64/Pow/PowBytes.lean) |
| `sin`, `cos` | [Sine and cosine](Library/Numerics/Float64/Trig/README.md) | fdlibm | 1 step | [`TrigTheorem.sin_bytes_accuracy`](Library/Numerics/Float64/Trig/TrigTheorem.lean), `cos_bytes_accuracy` |
| `tan` | [The tangent](Library/Numerics/Float64/Tan/README.md) | fdlibm | 1 step | [`TanTheorem.tan_bytes_accuracy`](Library/Numerics/Float64/Tan/TanTheorem.lean) |
| `sinpi`, `cospi`, `tanpi` | [The pi-scaled functions](Library/Numerics/Float64/Sinpi/README.md) | FreeBSD msun | 1 step | [`SinpiTheorem.sinpi_bytes_accuracy`](Library/Numerics/Float64/Sinpi/SinpiTheorem.lean), `cospi_bytes_accuracy`, `tanpi_bytes_accuracy` |
| `atan`, `atan2` | [The arctangent](Library/Numerics/Float64/Atan/README.md) | fdlibm | 1 step, 2 steps | [`AtanBytes.atan_bytes_accuracy`](Library/Numerics/Float64/Atan/AtanBytes.lean), `atan2_bytes_accuracy` |
| `asin`, `acos` | [The arcsine and arccosine](Library/Numerics/Float64/Asin/README.md) | fdlibm | 1 step | [`AsinBytes.asin_bytes_accuracy`](Library/Numerics/Float64/Asin/AsinBytes.lean), `acos_bytes_accuracy` |
| `asinh`, `acosh`, `atanh` | [The inverse hyperbolic functions](Library/Numerics/Float64/Asinh/README.md) | fdlibm | 2 steps | [`AsinhBytes.asinh_bytes_accuracy`](Library/Numerics/Float64/Asinh/AsinhBytes.lean), `acosh_bytes_accuracy`, `atanh_bytes_accuracy` |
| `erf` | [The error function](Library/Numerics/Float64/Erf/README.md) | fdlibm | 1 step | [`ErfTheorem.erf_bytes_accuracy`](Library/Numerics/Float64/Erf/ErfTheorem.lean) |
| `erfc` | [The error function](Library/Numerics/Float64/Erf/README.md) | CORE-MATH | 1 step | [`ErfcBytes.erfc_bytes_accuracy`](Library/Numerics/Float64/Erfc/ErfcBytes.lean) |
| `tgamma` | [The gamma function](Library/Numerics/Float64/Tgamma/README.md) | CORE-MATH | 1 step | [`TgammaBytes.tgamma_bytes_accuracy`](Library/Numerics/Float64/Tgamma/TgammaBytes.lean) |
| `lgamma` | [The log-gamma function](Library/Numerics/Float64/Lgamma/README.md) | CORE-MATH | 1 step | [`LgammaBytes.lgamma_bytes_accuracy`](Library/Numerics/Float64/Lgamma/LgammaBytes.lean) |

The bounds for `log`, `log2`, and `log10` cover `x > 0`, and the bound for `log1p` covers `x > -1`.  The bounds for `asin` and `acos` cover `-1 ≤ x ≤ 1`, the bound for `acosh` covers `x ≥ 1`, and the bound for `atanh` covers `-1 < x < 1`.  The bound for `atan2 y x` covers `y ≠ 0`, and the bound for `pow x y` covers `x > 0`, `x < 0` with integer `y`, and `x = 0` with `y ≥ 0`.  The bound for `tanpi` excludes the half-integers, and the bounds for `tgamma` and `lgamma` exclude zero and the negative integers.  The other bounds cover every finite input.

[`Log2Power.log2_power`](Library/Numerics/Float64/Log2/Log2Power.lean) proves that `log2` is exact at every representable power of two other than 1, and `Log2Theorem.log2_one` proves `log2 1 = +0`.  [`Log10Theorem.log10_pow10`](Library/Numerics/Float64/Log10/Log10Theorem.lean) proves that `log10` is exact at `10^n` for `0 ≤ n ≤ 22`, and [`LgammaSign.lgammaR_sign`](Library/Numerics/Float64/Lgamma/LgammaSign.lean) proves that the sign `lgammaR` returns with `ln |Γ(x)|` is the sign of `Γ(x)`.  The implementations of `sin`, `cos`, and `tan` reduce large arguments by the method of Payne and Hanek in 64-bit word arithmetic, following Go's `math.trigReduce`.  [`TrigDistance.quadrant_distance`](Library/Numerics/Float64/Trig/TrigDistance.lean) bounds how close a binary64 value comes to a multiple of `π/2`.

### 1.1. Bessel functions

The implementations of [the Bessel functions](Library/Numerics/Float64/Bessel/README.md) come from fdlibm.  Let `u = 2^-53` and `M_n(x) = √(J_n(x)² + Y_n(x)²)`.  The modulus bounds measure absolute error in units of `u M_n`, which stays positive at the zeros of `J_n` and `Y_n`.

| Functions | Bound | Domain |
|---|---|---|
| `j0`, `j1` | `10 u M_0(\|x\|)`, `12 u M_1(\|x\|)` | Every finite `x` |
| `y0` | `11 u M_0(x)` | `x > 0` |
| `y1` | `12 u M_1(x)` for `x ≥ 2^-1022`, and 1 step for `x < 2^-54 (1 + 2^-20)` | `x > 0`, by the two bounds together |
| `jn` | `(23 + 12 \|n\|) u M_\|n\|(\|x\|)` | Every finite `x` outside the range below |
| `yn` | `(250 + 12 \|n\|) u M_\|n\|(x)` when the result is finite, with an overflow alternative | `x > 0` outside the range below |

Both integer-order theorems exclude `2 ≤ |x| < 2^302` with `|n| > |x|/2`.  That range remains open: a proof needs a bound on `M_k(x)` for every order `k` through the turning point `k = x`.  For `yn`, the theorem permits the infinity with the sign of `Y_n(x)` only when `|Y_n(x)| > 2^1023`, and `BesselYnTheorem.yn_overflow` states that the result is that infinity when `|Y_n(x)| ≥ 2^1025`.  Between those thresholds the result is either that infinity or a finite value within the bound.  [The Bessel byte theorems](Library/Numerics/Float64/Bessel/BesselBytes.lean) state these bounds for the module's bytes, and `BesselBytes.bessel_module_accuracy` combines them.  [The file theorems](Library/Numerics/Float64/Bessel/BesselFile.lean) state that `build/verified/bessel.wasm` holds the module's encoding.

## 2. Conversion between decimal strings and binary floating point

| Functions | Document | Method | Byte theorems |
|---|---|---|---|
| `parse64`, `parse32` | [Decimal to binary conversion](Library/Numerics/Decimal/ParseFloat/README.md) | Clinger's fast path for short inputs, otherwise one exact rounding by Cox's unrounded scaling ([Section 3](#3-arithmetic)) | [`ParseFloatBytes.parse64_bytes_accuracy`](Library/Numerics/Decimal/ParseFloat/ParseFloatBytes.lean), `parse32_bytes_accuracy` |
| `print64`, `print64Ecma`, `print32`, `print32Ecma` | [Binary to decimal conversion](Library/Numerics/Decimal/PrintFloat/README.md) | A search for the largest power of 10 that has a multiple in the input's rounding interval, with each comparison an exact quotient from Cox's unrounded scaling ([Section 3](#3-arithmetic)) | [`PrintFloatBytes.print64_bytes_accuracy`](Library/Numerics/Decimal/PrintFloat/PrintFloatBytes.lean), `print64Ecma_bytes_accuracy`, `print32_bytes_accuracy`, `print32Ecma_bytes_accuracy` |

For a string of fewer than `2^32` bytes, the parsers' theorems state that the result is the number that the string denotes, rounded to nearest with ties to even, when the string belongs to the chosen grammar, and a rejection otherwise.  The grammars are RFC 8259's number grammar and a superset in the manner of C's `strtod`.  The printers' theorems state that parsing the output recovers the input, with a NaN replaced by the canonical NaN, and that the output for a finite input follows RFC 8259's grammar.  For a finite nonzero input, the output has the fewest significant digits among the decimals that round to the input, the least distance from the input among those, and an even last digit at a tie.  `print64` and `print32` write a scientific layout, and `print64Ecma` and `print32Ecma` write the layout of ECMA-262's Number::toString.  [`ParseFloatFile.parse_file`](Library/Numerics/Decimal/ParseFloat/ParseFloatFile.lean) and [`PrintFloatFile.print_file`](Library/Numerics/Decimal/PrintFloat/PrintFloatFile.lean) state that the files in `build/verified/` hold the modules' encodings.

## 3. Arithmetic

| Algorithm | Implementation | Theorems |
|---|---|---|
| Fused multiply-add | [The software fused multiply-add](Library/Numerics/Arithmetic/Fma/README.md): [`Fma.fma`](Library/Numerics/Arithmetic/Fma/Program.lean), with 128-bit products and shifts in 64-bit words | [`FmaTheorem.fma_toBits`](Library/Numerics/Arithmetic/Fma/FmaTheorem.lean): the result equals IEEE 754's fusedMultiplyAdd with roundTiesToEven for all operands.  The modules of `erfc`, `tgamma`, and `lgamma` in [Section 1](#1-elementary-and-special-functions) include it. |
| Natural numbers of any size and Cox's unrounded scaling | [Natural numbers on limbs](Library/Numerics/Arithmetic/Uscale/README.md): `Uscale`, on 32-bit limbs in 64-bit words, with multiplication by a word, shifts, comparison, subtraction, division, and powers of 10 | A theorem for each routine states its result as a natural number.  The decimal parsers and printers of [Section 2](#2-conversion-between-decimal-strings-and-binary-floating-point) call these routines. |
| Greatest common divisor | [Euclid's remainder recursion](Library/Numerics/Arithmetic/Gcd/README.md) | [`gcd_eq`](Library/Numerics/Arithmetic/Gcd/Proof.lean) proves equality with `Nat.gcd`.  [`gcd_bytes`](Library/Numerics/Arithmetic/Gcd/Verify.lean) proves that the compiled bytes compute it. |
| Number of prime factors with multiplicity | [Factor counting](Library/Numerics/Arithmetic/PrimeFactors/README.md), trial division in increasing order | [`compute_eq`](Library/Numerics/Arithmetic/PrimeFactors/Proof.lean) proves equality with the length of Mathlib's `Nat.primeFactorsList`.  [`primeFactors_bytes`](Library/Numerics/Arithmetic/PrimeFactors/Verify.lean) states that result for the bytes. |
| Sieve of Eratosthenes | `sieve` in [the array-element examples](Verified/Examples/Elements.lean), which marks the multiples of each prime `p` from `p²` and returns the flags of the composite numbers below `n` | The compiler's theorem. |
| Power modulo `2^64` by squaring | `pow` in [the recursion examples](Verified/Examples/Recursion.lean) | The compiler's theorem. |
| Integer ceiling square root | [Bracket halving](Library/Numerics/Arithmetic/CeilSqrt/README.md), in 17 steps | [`Sqrt.ceilSqrt_correct`](Library/Numerics/Arithmetic/CeilSqrt/Proof.lean) proves the least integer whose square is at least the input, for `n ≤ 2^32`.  [The compiled module](Library/Numerics/Arithmetic/CeilSqrt/Compiled.lean) proves execution of the word definition. |

## 4. Discrete Fourier transform

[The Fourier implementation](Library/Numerics/Fourier/Program.lean) computes the discrete Fourier transform, its inverse, and the power spectrum of real samples by the `n²` products of the definition.  A complex signal is an array of binary64 values with the real and imaginary parts interleaved.  The factors `exp (-2 π i m / n)` come from [`Trig.cosWith`](Library/Numerics/Float64/Trig/Program.lean) and [`Trig.sinWith`](Library/Numerics/Float64/Trig/Program.lean), which also define the cosine and sine of [Section 1](#1-elementary-and-special-functions).  The compiler's theorem states that the module computes these definitions bit for bit, and no theorem bounds the error.  [The native accuracy test](tests/TestSupport/Numerics/FourierAccuracy.lean) compares the results on its test signals with a reference transform computed using exact integer sums and 300-bit approximations to the trigonometric factors, then rounded to binary64.  It reports the largest error relative to its test tolerance.

## 5. Pseudorandom number generators

Each generator keeps its state in a `UInt64`.  The linked guides state the parameters, valid states, and memory conditions.

| Generator | Method | Proved results | Byte theorems |
|---|---|---|---|
| [Linear congruential generator](Library/Random/Lcg/README.md) (LCG) | `a * x + c` modulo `2^64` | Period `2^64` from every state, with each word occurring once per period.  Jump-ahead equals repeated steps.  Exact top-bit counts, hyperplane bounds, and spectral-test values for tuples of two to six successive states. | [`lcg_advance`](Library/Random/Lcg/Verified.lean), [`lcg_jump`](Library/Random/Lcg/Verified.lean) |
| [Park–Miller](Library/Random/ParkMiller/README.md) | `16807 * x % (2^31 - 1)` | Period `2^31 - 2` from every state in `[1, 2^31 - 2]`, with each state in the range occurring once per period.  Every seed maps into that range. | [`parkMiller_advance`](Library/Random/ParkMiller/Verified.lean) |
| [Xorshift64](Library/Random/Xorshift/README.md) | Marsaglia's shifts `(13, 7, 17)` | Period `2^64 - 1` from every nonzero state, with each nonzero word occurring once per period.  Jump-ahead equals repeated steps.  Exact top-bit counts and a 36,920-byte bound on heap growth for jump-ahead. | [`xorshift_advance`](Library/Random/Xorshift/Verified.lean), [`xorshift_jump`](Library/Random/Xorshift/Verified.lean) |
| [SplitMix64](Library/Random/SplitMix64/README.md) | A fixed odd increment followed by xorshift and multiplication rounds, as in Vigna's reference C code | The compiled step computes the Lean definition's new state and output word and preserves the store. | [`prng_bytes`](Library/Random/SplitMix64/Verify.lean) |

SplitMix64's module also exports `unitFloat`, which maps a word `x` to the binary64 value `(x >>> 11) / 2^53` in `[0, 1)`.  The theorem `prng_bytes` covers both functions.  The reusable proofs `splitMix_pure` and `unitFloat_pure`, described in [the SplitMix64 guide](Library/Random/SplitMix64/README.md) and [the `splitmix64` entry of the LTG knowledge base](ltg/entries/splitmix64/README.md), let other modules compile and call them.

[The orbit lemmas](Library/Random/Orbit/README.md) provide the shared facts about iteration, minimal periods, unique visits, and top-bit counts used by the LCG, Park–Miller, and xorshift proofs.

## 6. Floating-point folds

The floating-point operations follow the stated order.  [The reduction compilation](Library/Numerics/Reductions/Float64/Compiled.lean) proves that its Wasm module computes the Lean definitions bit for bit, including their NaNs and signed zeros.  Summation-error bounds remain future work.

| Fold | Implementation | Order |
|---|---|---|
| Sum | `total` in [binary64 reductions](Library/Numerics/Reductions/Float64/Program.lean) | Left to right from zero |
| Pairwise sum | `sumRange` in [binary64 reductions](Library/Numerics/Reductions/Float64/Program.lean) | Recursive halves of `[lo, hi)` for an ordered word-indexed range.  Missing entries read as zero. |
| Sum of flagged elements | `select` in [binary64 reductions](Library/Numerics/Reductions/Float64/Program.lean) | Left to right over the numeric array.  Missing flags read as false. |
| Maximum | `largest` in [binary64 reductions](Library/Numerics/Reductions/Float64/Program.lean) | Lean's `max`, left to right from negative infinity |
| Sum of squares | [Sum of squares](Library/Numerics/Statistics/SumSquares/README.md) | Left to right from zero, with separate multiplication and addition.  [`sumSquares_bytes`](Library/Numerics/Statistics/SumSquares/Verify.lean) proves execution. |
| Mean | [Mean](Library/Numerics/Statistics/Mean/README.md) | The left-to-right sum divided by the length converted to binary64.  The empty array gives NaN.  [`mean_bytes`](Library/Numerics/Statistics/Mean/Verify.lean) proves execution. |

The [linear-algebra functions](#8-linear-algebra) also accumulate their dot products left to right.

### 6.1. Word reductions

[The word reductions](Library/Numerics/Reductions/README.md) fold `Array UInt64` from the left.  `sumArray` starts from zero, `productArray` from one, and `xorArray` from zero.  Addition and multiplication wrap modulo `2^64`.  [Their compiled module](Library/Numerics/Reductions/Word/Compiled.lean) supplies execution, allocation, and trap-free theorems under the verified compiler's premises.  The [array examples](Verified/Examples/Arrays.lean) retain a word dot product as a compiler fixture.

### 6.2. Statistics

The reusable statistical functions are mean and sum of squares.  Related computations remain in their callers: [the selection examples](Verified/Examples/Select.lean) contain a median of three words, [the array-update examples](Verified/Examples/Updates.lean) contain a histogram of residues modulo a requested bucket count, and [the GPT layer normalizations](Demos/Gpt/Program.lean) compute population variance in their floating-point evaluation order.  [The binary32 model](Demos/Gpt32/Program.lean) has its own layer normalization.  Their compilation proofs establish execution of those definitions.

[The statistics plan](devnotes.md#2026-10-22-statistics-work-and-the-generator-index) records variance and standard deviation, incremental and merged moments, generalized sample quantiles, weighted quantiles, covariance, correlation, and dispersion measures as future work.  Empty samples, exceptional values, probability and weight domains, and numerical-error bounds require specifications.

## 7. Sorting, arrays, lists, and trees

These algorithms use `UInt64` words, counts, and indices.  Word arithmetic wraps modulo `2^64`.  Each family has native definitions and a separate verified-compiler module.  The generated theorems prove execution, allocation bounds, and trap-free execution under their representation, ownership, memory, and recursion premises.

| Family | Functions and behavior | Proofs and limits |
|---|---|---|
| [Insertion sort](Library/Sorting/README.md) | `sortInsert` inserts each element at the count of smaller accumulated elements.  It takes quadratic time. | [The compiled module](Library/Sorting/Insertion/Compiled.lean) and [the allocation-bound example](Verified/Examples/Insert.lean).  Sortedness and permutation theorems remain future work. |
| [Array search](Library/Arrays/Search/Program.lean) | `count` counts equal words.  `firstAbove` returns the first index above a limit and a success flag.  `firstZero` searches a specified prefix and returns the prefix length when it finds no zero.  Reads past the array's end return zero. | [The compiled module](Library/Arrays/Search/Compiled.lean).  [`firstZero_cases`](Library/Arrays/Search/Proof.lean) proves that the result is the first zero in the requested prefix, or that the prefix has none. |
| [Array filtering](Library/Arrays/Filter/Program.lean) | `removeAll` removes matching words in order by repeated searches and shifts.  `below` gathers at most a specified count of words below a limit.  `clearUntil` zeros the prefix before the first matching word. | [The compiled module](Library/Arrays/Filter/Compiled.lean).  `removeAll` takes quadratic time. |
| [Array repetition](Library/Arrays/Repeat/Program.lean) | `repeated` concatenates a specified number of copies. | [The compiled module](Library/Arrays/Repeat/Compiled.lean). |
| [Even-word range](Library/Arrays/Range/Program.lean) | `evens n` builds `n` words, with element `i` equal to `2 * i`. | [The compiled module](Library/Arrays/Range/Compiled.lean). |
| [Word-array scaling](Library/Arrays/Word/Program.lean) | `scaled` multiplies each element by a scalar. | [The compiled module](Library/Arrays/Word/Compiled.lean). |
| [Word lists](Library/Lists/README.md) | `range` builds `0` through `n - 1`.  `listSum` folds from zero, `sum` adds to a supplied accumulator, `reverse` reverses onto a supplied list, and `increment` adds one to each element. | [The compiled module](Library/Lists/Word/Compiled.lean).  Sum and reversal use tail loops.  Increment uses guarded structural recursion. |
| [Word trees](Library/Trees/README.md) | `KeyTree` stores a word and two children at each node.  `size`, `sum`, `height`, `incr`, `setKey`, `insert`, `leftChild`, and `splitRoot` provide structural operations and insertion by binary-search-tree comparisons. | [The compiled module](Library/Trees/WordTree/Compiled.lean), with [the fixed-layout encoding](Library/Trees/WordTree/Encoding.lean).  Search-tree ordering and membership theorems remain future work. |

[The array guide](Library/Arrays/README.md) gives the common array conventions.  [The list-tail cases](Verified/Examples/ListTailCases.lean) and [tree examples](Examples/Trees/README.md) check ownership, copying, header reuse, allocation counts, and the guarded recursion limit.  [The library case registry](tests/verified/library-cases.txt) reuses compiler-fixture cases for the extracted modules, with [supplementary native cases](tests/TestSupport/LibraryCases.lean).  Hashing remains a future library category.

## 8. Linear algebra

[The linear-algebra library](Library/Numerics/LinearAlgebra/README.md) provides the vector and matrix operations used by both GPT demos.  Matrices use row-major flat arrays and `UInt64` dimensions.  Index and dimension arithmetic wraps modulo `2^64`, and missing entries read as zero.  Dot products accumulate left to right with separate multiplication and addition.

| Precision | Native functions | Shape and operation rules | Compilation |
|---|---|---|---|
| [Binary64](Library/Numerics/LinearAlgebra/Float64/Program.lean) | `dot`, `axpy`, `grid`, `matVec`, `matMul`, `matMulT`, `add` | `dot` uses the first array's length.  `axpy` writes `a * x + y` over the length of `y`.  `grid` returns `x0 + i * dx`.  `matVec` returns the requested row count.  `matMul` and `matMulT` return the word product of their output dimensions.  `add` uses the first array's length. | [Binary64 compiled module](Library/Numerics/LinearAlgebra/Float64/Compiled.lean) |
| [Binary32](Library/Numerics/LinearAlgebra/Binary32/Program.lean) | `scale32`, `axpyArray32`, `matVec32`, `add32`, `linear32` | `scale32` and `axpyArray32` use the length of `x`.  `matVec32` returns the requested row count.  `add32` uses the first array's length.  `linear32` computes a row-vector times a matrix, then adds the bias. | [Binary32 compiled module](Library/Numerics/LinearAlgebra/Binary32/Compiled.lean) |

The compilation theorems preserve this floating-point evaluation order.  Numerical-error bounds for these operations remain future work.

## 9. Outward rounding and limiters

| Family | Operations | Mathematical results and compilation |
|---|---|---|
| [Checked outward rounding](Library/Numerics/Bounds/README.md) | `outAdd`, `outSub`, `outMul`, `outDiv`, and `outSqrt` return a `Checked` endpoint.  Status zero accepts a finite endpoint, and status one rejects it.  `endpoint` moves the rounded result one adjacent value in the requested direction.  `absBits`, `finite`, `nextUpBits`, and `nextDownBits` provide the word operations. | [`outAdd_accepted` and the other accepted-operation theorems](Library/Numerics/Bounds/Proof.lean) prove real lower or upper bounds on accepted results.  Division checks a nonzero denominator, and square root checks a nonnegative input.  [The compiled module](Library/Numerics/Bounds/Compiled.lean) proves execution with [the flat status-and-value encoding](Library/Numerics/Bounds/Encoding.lean). |
| [Minmod](Library/Numerics/Limiters/README.md) | `minmod` returns the input with smaller word magnitude when the sign bits agree, and zero when they differ. | [`real_minmod`](Library/Numerics/Limiters/Minmod/Proof.lean) relates the implementation through `CodeLib.IEEE64.value` to [real minmod](Library/Numerics/Limiters/Minmod/Real.lean).  The real theory proves symmetry, sign reversal, bounds, a Lipschitz bound, and constant- and linear-profile reconstruction properties.  [The compiled module](Library/Numerics/Limiters/Minmod/Compiled.lean) proves execution. |

The checked operations reject nonfinite inputs, results, or endpoints.  Interpreting `nextUpBits` and `nextDownBits` as adjacent real values requires their finite-input conditions.  [The Euler enclosure proofs](Demos/Euler/Enclosure.lean) use the checked operations, and [the reconstruction analysis](Demos/Euler/ReconstructionAccuracy.lean) uses minmod to bound the differences and faces computed from rounded inputs.

## 10. Applications

Application definitions and proofs live in `Demos`, with shared algorithms imported from `Library`.  The linked guides state the full domains, execution premises, and host assumptions.

| Application | Computation | Proved results |
|---|---|---|
| [Euler solvers](Demos/Euler/README.md) | First-order Rusanov and minmod-reconstructed finite-volume solvers for the two-dimensional Euler equations. | [Execution](Demos/Euler/Verify.lean) and [total execution within 1,407 pages](Demos/Euler/Total.lean) for the LeanExe module under its fresh-store and cap premises.  The solver proofs establish admissibility, hyperbolicity, conservation with rounding residuals, flux and update error bounds, and a reconstructed CFL bound.  [The verified compilation](Demos/Euler/Verified.lean) computes the same solvers under its generated bounds.  Convergence to a continuous solution remains open. |
| [Binary64 GPT-2](Demos/Gpt/README.md) | Full-sequence inference, cached generation, layer normalization, causal attention, an MLP, and top-k sampling using SplitMix64. | [The byte theorem](Demos/Gpt/Bytes.lean) covers the Lean model's operations.  [`forward_causal`](Demos/Gpt/Causal.lean) proves causality, [`steps_exact`](Demos/Gpt/Exact.lean) proves bit-for-bit equivalence of cached steps and full inference, and [the generation proof](Demos/Gpt/Generation.lean) composes the host's calls.  [The verified compilation](Demos/Gpt/Verified.lean) adds generated allocation and trap-free theorems under their bounds. |
| [Binary32 GPT-2](Demos/Gpt32/README.md) | Thirteen kernels for a cached generation step, compiled to Wasm and WGSL, with a modeled host program. | [The dispatch proofs](Demos/Gpt32/Proofs.lean) and [`generate_host`](Demos/Gpt32/Compose.lean) prove the native step's scores and race-free dispatch under strict binary32 device semantics and shape, buffer, and token bounds.  [The verified compilation](Demos/Gpt32/Verified.lean) proves Wasm execution and supplies the proved WGSL path.  [Its host theorem](Demos/Gpt32/VerifiedHost.lean) reuses the application proof. |
| [Drone planner](Demos/Drone/README.md) | Dynamic programming over station altitudes and speeds, minimizing duration and then excess altitude. | [The byte theorems](Demos/Drone/Verify.lean) prove optimality and safety in the ideal point-mass model for valid terrain.  [Total execution](Demos/Drone/Total.lean) uses at most 70 pages under its initial-allocator and cap premises.  [The verified compilation](Demos/Drone/Verified.lean) transports the safety and optimality results and proves trap-free execution under its bounds. |
| [Order book](Demos/Clob/README.md) | Level insertion and cancellation, market fills, depth, and command streams over word arrays. | [The byte theorem](Demos/Clob/Verify.lean) proves the fifteen functions' execution.  [The command-stream theorems](Demos/Clob/Commands.lean) prove chunk equivalence and equality of the books returned by `runOut` and `runCommands`.  [The verified version](Demos/Clob/Verified.lean) has its own typed definitions and command-stream proofs. |

The GPU theorems concern the modeled device and host commands.  The application guides describe the host processes, file I/O, engines, and GPU arithmetic conditions that execution tests check.

## 11. Compiler examples

These algorithms remain in `Examples` or `Verified/Examples` because they demonstrate language forms, ownership, or proof procedures.  Their compiler theorems state that the module computes the Lean definition under the linked compiler's premises.  Word arithmetic wraps modulo `2^64`.

| Program | Implementation | Computation |
|---|---|---|
| Fixed-table lookup | [The lookup example](Examples/Lookup/README.md) | The first match among ten key-value pairs, encoded after the query in 21 words.  A miss or another input length gives `[0, 0]`.  [`lookup_bytes`](Examples/Lookup/Verify.lean) proves equality with the independent specification. |
| Fixed-tree lookup | [The tree-lookup example](Examples/TreeLookup/README.md) | Three comparisons through a seven-node tree in a 15-word array.  A miss or another input length gives `[0, 0]`.  [`treeLookup_bytes`](Examples/TreeLookup/Verify.lean) proves equality with the specified traversal. |
| Bounded filtering | [The below-100 example](Examples/Below100/README.md) | The words below 100 in their original order for an input of at most eight words.  Longer inputs give an empty array.  [`below100_bytes`](Examples/Below100/Verify.lean) proves equality with the filtering specification. |
| Bounded increment | [The increment example](Examples/Increment/README.md) | One added to each word for an input of at most eight words.  Longer inputs give an empty array.  [`increment_bytes` and `increment_total`](Examples/Increment/Verify.lean) prove the specification and trap-free execution under the stated 16-page memory premises. |
| First-zero removal | [The removal example](Examples/RemoveZero/README.md) | Remove the first zero from at most eight words while preserving the other words' order.  An input without a zero is unchanged, and a longer input gives an empty array.  [`removeZero_bytes`](Examples/RemoveZero/Verify.lean) proves the independent specification. |
| Scalar multiply-add | [The binary64 arithmetic example](Examples/Axpy/README.md) | `a * x + y` with separate multiplication and addition |
| Scaled hypotenuse | `hypot` in [the binary64 examples](Verified/Examples/Floats.lean) | `sqrt (x * x + y * y) / s`.  The sum of squares can overflow even when the exact result is finite. |
| Newton's square root | `newtonSqrt` in [the bounded-repeat examples](Verified/Examples/Repeat.lean) | `x ↦ (x + a/x)/2` from `x = a` until `\|x² - a\| ≤ 10^-12 a`, for at most 64 steps |
| Scaling by a power of two | `scaleByPower` in [the binary64 examples](Verified/Examples/Floats.lean) | `x * 2^k` for `k` from 0 to 1023, with the power built from its exponent field |
| Mean of the indices | `mean` in [the binary64 examples](Verified/Examples/Floats.lean) | `(0 + 1 + ⋯ + (n - 1))/n` in binary64, NaN for `n = 0` |
| Harmonic number | `harmonic` in [the binary64 examples](Verified/Examples/Floats.lean) | `1/1 + 1/2 + ⋯ + 1/n` left to right.  The binary64 denominator stops increasing at `2^53`. |
| Falling body | `fall` in [the bounded-repeat examples](Verified/Examples/Repeat.lean) | Explicit Euler steps under gravity until the height reaches 0, for at most 100,000 steps |
| Histogram bucket | [The bucket example](Examples/Bucket/README.md) | `((x - lo) / width).toUInt64`, with Lean's saturating conversion (`bucket_bytes`) |
| Arithmetic in binary32 | [The binary32 example](Examples/Binary32/README.md) | Scalar `axpy32`, `hypot32`, and `ratio32`, plus imported library scaling and matrix-vector products.  Each has an execution theorem in the example, and `binary32_bytes` covers its module. |
| Verified WGSL kernels | [The kernel examples](Verified/Examples/Wgsl.lean) and [native-value dispatch proofs](Verified/Examples/WgslProof.lean) | Binary32 scaling and a conditional sum with a loop in one branch, Boolean arrays, a word scan, and square root after nearest-even rounding.  Wasm correctness and, under the device model, correct and race-free WGSL dispatch. |
| Triangle numbers, Fibonacci numbers, powers, sums of powers | `triangle`, `fib`, `power`, and `sumPowers` in [the counted-loop examples](Verified/Examples/Loops.lean) | Loops on words |
| Fibonacci pairs | `fibPair` in [the recursion examples](Verified/Examples/Recursion.lean) | Recursion on a pair of words |
| Collatz map | `collatz` in [the counted-loop examples](Verified/Examples/Loops.lean) and `collatzSteps` in [the bounded-repeat examples](Verified/Examples/Repeat.lean) | `n` iterations of the map from `x`, and the number of steps to reach 1, counted up to 1,000 |

[The LeanExe worked examples](docs/leanexe-manual.md#worked-examples) and [the verified compiler examples](docs/verified-manual.md#examples) also index the language and ownership examples: scalar tuples and sums, records, arrays, calls, module composition, lists, and recursive types.
