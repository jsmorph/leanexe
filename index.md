# Seminumerical algorithms

This index lists the arithmetic and numerical algorithms implemented in this repository, with the strongest result proved for each.  Every entry is compiled to WebAssembly.  Programs that test data structures, control flow, or memory management are left out, and so are the applications under `Examples/` (the Euler solver, GPT inference, and the WGSL kernels).  An implementation under `Verified/` is a Lean program that [the Verified compiler](Verified/README.md) translates to WebAssembly, and the compiler's theorem states that the module computes the Lean definition.  A byte theorem adds a numerical statement about the compiled module's bytes, and a file theorem states that the file in `build/verified/` holds those bytes.  An implementation under `Examples/` is compiled by the LeanExe compiler with a proof written for the example, and it appears here only where `Verified/` has no equivalent.  [The status of the transcendental functions](transcendentals.md) records the work in progress and the open items.

## Elementary and special functions

Every function takes and returns binary64.  A bound of `n` steps states that the result lies at most `n` doubles away from the exact value rounded to the nearest double, ties to even.  The document of each function states the theorem's domain, the exceptional values, and the remaining limits.

| Functions | Document | Origin | Bound | Byte theorem |
|---|---|---|---|---|
| `exp` | [The exponential](Verified/Examples/Exp.md) | Arm optimized-routines | 1 step | `ExpTheorem.exp_bytes_accuracy` |
| `exp2`, `exp10` | [Exponentials in bases 2 and 10](Verified/Examples/Exp2.md) | Arm optimized-routines | 1 step | `Exp2Bytes.exp2_bytes_accuracy`, `exp10_bytes_accuracy` |
| `expm1`, `tanh` | [`expm1` and `tanh`](Verified/Examples/Tanh.md) | fdlibm | 1 step, 3 steps | `TanhBytes.expm1_bytes_accuracy`, `tanh_bytes_accuracy` |
| `sinh`, `cosh` | [`sinh` and `cosh`](Verified/Examples/Sinh.md) | fdlibm | 3 steps, 1 step | `SinhBytes.sinh_bytes_accuracy`, `cosh_bytes_accuracy` |
| `log` | [The logarithm](Verified/Examples/Log.md) | Arm optimized-routines | 1 step | `LogTheorem.log_bytes_accuracy` |
| `log2` | [The base-2 logarithm](Verified/Examples/Log2.md) | Arm optimized-routines | 1 step | `Log2Theorem.log2_bytes_accuracy` |
| `log10` | [The base-10 logarithm](Verified/Examples/Log10.md) | fdlibm | 1 step | `Log10Theorem.log10_bytes_accuracy` |
| `log1p` | [`log1p`](Verified/Examples/Log1p.md) | fdlibm | 1 step | `Log1pBytes.log1p_bytes_accuracy` |
| `pow` | [The power function](Verified/Examples/Pow.md) | Arm optimized-routines | 1 step | `PowBytes.pow_bytes_accuracy` |
| `sin`, `cos` | [Sine and cosine](Verified/Examples/Trig.md) | fdlibm | 1 step | `TrigTheorem.sin_bytes_accuracy`, `cos_bytes_accuracy` |
| `tan` | [The tangent](Verified/Examples/Tan.md) | fdlibm | 1 step | `TanTheorem.tan_bytes_accuracy` |
| `sinpi`, `cospi`, `tanpi` | [The pi-scaled functions](Verified/Examples/Sinpi.md) | FreeBSD msun | 1 step | `SinpiTheorem.sinpi_bytes_accuracy`, `cospi_bytes_accuracy`, `tanpi_bytes_accuracy` |
| `atan`, `atan2` | [The arctangent](Verified/Examples/Atan.md) | fdlibm | 1 step, 2 steps | `AtanBytes.atan_bytes_accuracy`, `atan2_bytes_accuracy` |
| `asin`, `acos` | [The arcsine and arccosine](Verified/Examples/Asin.md) | fdlibm | 1 step | `AsinBytes.asin_bytes_accuracy`, `acos_bytes_accuracy` |
| `asinh`, `acosh`, `atanh` | [The inverse hyperbolic functions](Verified/Examples/Asinh.md) | fdlibm | 2 steps | `AsinhBytes.asinh_bytes_accuracy`, `acosh_bytes_accuracy`, `atanh_bytes_accuracy` |
| `erf` | [The error function](Verified/Examples/Erf.md) | fdlibm | 1 step | `ErfTheorem.erf_bytes_accuracy` |
| `erfc` | [The error function](Verified/Examples/Erf.md) | CORE-MATH | 1 step | `ErfcBytes.erfc_bytes_accuracy` |
| `tgamma` | [The gamma function](Verified/Examples/Tgamma.md) | CORE-MATH | 1 step | `TgammaBytes.tgamma_bytes_accuracy` |
| `lgamma` | [The log-gamma function](Verified/Examples/Lgamma.md) | CORE-MATH | 1 step | `LgammaBytes.lgamma_bytes_accuracy` |
| `j0`, `j1`, `y0`, `y1`, `jn`, `yn` | [The Bessel functions](Verified/Examples/Bessel.md) | fdlibm | `c · 2^-53 · √(J² + Y²)` | `BesselBytes.bessel_module_accuracy` |

The Bessel bound is relative to the modulus `√(J² + Y²)` of the order's functions, with `c` from 10 to 12 for orders 0 and 1 and `c = a + b |n|` for `jn` and `yn`.  The theorems of `jn` and `yn` exclude `2 ≤ |x| < 2^302` with `|n| > |x|/2`, where the proof needs a bound on the modulus through the turning point `k = x`.  The ports of `sin`, `cos`, and `tan` reduce large arguments by the method of Payne and Hanek in 64-bit word arithmetic, after Go's `math.trigReduce`, and `TrigDistance.quadrant_distance` bounds how close a double comes to a multiple of `π/2`.

## Conversion between decimal strings and binary floating point

| Functions | Document | Method | Theorems |
|---|---|---|---|
| `parse64`, `parse32` | [Decimal to binary conversion](Verified/Examples/ParseFloat.md) | Clinger's fast path for short inputs and otherwise one exact rounding by Cox's unrounded scaling, for strings of any length in RFC 8259's grammar or a `strtod`-like superset | `ParseFloatBytes.parse64_bytes_accuracy`, `parse32_bytes_accuracy`: the word of roundTiesToEven applied to the number the string denotes, or a rejection.  `ParseFloatFile.parse_file`. |
| `print64`, `print64Ecma`, `print32`, `print32Ecma` | [Binary to decimal conversion](Verified/Examples/PrintFloat.md) | The shortest decimal that rounds back to the word, nearest to the word's value among the shortest, with an even last digit at a tie, in a scientific or an ECMAScript layout | `PrintFloatBytes.print64_bytes_accuracy` and the three others: the string denotes a number that rounds back to the word, lies in RFC 8259's grammar when the word is finite, and holds the shortest digits when the word is finite and nonzero.  `PrintFloatFile.print_file`. |

## Arithmetic

| Algorithm | Implementation | Result |
|---|---|---|
| Fused multiply-add | [The software fused multiply-add](Verified/Examples/Fma.md): `Fma.fma`, with 128-bit products and shifts in 64-bit words | `FmaTheorem.fma_toBits`: equal to IEEE 754's fusedMultiplyAdd with roundTiesToEven for all operands.  The ports of `erfc`, `tgamma`, and `lgamma` compile it in their modules. |
| Natural numbers of any size and Cox's unrounded scaling | [Natural numbers on limbs](Verified/Examples/Uscale.md): `Uscale`, on 32-bit limbs in 64-bit words, with multiplication by a word, shifts, comparison, subtraction, division, and powers of 10 | One theorem per routine stating its result as a natural number.  The decimal parsers and printers call these routines. |
| Integer ceiling square root | `ceilSqrt` in [the drone planner](Examples/Drone/README.md), compiled unchanged by [`Verified/Examples/Drone.lean`](Verified/Examples/Drone.lean), by 17 halvings of a bracket | `Examples.Drone.ceilSqrt_correct`: the exact ceiling square root for arguments up to `2^32`. |
| Greatest common divisor | `gcd` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean), Euclid's remainder recursion | The compiler's theorem.  [The `Examples/Gcd` example](Examples/Gcd/README.md) compiles the same recursion and proves that its bytes compute `Nat.gcd` (`gcd_eq`, `gcd_bytes`). |
| Count of prime factors | [The `Examples/PrimeFactors` example](Examples/PrimeFactors/README.md), trial division in increasing order | `compute_eq` and `primeFactors_bytes`: the module's bytes compute the length of Mathlib's `Nat.primeFactorsList`. |
| Sieve of Eratosthenes | `sieve` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | The compiler's theorem. |
| Power modulo `2^64` by squaring | `pow` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean) | The compiler's theorem. |

## Discrete Fourier transform

[`Verified/Examples/Fourier.lean`](Verified/Examples/Fourier.lean) computes the discrete Fourier transform of interleaved complex floats by the `n²` products of the definition, its inverse, and the power spectrum of real samples, with the factors from `Trig.cosWith` and `Trig.sinWith`.  The compiler's theorem states that the module computes these definitions bit for bit.  `FourierAccuracy.lean` checks the results in native Lean against an exact transform, and no theorem bounds their error.

## Pseudorandom number generators

The verified compiler compiles the generators of [LCG](Examples/Lcg/README.md), [Park–Miller](Examples/ParkMiller/README.md), and [xorshift64](Examples/Xorshift/README.md).  Their byte theorems combine the compiler's result with the generators' period and orbit theorems.  LCG and xorshift64 also have compiled jump-ahead functions proved equal to repeated advancement and theorems counting their top-bit distributions over a period.  The LCG proofs give the hyperplane bounds and spectral test values for two to six successive states.  The linked documents state the parameters, domains, and memory conditions.

[The `Examples/Prng` example](Examples/Prng/README.md) implements SplitMix64, the generator of Steele, Lea, and Flood in the form of Vigna's reference C code, and `unitFloat`, which maps a word to the binary64 value `(x >>> 11) / 2^53` in `[0, 1)`.  `splitMix_implements`, `unitFloat_implements`, and `prng_bytes` state that the compiled module computes the Lean definitions.  [The LTG entry](ltg/entries/splitmix64/README.md) lets other modules compile and call both functions.

## Floating-point folds

Each fold runs over binary64 values in a fixed order and rounds after every operation, so its result depends on the order of the elements.  The theorem of each states that the compiled module computes the Lean definition bit for bit.  No theorem bounds a fold's error against the exact result.

| Fold | Implementation | Order |
|---|---|---|
| Sum | `total` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | Left to right |
| Pairwise sum | `sumRange` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean) | Recursive halves of the index range |
| Dot product | `dot` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | Left to right, with the second array read as 0 past its end |
| Maximum | `largest` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | Left to right, negative infinity for an empty array |
| Sum of the flagged elements | `select` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | Left to right |
| Harmonic number | `harmonic` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `1/1 + 1/2 + ⋯ + 1/n` in increasing order |
| Mean | [The `Examples/Mean` example](Examples/Mean/README.md) | The left-to-right sum divided by the length, NaN for an empty array (`mean_bytes`) |
| Sum of squares | [The `Examples/SumSquares` example](Examples/SumSquares/README.md) | Left to right (`sumSquares_bytes`) |
| Matrix-vector product in binary32 | `matVec32` in [the `Examples/Binary32` example](Examples/Binary32/README.md) | Each row's dot product left to right (`matVec32_implements`, `binary32_bytes`) |

## Demos

These programs exercise the compilers on numerical code.  The theorem of each states that the compiled module computes the Lean definition bit for bit: the Verified compiler's theorem for a program under `Verified/`, and the example's own proof for a program under `Examples/`.  The arithmetic on words wraps modulo `2^64`.

| Program | Implementation | Computation |
|---|---|---|
| Scaled hypotenuse | `hypot` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `sqrt (x * x + y * y) / s` by the textbook formula, which overflows for `|x|` above about `1.34e154` |
| Newton's square root | `newtonSqrt` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | `x ↦ (x + a/x)/2` from `a`, at most 64 steps, until `|x² - a| ≤ 10^-12 a` |
| `axpy` | `axpy` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | `a * x + y` for each element, written in place |
| Grid | `grid` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | The points `x0 + i * dx` |
| Scaling by a power of two | `scaleByPower` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `x * 2^k` for `k` from 0 to 1023, with the power built from its exponent field |
| Mean of the indices | `mean` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `(0 + 1 + ⋯ + (n - 1))/n` in binary64 |
| Falling body | `fall` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | Explicit Euler steps under gravity until the height reaches 0 |
| Triangle numbers, Fibonacci numbers, powers, sums of powers | `triangle`, `fib`, `power`, and `sumPowers` in [`Verified/Examples/Loops.lean`](Verified/Examples/Loops.lean) | Loops on words |
| Fibonacci pairs | `fibPair` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean) | Recursion on a pair of words |
| Word folds | `sum` and `dot` in [`Verified/Examples/Arrays.lean`](Verified/Examples/Arrays.lean), and the product and exclusive or in [the `Examples/SumArray` example](Examples/SumArray/README.md) | Left folds over arrays of words (`productArray_implements`, `xorArray_implements`) |
| binary32 arithmetic | `axpy32`, `hypot32`, `ratio32`, `scale32`, and `axpyArray32` in [the `Examples/Binary32` example](Examples/Binary32/README.md) | Scalar and elementwise operations on `Float32`, each with an `implements` theorem, and `binary32_bytes` |
| Histogram bucket | [The `Examples/Bucket` example](Examples/Bucket/README.md) | `((x - lo) / width).toUInt64`, with Lean's saturating conversion (`bucket_bytes`) |
| Collatz map | `collatz` in [`Verified/Examples/Loops.lean`](Verified/Examples/Loops.lean) and `collatzSteps` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | `n` iterations, and the number of steps to 1 up to 1,000 |
