# Seminumerical algorithms

This index lists the compiled arithmetic and numerical algorithms and their theorems.  The [verified compiler](docs/verified-manual.md) compiles the implementations in `Verified/Examples/` and the generators of [Section 5](#5-pseudorandom-number-generators) in `Examples/Lcg/`, `Examples/ParkMiller/`, and `Examples/Xorshift/`.  The other entries in `Examples/` use the [LeanExe compiler](docs/leanexe-manual.md) and a separate proof for each program.  Four applications have their own guides: [the Euler solvers](Examples/Euler/README.md), [GPT-2 in binary64](Examples/Gpt/README.md), [GPT-2 in binary32 and its WGSL kernels](Examples/Gpt32/README.md), and [the drone planner](Examples/Drone/README.md).

The compiler's theorem for a module states that the module computes its Lean definition.  A byte theorem combines that result with a theorem about the definition, such as an accuracy bound, to state the same property of the module's bytes.  A file theorem states that a file in `build/verified/` holds the module's encoding.  The theorems hold in Talos's semantics of WebAssembly with the deterministic floating-point profile, and they assume the allocator invariant and, for some functions, borrowed tables and bounds on memory and recursion depth.  Each linked document states these premises, the exceptional inputs, and the assumptions about the host.  [The transcendental development record](transcendentals.md) gives the history of the proofs and the open range of the Bessel theorems of [Section 1.1](#11-bessel-functions).

## Contents

- [1. Elementary and special functions](#1-elementary-and-special-functions)
  - [1.1. Bessel functions](#11-bessel-functions)
- [2. Conversion between decimal strings and binary floating point](#2-conversion-between-decimal-strings-and-binary-floating-point)
- [3. Arithmetic](#3-arithmetic)
- [4. Discrete Fourier transform](#4-discrete-fourier-transform)
- [5. Pseudorandom number generators](#5-pseudorandom-number-generators)
- [6. Floating-point folds](#6-floating-point-folds)
- [7. Demonstration programs](#7-demonstration-programs)

## 1. Elementary and special functions

Arguments and results are binary64 values, and `jn` and `yn` of [Section 1.1](#11-bessel-functions) take an additional order word whose low 32 bits encode a signed integer.  A bound of `k` steps means that the result lies within `k` positions of the nearest-even rounding of the exact result on the ordered line of binary64 values, which puts both zeros at one position and the infinities at its ends.  The bounds cover finite inputs in the domains listed after the table, and each function's document states its theorems for exceptional inputs.

| Functions | Document | Origin | Bound | Byte theorems |
|---|---|---|---|---|
| `exp` | [The exponential](Verified/Examples/Exp.md) | Arm optimized-routines | 1 step | [`ExpTheorem.exp_bytes_accuracy`](Verified/Examples/ExpTheorem.lean) |
| `exp2`, `exp10` | [Exponentials in bases 2 and 10](Verified/Examples/Exp2.md) | Arm optimized-routines | 1 step | [`Exp2Bytes.exp2_bytes_accuracy`](Verified/Examples/Exp2Bytes.lean), `exp10_bytes_accuracy` |
| `expm1`, `tanh` | [`expm1` and `tanh`](Verified/Examples/Tanh.md) | fdlibm | 1 step, 3 steps | [`TanhBytes.expm1_bytes_accuracy`](Verified/Examples/TanhBytes.lean), `tanh_bytes_accuracy` |
| `sinh`, `cosh` | [`sinh` and `cosh`](Verified/Examples/Sinh.md) | fdlibm | 3 steps, 1 step | [`SinhBytes.sinh_bytes_accuracy`](Verified/Examples/SinhBytes.lean), `cosh_bytes_accuracy` |
| `log` | [The logarithm](Verified/Examples/Log.md) | Arm optimized-routines | 1 step | [`LogTheorem.log_bytes_accuracy`](Verified/Examples/LogTheorem.lean) |
| `log2` | [The base-2 logarithm](Verified/Examples/Log2.md) | Arm optimized-routines | 1 step | [`Log2Theorem.log2_bytes_accuracy`](Verified/Examples/Log2Theorem.lean) |
| `log10` | [The base-10 logarithm](Verified/Examples/Log10.md) | fdlibm | 1 step | [`Log10Theorem.log10_bytes_accuracy`](Verified/Examples/Log10Theorem.lean) |
| `log1p` | [`log1p`](Verified/Examples/Log1p.md) | fdlibm | 1 step | [`Log1pBytes.log1p_bytes_accuracy`](Verified/Examples/Log1pBytes.lean) |
| `pow` | [The power function](Verified/Examples/Pow.md) | Arm optimized-routines | 1 step | [`PowBytes.pow_bytes_accuracy`](Verified/Examples/PowBytes.lean) |
| `sin`, `cos` | [Sine and cosine](Verified/Examples/Trig.md) | fdlibm | 1 step | [`TrigTheorem.sin_bytes_accuracy`](Verified/Examples/TrigTheorem.lean), `cos_bytes_accuracy` |
| `tan` | [The tangent](Verified/Examples/Tan.md) | fdlibm | 1 step | [`TanTheorem.tan_bytes_accuracy`](Verified/Examples/TanTheorem.lean) |
| `sinpi`, `cospi`, `tanpi` | [The pi-scaled functions](Verified/Examples/Sinpi.md) | FreeBSD msun | 1 step | [`SinpiTheorem.sinpi_bytes_accuracy`](Verified/Examples/SinpiTheorem.lean), `cospi_bytes_accuracy`, `tanpi_bytes_accuracy` |
| `atan`, `atan2` | [The arctangent](Verified/Examples/Atan.md) | fdlibm | 1 step, 2 steps | [`AtanBytes.atan_bytes_accuracy`](Verified/Examples/AtanBytes.lean), `atan2_bytes_accuracy` |
| `asin`, `acos` | [The arcsine and arccosine](Verified/Examples/Asin.md) | fdlibm | 1 step | [`AsinBytes.asin_bytes_accuracy`](Verified/Examples/AsinBytes.lean), `acos_bytes_accuracy` |
| `asinh`, `acosh`, `atanh` | [The inverse hyperbolic functions](Verified/Examples/Asinh.md) | fdlibm | 2 steps | [`AsinhBytes.asinh_bytes_accuracy`](Verified/Examples/AsinhBytes.lean), `acosh_bytes_accuracy`, `atanh_bytes_accuracy` |
| `erf` | [The error function](Verified/Examples/Erf.md) | fdlibm | 1 step | [`ErfTheorem.erf_bytes_accuracy`](Verified/Examples/ErfTheorem.lean) |
| `erfc` | [The error function](Verified/Examples/Erf.md) | CORE-MATH | 1 step | [`ErfcBytes.erfc_bytes_accuracy`](Verified/Examples/ErfcBytes.lean) |
| `tgamma` | [The gamma function](Verified/Examples/Tgamma.md) | CORE-MATH | 1 step | [`TgammaBytes.tgamma_bytes_accuracy`](Verified/Examples/TgammaBytes.lean) |
| `lgamma` | [The log-gamma function](Verified/Examples/Lgamma.md) | CORE-MATH | 1 step | [`LgammaBytes.lgamma_bytes_accuracy`](Verified/Examples/LgammaBytes.lean) |

The bounds for `log`, `log2`, and `log10` cover `x > 0`, and the bound for `log1p` covers `x > -1`.  The bounds for `asin` and `acos` cover `-1 ≤ x ≤ 1`, the bound for `acosh` covers `x ≥ 1`, and the bound for `atanh` covers `-1 < x < 1`.  The bound for `atan2 y x` covers `y ≠ 0`, and the bound for `pow x y` covers `x > 0`, `x < 0` with integer `y`, and `x = 0` with `y ≥ 0`.  The bound for `tanpi` excludes the half-integers, and the bounds for `tgamma` and `lgamma` exclude zero and the negative integers.  The other bounds cover every finite input.

[`Log2Power.log2_power`](Verified/Examples/Log2Power.lean) proves that `log2` is exact at every representable power of two other than 1, and `Log2Theorem.log2_one` proves `log2 1 = +0`.  [`Log10Theorem.log10_pow10`](Verified/Examples/Log10Theorem.lean) proves that `log10` is exact at `10^n` for `0 ≤ n ≤ 22`, and [`LgammaSign.lgammaR_sign`](Verified/Examples/LgammaSign.lean) proves that the sign `lgammaR` returns with `ln |Γ(x)|` is the sign of `Γ(x)`.  The implementations of `sin`, `cos`, and `tan` reduce large arguments by the method of Payne and Hanek in 64-bit word arithmetic, following Go's `math.trigReduce`.  [`TrigDistance.quadrant_distance`](Verified/Examples/TrigDistance.lean) bounds how close a binary64 value comes to a multiple of `π/2`.

### 1.1. Bessel functions

The implementations of [the Bessel functions](Verified/Examples/Bessel.md) come from fdlibm.  Let `u = 2^-53` and `M_n(x) = √(J_n(x)² + Y_n(x)²)`.  The modulus bounds measure absolute error in units of `u M_n`, which stays positive at the zeros of `J_n` and `Y_n`.

| Functions | Bound | Domain |
|---|---|---|
| `j0`, `j1` | `10 u M_0(\|x\|)`, `12 u M_1(\|x\|)` | Every finite `x` |
| `y0` | `11 u M_0(x)` | `x > 0` |
| `y1` | `12 u M_1(x)` for `x ≥ 2^-1022`, and 1 step for `x < 2^-54 (1 + 2^-20)` | `x > 0`, by the two bounds together |
| `jn` | `(23 + 12 \|n\|) u M_\|n\|(\|x\|)` | Every finite `x` outside the range below |
| `yn` | `(250 + 12 \|n\|) u M_\|n\|(x)` when the result is finite, with an overflow alternative | `x > 0` outside the range below |

Both integer-order theorems exclude `2 ≤ |x| < 2^302` with `|n| > |x|/2`.  That range remains open: a proof needs a bound on `M_k(x)` for every order `k` through the turning point `k = x`.  For `yn`, the theorem permits the infinity with the sign of `Y_n(x)` only when `|Y_n(x)| > 2^1023`, and `BesselYnTheorem.yn_overflow` states that the result is that infinity when `|Y_n(x)| ≥ 2^1025`.  Between those thresholds the result is either that infinity or a finite value within the bound.  [The Bessel byte theorems](Verified/Examples/BesselBytes.lean) state these bounds for the module's bytes, and `BesselBytes.bessel_module_accuracy` combines them.  [The file theorems](Verified/Examples/BesselFile.lean) state that `build/verified/bessel.wasm` holds the module's encoding.

## 2. Conversion between decimal strings and binary floating point

| Functions | Document | Method | Byte theorems |
|---|---|---|---|
| `parse64`, `parse32` | [Decimal to binary conversion](Verified/Examples/ParseFloat.md) | Clinger's fast path for short inputs, otherwise one exact rounding by Cox's unrounded scaling ([Section 3](#3-arithmetic)) | [`ParseFloatBytes.parse64_bytes_accuracy`](Verified/Examples/ParseFloatBytes.lean), `parse32_bytes_accuracy` |
| `print64`, `print64Ecma`, `print32`, `print32Ecma` | [Binary to decimal conversion](Verified/Examples/PrintFloat.md) | A search for the largest power of 10 that has a multiple in the input's rounding interval, with each comparison an exact quotient from Cox's unrounded scaling ([Section 3](#3-arithmetic)) | [`PrintFloatBytes.print64_bytes_accuracy`](Verified/Examples/PrintFloatBytes.lean), `print64Ecma_bytes_accuracy`, `print32_bytes_accuracy`, `print32Ecma_bytes_accuracy` |

For a string of fewer than `2^32` bytes, the parsers' theorems state that the result is the number that the string denotes, rounded to nearest with ties to even, when the string belongs to the chosen grammar, and a rejection otherwise.  The grammars are RFC 8259's number grammar and a superset in the manner of C's `strtod`.  The printers' theorems state that parsing the output recovers the input, with a NaN replaced by the canonical NaN, and that the output for a finite input follows RFC 8259's grammar.  For a finite nonzero input, the output has the fewest significant digits among the decimals that round to the input, the least distance from the input among those, and an even last digit at a tie.  `print64` and `print32` write a scientific layout, and `print64Ecma` and `print32Ecma` write the layout of ECMA-262's Number::toString.  [`ParseFloatFile.parse_file`](Verified/Examples/ParseFloatFile.lean) and [`PrintFloatFile.print_file`](Verified/Examples/PrintFloatFile.lean) state that the files in `build/verified/` hold the modules' encodings.

## 3. Arithmetic

| Algorithm | Implementation | Theorems |
|---|---|---|
| Fused multiply-add | [The software fused multiply-add](Verified/Examples/Fma.md): [`Fma.fma`](Verified/Examples/Fma.lean), with 128-bit products and shifts in 64-bit words | [`FmaTheorem.fma_toBits`](Verified/Examples/FmaTheorem.lean): the result equals IEEE 754's fusedMultiplyAdd with roundTiesToEven for all operands.  The modules of `erfc`, `tgamma`, and `lgamma` in [Section 1](#1-elementary-and-special-functions) include it. |
| Natural numbers of any size and Cox's unrounded scaling | [Natural numbers on limbs](Verified/Examples/Uscale.md): `Uscale`, on 32-bit limbs in 64-bit words, with multiplication by a word, shifts, comparison, subtraction, division, and powers of 10 | A theorem for each routine states its result as a natural number.  The decimal parsers and printers of [Section 2](#2-conversion-between-decimal-strings-and-binary-floating-point) call these routines. |
| Greatest common divisor | `gcd` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean), Euclid's remainder recursion | The compiler's theorem.  [The `Examples/Gcd` example](Examples/Gcd/README.md) compiles the same recursion, and `gcd_eq` and `gcd_bytes` prove that its bytes compute `Nat.gcd`. |
| Number of prime factors with multiplicity | [The `Examples/PrimeFactors` example](Examples/PrimeFactors/README.md), trial division in increasing order | `compute_eq` and `primeFactors_bytes`: the module's bytes compute the length of Mathlib's `Nat.primeFactorsList`. |
| Sieve of Eratosthenes | `sieve` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean), which marks the multiples of each prime `p` from `p²` and returns the flags of the composite numbers below `n` | The compiler's theorem. |
| Power modulo `2^64` by squaring | `pow` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean) | The compiler's theorem. |
| Integer ceiling square root | `ceilSqrt` in [the drone planner](Examples/Drone/README.md), by 17 halvings of a bracket.  [`Verified/Examples/Drone.lean`](Verified/Examples/Drone.lean) compiles it unchanged. | `Examples.Drone.ceilSqrt_correct`: the exact ceiling square root for arguments up to `2^32`. |

## 4. Discrete Fourier transform

[The Fourier implementation](Verified/Examples/Fourier.lean) computes the discrete Fourier transform, its inverse, and the power spectrum of real samples by the `n²` products of the definition.  A complex signal is an array of binary64 values with the real and imaginary parts interleaved.  The factors `exp (-2 π i m / n)` come from [`Trig.cosWith`](Verified/Examples/Trig.lean) and [`Trig.sinWith`](Verified/Examples/Trig.lean), which also define the cosine and sine of [Section 1](#1-elementary-and-special-functions).  The compiler's theorem states that the module computes these definitions bit for bit, and no theorem bounds the error.  [The native accuracy test](Verified/Examples/FourierAccuracy.lean) compares the results on its test signals with a reference transform computed using exact integer sums and 300-bit approximations to the trigonometric factors, then rounded to binary64.  It reports the largest error relative to its test tolerance.

## 5. Pseudorandom number generators

The byte theorems of [the linear congruential generator](Examples/Lcg/README.md) (LCG), [the Park–Miller generator](Examples/ParkMiller/README.md), and [xorshift64](Examples/Xorshift/README.md) combine the verified compiler's result with the generators' theorems on period and orbit.  The LCG and xorshift64 also have compiled jump-ahead functions, proved equal to repeated steps, and theorems that count how often each value of the top bits occurs over a period.  The LCG proofs give hyperplane bounds and spectral-test values for tuples of two to six successive states.  The linked documents state the parameters, domains, and memory conditions.

[The `Examples/Prng` example](Examples/Prng/README.md) implements SplitMix64, the generator of Steele, Lea, and Flood, in the form of Vigna's reference C code.  It also implements `unitFloat`, which maps a word `x` to the binary64 value `(x >>> 11) / 2^53` in `[0, 1)`.  The theorems `splitMix_implements`, `unitFloat_implements`, and `prng_bytes` state that the compiled module computes the Lean definitions, and [the `splitmix64` entry of the LTG knowledge base](ltg/entries/splitmix64/README.md) lets other modules compile and call both functions.

## 6. Floating-point folds

Each fold performs its operations in the order that the table gives and rounds after each one, so its result depends on that order.  The theorem for each fold states that the compiled module computes the Lean definition bit for bit.  No theorem bounds a fold's error against the exact result.

| Fold | Implementation | Order |
|---|---|---|
| Sum | `total` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | Left to right |
| Pairwise sum | `sumRange` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean) | Recursive halves of the index range |
| Sum of the flagged elements | `select` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | Left to right |
| Sum of squares | [The `Examples/SumSquares` example](Examples/SumSquares/README.md) | Left to right (`sumSquares_bytes`) |
| Mean | [The `Examples/Mean` example](Examples/Mean/README.md) | The left-to-right sum divided by the length, NaN for an empty array (`mean_bytes`) |
| Harmonic number | `harmonic` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `1/1 + 1/2 + ⋯ + 1/n` left to right.  The denominator is a binary64 value, so from `2^53` on, adding 1 leaves it unchanged. |
| Dot product | `dot` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | Left to right, with the second array read as 0 past its end |
| Matrix-vector product in binary32 | `matVec32` in [the `Examples/Binary32` example](Examples/Binary32/README.md) | Each row's dot product left to right (`matVec32_implements`, `binary32_bytes`) |
| Maximum | `largest` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | Left to right, negative infinity for an empty array |

## 7. Demonstration programs

These programs test the compilers on numerical code.  The theorem for each states that the compiled module computes the Lean definition bit for bit: the verified compiler's theorem for a program in `Verified/`, and the example's theorem for a program in `Examples/`.  Arithmetic on words wraps modulo `2^64`.

| Program | Implementation | Computation |
|---|---|---|
| Scaled hypotenuse | `hypot` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `sqrt (x * x + y * y) / s`.  The sum of squares can overflow even when the exact result is finite. |
| Newton's square root | `newtonSqrt` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | `x ↦ (x + a/x)/2` from `x = a` until `\|x² - a\| ≤ 10^-12 a`, for at most 64 steps |
| `axpy` | `axpy` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | `a * x + y` for each element, written over `y` |
| Grid | `grid` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | The points `x0 + i * dx` for `0 ≤ i < n` |
| Scaling by a power of two | `scaleByPower` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `x * 2^k` for `k` from 0 to 1023, with the power built from its exponent field |
| Mean of the indices | `mean` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `(0 + 1 + ⋯ + (n - 1))/n` in binary64, NaN for `n = 0` |
| Falling body | `fall` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | Explicit Euler steps under gravity until the height reaches 0, for at most 100,000 steps |
| Histogram bucket | [The `Examples/Bucket` example](Examples/Bucket/README.md) | `((x - lo) / width).toUInt64`, with Lean's saturating conversion (`bucket_bytes`) |
| Arithmetic in binary32 | `axpy32`, `hypot32`, `ratio32`, `scale32`, and `axpyArray32` in [the `Examples/Binary32` example](Examples/Binary32/README.md) | Scalar and elementwise operations on `Float32` (an `implements` theorem for each, and `binary32_bytes`) |
| Verified WGSL kernels | [The kernel examples](Verified/Examples/Wgsl.lean) and [native-value dispatch proofs](Verified/Examples/WgslProof.lean) | Binary32 scaling and a conditional sum with a loop in one branch, Boolean arrays, a word scan, and square root after nearest-even rounding.  Wasm correctness and, under the device model, correct and race-free WGSL dispatch. |
| Binary32 GPT-2 | [The binary32 program](Examples/Gpt32/README.md#verified-compiler), [its Verified compilation](Verified/Examples/Gpt32.lean), and [its host proof](Verified/Examples/Gpt32Host.lean) | Thirteen unchanged functions with generated Wasm execution, allocation-bound, trap-free, and byte theorems.  Under the device model, WGSL generation returns the native step's scores, with every dispatch race-free. |
| Triangle numbers, Fibonacci numbers, powers, sums of powers | `triangle`, `fib`, `power`, and `sumPowers` in [`Verified/Examples/Loops.lean`](Verified/Examples/Loops.lean) | Loops on words |
| Fibonacci pairs | `fibPair` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean) | Recursion on a pair of words |
| Word folds | `sum` and `dot` in [`Verified/Examples/Arrays.lean`](Verified/Examples/Arrays.lean), and the product and exclusive or in [the `Examples/SumArray` example](Examples/SumArray/README.md) | Left folds over arrays of words (`productArray_implements`, `xorArray_implements`) |
| Collatz map | `collatz` in [`Verified/Examples/Loops.lean`](Verified/Examples/Loops.lean) and `collatzSteps` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | `n` iterations of the map from `x`, and the number of steps to reach 1, counted up to 1,000 |
