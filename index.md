# Seminumerical algorithms

This index lists the compiled arithmetic and numerical algorithms and their proved results.  The [verified compiler](docs/verified-manual.md) compiles the implementations in `Verified/Examples/` and the generators defined in `Examples/Lcg/`, `Examples/ParkMiller/`, and `Examples/Xorshift/`.  The other entries in `Examples/` use the [LeanExe compiler](docs/leanexe-manual.md) and a proof per program.  The applications have separate guides: [the Euler solvers](Examples/Euler/README.md), [binary64 GPT-2](Examples/Gpt/README.md), [binary32 GPT-2 and its WGSL kernels](Examples/Gpt32/README.md), and [the drone planner](Examples/Drone/README.md).

A compiler theorem states that the module computes the Lean definition.  A numerical byte theorem combines that result with a mathematical accuracy statement.  A file theorem connects the encoding to the file emitted in `build/verified/`.  These claims use Talos's WebAssembly semantics and the deterministic floating-point profile.  Calls require the allocator invariant and, where applicable, borrowed tables, memory, and recursion bounds.  Each linked guide states those premises, exceptional inputs, and host assumptions.  [The transcendental development record](transcendentals.md) preserves the proof history and the remaining Bessel range.

## Elementary and special functions

The real arguments and results use binary64.  `jn` and `yn` also take an order word, whose low 32 bits encode a signed integer.  A bound of `n` steps permits a distance of at most `n` from the nearest-even rounding of the exact real result on the ordered line of doubles, with both signed zeros at the same position and infinities at its ends.  The bounds below apply to finite inputs in the stated domains.  Each function's guide gives its exceptional-value theorems.

| Functions | Document | Origin | Bound | Byte theorem |
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

The logarithms `log`, `log2`, and `log10` require `x > 0`, and `log1p` requires `x > -1`.  `asin` and `acos` require `-1 ≤ x ≤ 1`, `acosh` requires `x ≥ 1`, and `atanh` requires `-1 < x < 1`.  The `atan2 y x` bound requires finite `x` and `y` with `y ≠ 0`.  The `tanpi` bound excludes half-integers.  For finite `x` and `y`, the `pow x y` bound covers positive `x`, negative `x` with integer `y`, and zero `x` with `y ≥ 0`.  The gamma bounds exclude zero and the negative integers.  The other rows cover every finite input.

[`Log2Power.log2_power`](Verified/Examples/Log2Power.lean) proves exact results at representable powers of two other than 1, whose result `+0` is given by `Log2Theorem.log2_one`.  [`Log10Theorem.log10_pow10`](Verified/Examples/Log10Theorem.lean) proves exact results at `10^n` for `0 ≤ n ≤ 22`, and [`LgammaSign.lgammaR_sign`](Verified/Examples/LgammaSign.lean) proves the sign returned by `lgammaR`.  The ports of `sin`, `cos`, and `tan` reduce large arguments by the method of Payne and Hanek in 64-bit word arithmetic, after Go's `math.trigReduce`.  [`TrigDistance.quadrant_distance`](Verified/Examples/TrigDistance.lean) bounds how close a double comes to a multiple of `π/2`.

### Bessel functions

For the [Bessel functions](Verified/Examples/Bessel.md), let `u = 2^-53` and `M_n(x) = √(J_n(x)² + Y_n(x)²)`.  The modulus bound measures absolute error in units of `u M_n`, which remain positive at zeros of either function.  The implementations come from fdlibm.

| Function | Proved bound | Finite-input domain |
|---|---|---|
| `j0`, `j1` | `10 u M_0(\|x\|)`, `12 u M_1(\|x\|)` | Every finite `x` |
| `y0` | `11 u M_0(x)` | `x > 0` |
| `y1` | `12 u M_1(x)` from `2^-1022` on, and one representable step below the high-word cutoff `0x3c900000` (about `2^-54`) | The two results together cover every `x > 0` |
| `jn` | `(23 + 12 \|n\|) u M_\|n\|(\|x\|)` | Every finite `x` outside the range below |
| `yn` | `(250 + 12 \|n\|) u M_\|n\|(x)` when the result is finite, with an overflow alternative | `x > 0` outside the range below |

Both integer-order theorems exclude `2 ≤ |x| < 2^302` with `|n| > |x|/2`.  That range needs a modulus bound through the turning point `k = x` and remains open.  For `yn`, the theorem permits the infinity with the sign of `Y_n(x)` only when `|Y_n(x)| > 2^1023`, and proves that infinity when `|Y_n(x)| ≥ 2^1025`.  Between those thresholds it permits either that infinity or a finite result within the bound.  [The Bessel byte theorems](Verified/Examples/BesselBytes.lean), joined by [`BesselBytes.bessel_module_accuracy`](Verified/Examples/BesselBytes.lean), carry these statements to the module.  [The file theorems](Verified/Examples/BesselFile.lean) identify `build/verified/bessel.wasm`.

## Conversion between decimal strings and binary floating point

| Functions | Document | Method | Theorems |
|---|---|---|---|
| `parse64`, `parse32` | [Decimal to binary conversion](Verified/Examples/ParseFloat.md) | Clinger's fast path for short inputs and otherwise one exact rounding by Cox's unrounded scaling, for strings of fewer than `2^32` bytes in RFC 8259's grammar or a `strtod`-like superset | [`ParseFloatBytes.parse64_bytes_accuracy`](Verified/Examples/ParseFloatBytes.lean), `parse32_bytes_accuracy`: the word of roundTiesToEven applied to the number the string denotes, or a rejection.  [`ParseFloatFile.parse_file`](Verified/Examples/ParseFloatFile.lean). |
| `print64`, `print64Ecma`, `print32`, `print32Ecma` | [Binary to decimal conversion](Verified/Examples/PrintFloat.md) | For finite nonzero inputs, the shortest decimal that rounds back to the word, nearest to its value among the shortest, with an even last digit at a tie, in a scientific or an ECMAScript layout | [`PrintFloatBytes.print64_bytes_accuracy`](Verified/Examples/PrintFloatBytes.lean) and the three others: parsing the output recovers the input with any NaN replaced by the canonical NaN.  Outputs for finite inputs follow RFC 8259's number grammar and have the shortest digits when the input is nonzero.  [`PrintFloatFile.print_file`](Verified/Examples/PrintFloatFile.lean). |

## Arithmetic

| Algorithm | Implementation | Result |
|---|---|---|
| Fused multiply-add | [The software fused multiply-add](Verified/Examples/Fma.md): [`Fma.fma`](Verified/Examples/Fma.lean), with 128-bit products and shifts in 64-bit words | [`FmaTheorem.fma_toBits`](Verified/Examples/FmaTheorem.lean): equal to IEEE 754's fusedMultiplyAdd with roundTiesToEven for all operands.  The ports of `erfc`, `tgamma`, and `lgamma` compile it in their modules. |
| Natural numbers of any size and Cox's unrounded scaling | [Natural numbers on limbs](Verified/Examples/Uscale.md): `Uscale`, on 32-bit limbs in 64-bit words, with multiplication by a word, shifts, comparison, subtraction, division, and powers of 10 | One theorem per routine stating its result as a natural number.  The decimal parsers and printers call these routines. |
| Integer ceiling square root | `ceilSqrt` in [the drone planner](Examples/Drone/README.md), compiled unchanged by [`Verified/Examples/Drone.lean`](Verified/Examples/Drone.lean), by 17 halvings of a bracket | `Examples.Drone.ceilSqrt_correct`: the exact ceiling square root for arguments up to `2^32`. |
| Greatest common divisor | `gcd` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean), Euclid's remainder recursion | The compiler's theorem.  [The `Examples/Gcd` example](Examples/Gcd/README.md) compiles the same recursion and proves that its bytes compute `Nat.gcd` (`gcd_eq`, `gcd_bytes`). |
| Count of prime factors | [The `Examples/PrimeFactors` example](Examples/PrimeFactors/README.md), trial division in increasing order | `compute_eq` and `primeFactors_bytes`: the module's bytes compute the length of Mathlib's `Nat.primeFactorsList`. |
| Sieve of Eratosthenes | `sieve` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | The compiler's theorem. |
| Power modulo `2^64` by squaring | `pow` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean) | The compiler's theorem. |

## Discrete Fourier transform

[The Fourier implementation](Verified/Examples/Fourier.lean) computes the discrete Fourier transform of interleaved complex floats by the `n²` products of the definition, its inverse, and the power spectrum of real samples, with factors from [`Trig.cosWith`](Verified/Examples/Trig.lean) and [`Trig.sinWith`](Verified/Examples/Trig.lean).  The compiler's theorem states that the module computes these definitions bit for bit.  [The native accuracy test](Verified/Examples/FourierAccuracy.lean) compares the results with an exact transform and reports error on its argument sets.

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
| Harmonic number | `harmonic` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | Adds `1/d` and increments the binary64 denominator `d` from 1 on each pass.  At `2^53`, adding 1 leaves `d` unchanged. |
| Mean | [The `Examples/Mean` example](Examples/Mean/README.md) | The left-to-right sum divided by the length, NaN for an empty array (`mean_bytes`) |
| Sum of squares | [The `Examples/SumSquares` example](Examples/SumSquares/README.md) | Left to right (`sumSquares_bytes`) |
| Matrix-vector product in binary32 | `matVec32` in [the `Examples/Binary32` example](Examples/Binary32/README.md) | Each row's dot product left to right (`matVec32_implements`, `binary32_bytes`) |

## Demos

These programs exercise the compilers on numerical code.  The theorem of each states that the compiled module computes the Lean definition bit for bit: the Verified compiler's theorem for a program under `Verified/`, and the example's own proof for a program under `Examples/`.  The arithmetic on words wraps modulo `2^64`.

| Program | Implementation | Computation |
|---|---|---|
| Scaled hypotenuse | `hypot` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `sqrt (x * x + y * y) / s`.  The sum of squares can overflow even when the mathematical result is finite. |
| Newton's square root | `newtonSqrt` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | `x ↦ (x + a/x)/2` from `a`, at most 64 steps, until `\|x² - a\| ≤ 10^-12 a` |
| `axpy` | `axpy` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | `a * x + y` for each element, written in place |
| Grid | `grid` in [`Verified/Examples/Elements.lean`](Verified/Examples/Elements.lean) | The points `x0 + i * dx` |
| Scaling by a power of two | `scaleByPower` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `x * 2^k` for `k` from 0 to 1023, with the power built from its exponent field |
| Mean of the indices | `mean` in [`Verified/Examples/Floats.lean`](Verified/Examples/Floats.lean) | `(0 + 1 + ⋯ + (n - 1))/n` in binary64 |
| Falling body | `fall` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | Explicit Euler steps under gravity until the height reaches 0 |
| Triangle numbers, Fibonacci numbers, powers, sums of powers | `triangle`, `fib`, `power`, and `sumPowers` in [`Verified/Examples/Loops.lean`](Verified/Examples/Loops.lean) | Loops on words |
| Fibonacci pairs | `fibPair` in [`Verified/Examples/Recursion.lean`](Verified/Examples/Recursion.lean) | Recursion on a pair of words |
| Word folds | `sum` and `dot` in [`Verified/Examples/Arrays.lean`](Verified/Examples/Arrays.lean), and the product and exclusive or in [the `Examples/SumArray` example](Examples/SumArray/README.md) | Left folds over arrays of words (`productArray_implements`, `xorArray_implements`) |
| binary32 arithmetic | `axpy32`, `hypot32`, `ratio32`, `scale32`, and `axpyArray32` in [the `Examples/Binary32` example](Examples/Binary32/README.md) | Scalar and elementwise operations on `Float32`, each with an `implements` theorem, and `binary32_bytes` |
| Verified WGSL kernels | [The kernel examples](Verified/Examples/Wgsl.lean) and [native-value dispatch proofs](Verified/Examples/WgslProof.lean) | Binary32 scaling and a conditional sum with a loop in one branch, Boolean arrays, a word scan, and square root after nearest-even rounding.  Wasm correctness and, under the device model, correct and race-free WGSL dispatch. |
| Binary32 GPT-2 | [The binary32 program](Examples/Gpt32/README.md#verified-compiler), [its Verified compilation](Verified/Examples/Gpt32.lean), and [its host proof](Verified/Examples/Gpt32Host.lean) | Thirteen unchanged functions with generated Wasm execution, allocation-bound, trap-free, and byte theorems.  Under the device model, WGSL generation returns the native step's scores, with every dispatch race-free. |
| Histogram bucket | [The `Examples/Bucket` example](Examples/Bucket/README.md) | `((x - lo) / width).toUInt64`, with Lean's saturating conversion (`bucket_bytes`) |
| Collatz map | `collatz` in [`Verified/Examples/Loops.lean`](Verified/Examples/Loops.lean) and `collatzSteps` in [`Verified/Examples/Repeat.lean`](Verified/Examples/Repeat.lean) | `n` iterations, and the number of steps to 1 up to 1,000 |
