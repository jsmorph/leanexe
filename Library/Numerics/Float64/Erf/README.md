# The error function and its complement

[The implementation of `erf`](Program.lean) ports fdlibm from FreeBSD msun [1] and calls [Arm's exponential](../Exp/README.md).  [The separate implementation of `erfc`](../Erfc/Program.lean) ports CORE-MATH [10] and uses [the software fused multiply-add](../../Arithmetic/Fma/README.md).  `ErfTheorem.erf_within_one` and `ErfcTheorem.erfc_within_one` prove one representable step from nearest-even rounding at every finite input.  [The `erf` byte theorem](ErfTheorem.lean) and [the `erfc` byte theorem](../Erfc/ErfcBytes.lean) carry those bounds to their modules.  [The `erf` file theorem](ErfFile.lean) and [the `erfc` file theorem](../Erfc/ErfcFile.lean) identify the emitted `build/verified/erf.wasm` and `erfc.wasm`.

## Specification

`LeanExe.ProofKit.RealErf` defines the functions that Mathlib lacks: `erf x = (2/√π) ∫₀ˣ exp (-t²) dt`, the definition of DLMF 7.2.1 [4], and `erfc x = 1 - erf x`, which DLMF 7.2.2 gives as the same integral from `x` to `∞` [4].  `erfcx x = exp (x²) erfc x` is the scaled complement that the proof of the tail uses.  Every finite double is in the domain of both functions.  `erf` lies in `(-1, 1)` and `erfc` in `(0, 2)` (`RealErf.neg_one_lt_erf`, `erf_lt_one`, `erfc_pos`, `erfc_lt_two`), so neither overflows.  The asymptotic expansion 7.12.1 [4] puts `erfc x` in the subnormal range from about 26.54 and rounds it to `+0` from about 27.23.

The bound of `erf` is `ErfTheorem.erf_within_one`: for finite `x`, `F64SignedRounding.WithinSteps 1 (RealErf.erf (value x.toBits)) (Erf.erf x).toBits`.  [The signed rounding module](../../../../LeanExe/ProofKit/F64SignedRounding.lean) defines `WithinSteps n y w`: `w` is not a NaN, and its position on the ordered line of doubles, with both zeros at 0, differs by at most `n` from that of the nearest-even rounding of `y`, which is the negation of the nonnegative rounding of `|y|` for negative `y`.  The decided bound for `erfc`, one step for the CORE-MATH port in [the plan's decisions](../../../../transcendentals.md#decisions), has the same form with `RealErf.erfc`, and `ErfcTheorem.erfc_within_one` proves it.

| Input | `erf` | `erfc` | Source of the rule | Theorem |
|---|---|---|---|---|
| `+0`, `-0` | `+0`, `-0` | `1` | C99 F.9.5.1 [6] for `erf`; `erfc (0) = 1` from the definition | `erf_pos_zero`, `erf_neg_zero`; `erfc_within_one` within one step |
| `+∞` | `1` | `+0` | C99 F.9.5.1 and F.9.5.2 | `erf_pos_infinity`, `ErfcNonfinite.erfc_pos_inf` |
| `-∞` | `-1` | `2` | C99 F.9.5.1 and F.9.5.2 | `erf_neg_infinity`, `ErfcNonfinite.erfc_neg_inf` |
| NaN | the canonical NaN `0x7FF8000000000000` | the canonical NaN | C99 F.9 paragraph 11; the deterministic profile of WebAssembly [7] | `erf_nan`, `ErfcNonfinite.erfc_nan` |
| finite | within one step of `erf a` | within one step of `erfc a` | | `erf_within_one`, `ErfcTheorem.erfc_within_one` |

The recommended operations of IEEE 754-2019 clause 9.2 omit the error functions [5], so C99's Annex F fixes their special values.  The `erfc` column states what the port of CORE-MATH's `erfc` returns, the values that fdlibm's `erfc` also gave, by these expressions: `1` at both zeros as `fma (-x, 2^-54, 1)`, `+0` at `+∞`, `2` at `-∞`, and the canonical NaN for a NaN as `x + x`.  It also returns `2` from `-0x1.7744f8f74e94bp+2`, about -5.86, down, as `2 - 2^-54` rounded, and `+0` from `0x1.b39dc41e48bfdp+4`, about 27.23, up, as `2^-1074 · 0.25` rounded, where `erfc x` lies below `2^-1075`.  The theorems say nothing about floating-point exceptions, which the port does not compute.

## Algorithm

fdlibm splits the range of `|x|` into five parts, and the comment of `s_erf.c` gives the formulas [1].  The `erfc` column of the table below describes fdlibm's `erfc`, which shares the ranges and kernels with `erf` and which the module no longer exports.  `erf` is odd and `erfc (-x) = 2 - erfc x` (DLMF 7.4.1 and 7.4.2 [4]), so the code works with `|x|` and restores the sign at the end, except on the first range, where it applies the same operations to `x`.  fdlibm states an error bound for `erf` on the first range only, below one unit in the last place.

| Range of `\|x\|` | `erf` | `erfc` | Approximation |
|---|---|---|---|
| below `2^-28` | `x + efx · x`, with `(8 x + efx8 · x)/8` below `2^-1015` | `1 - x` below `2^-56` | `efx` is `2/√π - 1` rounded. |
| `[2^-28, 0.84375)`, and for `erfc` `[2^-56, 0.84375)` | `x + x R (x²)` | `1 - (x + x R)` below `1/4` and for negative `x`, `0.5 - (x R + (x - 0.5))` from `1/4` on | `R = pp/qq` of degrees 4 and 5 approximates `(erf x - x)/x`. |
| `[0.84375, 1.25)` | `±(erx + P (s)/Q (s))`, `s = \|x\| - 1` | `(1 - erx) - P/Q`, or `1 + (erx + P/Q)` for negative `x` | `erx` is the decimal `0.84506291151` rounded to single precision, and `P/Q` of degrees 6 and 6 approximates `erf (1 + s) - erx`. |
| `[1.25, 6)` and, for `erfc`, `[1.25, 28)` | `1 - r/x` | `r/x`, or `2 - r/x` for negative `x` | `r = exp (-z² - 0.5625) · exp ((z - x)(z + x) + R (s)/S (s))` with `s = 1/x²`, where `R/S` approximates `log (x erfc x) + x² + 0.5625`: `R_a/S_a` of degrees 7 and 8 below `1/0.35`, `R_b/S_b` of degrees 6 and 7 above. |
| `6` and above | `±(1 - tiny)` | the tail formula for `6 ≤ x < 28`, `tiny · tiny` from 28 on, and `2 - tiny` for `x ≤ -6` | `tiny = 1.0e-300`, and the results round to `±1`, `+0`, and `2`. |

The first range starts from the power series `erf x = (2/√π) Σ (-1)^n x^(2n+1)/(n! (2n+1))` (DLMF 7.6.1 [4]), and fdlibm chose 0.84375 so that the error of `erf` stays below one unit in the last place there.  Above 1/4, `erfc` regroups `1 - x - x R` as `0.5 - (x R + (x - 0.5))`, where `x - 0.5` is exact.  On the middle range `erx` has 24 significant bits, so `1 - erx` is exact, and the rational function carries only the small difference `erf (1 + s) - erx`, below 0.078 in magnitude by fdlibm's comment.

The tail follows the asymptotic expansion `erfc x ~ exp (-x²)/(x √π) Σ (-1)^m (1/2)_m x^(-2m)` (DLMF 7.12.1 [4]), which fdlibm's comment names: the code computes the factor `exp (-x²)/x` with the exponential, and `R/S` models the logarithm of the rest, `log (x erfc x) + x²`, offset by `0.5625`.  The offset `9/16` is exact in binary and close to `log √π ≈ 0.5724`, so `R/S` stays near its constant term, about `-0.0099`.  The exponential's relative error grows with the absolute error of its argument, and `x²` reaches 784, so the code splits `-x²` as `-z² + (z - x)(z + x)`, where `z` keeps the high 32 bits of `x`.  `z` has at most 21 significant bits, so `z²` is exact, and the correction `(z - x)(z + x)` is small.  The comment of `s_erf.c` calls the target of `R/S` `log (erfc x · x) - x² + 0.5625`, but its own formula `erfc x = exp (-x² - 0.5625 + R/S)/x` requires `+ x²`, as [the port's journal section](../../../../devnotes.md#2026-10-10-ports-of-sinpi-cospi-tanpi-erf-and-erfc) notes and the docstring of `Erf.lean` states.

### CORE-MATH's `erfc`

CORE-MATH's `erfc` [10] computes a double-double `h + l` with an absolute error bound `err` and returns `h + (l - err)` when it equals `h + (l + err)`, and otherwise calls an accurate path that recomputes the value to about 104 bits.  On `[-0x1.c5bf891b4ef6ap-54, 0x1.c5bf891b4ef6ap-55]` it returns `fma (-x, 2^-54, 1)`, which rounds to 1, and outside `(-0x1.7744f8f74e94bp+2, 0x1.b39dc41e48bfdp+4)` it returns 2 or `+0` as the specification states.  For negative `x` the fast path computes `1 + erf (-x)` (DLMF 7.4.2 [4]), and up to `0x1.713786d9c7c09p+1`, about 2.885, it computes `1 - erf x`.  `erf z` comes from an odd polynomial of degree 11 below `1/16` and from a polynomial of degree 10 in `z - (2 i + 1)/32` on `[i/16, (i + 1)/16)` for `1 ≤ i ≤ 94`, whose coefficients of degree 0 and 1 are double-doubles, with stated relative error bounds `0x1.78p-69` and `0x1.11p-69`.

Above `0x1.713786d9c7c09p+1` the fast path computes `erfc x = exp (-x²) p (1/x)`, where `p (y)` approximates `erfc (1/y) exp (1/y²)` by an odd polynomial of degree 23 on six intervals of `y`, in the variable `y²`.  `1/x` is a double-double from one Newton step, and `exp (-x²)` comes from `exp_1` of CORE-MATH's `pow`, which writes the argument as `k log 2/4096` plus a remainder below `0.00013`, takes `2^(k/4096)` from two tables of 64 double-doubles of `2^(i/64)` and `2^(i/4096)`, and evaluates a polynomial of degree 4.  The code bounds the relative error of this path by `2^-67.115` and sends arguments from `0x1.9db1bb14e15cap+4` on to the accurate path.  The accurate path evaluates `erf` with an odd polynomial of degree 21 below `1/8` and with polynomials of degree 18 on `[i/8, (i + 1)/8)` for `1 ≤ i ≤ 47`, whose coefficients of degree 0 to 7 are double-doubles, and computes `erfc x` above `0x1.b59ffb450828cp+0`, about 1.71, as `exp (-x²) p (1/x)` with odd polynomials of degree 29 to 47 on ten intervals of `1/x`.  There `exp_accurate` reduces by `log 2` in three parts and evaluates a polynomial of degree 19, and the result `(h + l) 2^e` is rounded once, also when it is subnormal.  Tables of 68 inputs supply the results that even the accurate path cannot round, and the input `0x1.a8f7bfbd15495p+4`, whose result is subnormal, has a case of its own.

## Implementation

The source is `lib/msun/src/s_erf.c` of FreeBSD [1].  Its notice reads "Copyright (C) 1993 by Sun Microsystems, Inc.  All rights reserved.  Developed at SunPro, a Sun Microsystems, Inc. business.  Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved."  The module docstring of [the implementation](Program.lean) quotes the notice verbatim, as the notice requires.

`verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, erfSmall, erfMiddle, erfTail, erfExp, erfWith, erf]` compiles the exponential's functions into the module, so the module carries Arm's exponential and borrows `Exp.expTable` at address 4096, as [the exponential's module](../Exp/README.md) does.  With the runtime's `alloc` and `release` first, `erf` is function 10; it was function 11 while `erfcWith` came before it.  fdlibm's `erf` and `erfc` call fdlibm's `exp` from `e_exp.c`, which reduces by `ln 2`, approximates `exp r` by a rational form with a Remez polynomial of degree 5, and states an error below one unit in the last place [2].  The port calls `Exp.expWith Exp.expTable` instead, Arm's table-driven exponential with a stated error of 0.511 units [3], so its results can differ from FreeBSD's in the last bit.  The proof uses only the relative bound `1.405 · 2^-53` for each of the two exponentials, which `ErfPositive.expWith_relative` derives from `ExpTightFloat.exp_relative`.

| C code | Port | Reason |
|---|---|---|
| The rational functions written out in both `erf` and `erfc` | `erfSmall`, `erfMiddle`, `erfTail`, and `erfExp`, with the same operations in the same order | One definition for both entries, and one set of proofs. |
| `static const volatile double tiny` and the expressions `one-tiny`, `tiny-one`, `two-tiny`, and `tiny*tiny`, which fdlibm evaluates to raise the inexact and underflow flags | ordinary rounded sums and products with the same values | The dialect has no floating-point flags and no `volatile`. |
| `GET_HIGH_WORD (hx, x)` into a signed `int32_t` | `hx := x.toBits >>> 32`, a word, and `neg := hx >>> 31 == 1` | A signed comparison of `hx` with a positive bound also tests the sign, so `hx < 0x3fd00000` becomes `neg \|\| hx < 0x3fd00000`, and `hx >= 0` becomes `!neg`.  `erfc`'s `hx > 0` equals `!neg` on the ranges where it occurs. |
| `SET_LOW_WORD (z, 0)` | `Float.ofBits (x.toBits &&& 0xFFFFFFFF00000000)` | The same word. |
| `(double)(1-i)+one/x` | `(if neg then -1.0 else 1.0) + 1.0/x` | The same values for infinities and NaN. |
| `exp` | `Exp.expWith tab` | As above. |

A script that compares the port with the pinned `s_erf.c` finds that the decimal literal of each of the 56 constants annotated with hexadecimal words converts to those bits and equals the port's `Float.ofBits` word, and that `tiny` is the word `0x01A56E1FC2F8F359` of `1.0e-300`.  The journal records the same check of the 56 constants against their decimals ([the port's journal section](../../../../devnotes.md#2026-10-10-ports-of-sinpi-cospi-tanpi-erf-and-erfc)).  The thresholds `0x7ff00000`, `0x3feb0000`, `0x3e300000`, `0x00800000`, `0x3ff40000`, `0x40180000`, `0x4006DB6E` (`erf`), `0x3c700000`, `0x3fd00000`, `0x4006DB6D` (`erfc`), and `0x403c0000` are those of the C code, and `ErfBits` computes the value of the double with each threshold of `erf` as its high word.  `erf` switches tail kernels at the high word `0x4006DB6E` and `erfc` at `0x4006DB6D`, as fdlibm does, so `ErfTailKernel` proves `R_a/S_a` up to the first and `R_b/S_b` from the second, which covers every argument at which either function calls each kernel.

### The port of CORE-MATH's `erfc`

[The port](../Erfc/Program.lean) follows `src/binary64/erfc/erfc.c` of CORE-MATH [10], which carries "Copyright (c) 2022-2026 Alexei Sibidanov, Paul Zimmermann, Tom Hubrecht and Claude-Pierre Jeannerod" and the MIT license; the module docstring quotes the notice in full.  The port follows the C code operation for operation and calls `Fma.fma`, [the software fused multiply-add](../../Arithmetic/Fma/README.md), for each `__builtin_fma`, so its results should equal CORE-MATH's bit for bit.  It imports no other function of the repository: the code carries its own `exp_1` and `exp_accurate`.

| C code | Port | Reason |
|---|---|---|
| Results through pointers | Tuples | The dialect has no pointers. |
| The tables `C`, `C2`, `T1` and `T2`, `T`, `Tacc`, `E2`, and the three tables of exceptions | The arrays of words `fastTable`, `accTable`, `expTable`, `asymTable`, `asymAccTable`, `expAccTable`, and `excTable`, which `erfc` passes to `erfcWith`, with the rows of `Tacc` padded with zeros to 30 entries as in C | The arrays have docstrings with the offsets of the C arrays. |
| The short arrays `c0`, `p`, `Q_1`, and `threshold` | Constants in `erfFastTiny`, `tinyCoeff`, `q1`, `asymptIndex`, and `asymptAccIndex` | Fewer table arguments. |
| `roundeven_finite` and `__builtin_floor` | `roundEven`, which adds and subtracts `2^52`, and `floorF` | The same results for the arguments that occur, below `2^52` in magnitude. |
| `int64_t K` with `K >> 12`, `(K >> 6) & 0x3f`, and `K & 0x3f` in `exp_1` | A two's complement word with `sar` | C's arithmetic shift. |
| `int k` in `exp_accurate` | An integer-valued double | The value is between -1069 and -4. |
| `__builtin_ldexp` | `ldexp`, a product with powers of two that are doubles, through `2^1023` for exponents above 1023 | One rounding, as C's `ldexp`, for the exponents from -1069 to 1069 that occur. |
| `for (i = 0; yh > threshold[i]; i++);` | Chains of comparisons that end at the last interval without comparing with the last threshold | `yh` is at most `0x1.62fffffffffffp-2` and `0x1.2b81f34bfce35p-1` in the two domains, below the last thresholds. |
| Loops over the exceptions with an early return | `hardCase`, which scans every row | The inputs of the rows are distinct, so the result is the same. |
| `fetestexcept`, `feclearexcept`, and `errno` | Removed | The dialect has no floating-point flags and no `errno`, and the expressions that C evaluates for the flags keep their values. |

A script compared the port with `erfc.c` at the pinned commit.  Each of the 3,357 table words equals the bits of the C literal in its comment, 45 of them the zeros that pad `Tacc`, and the literals of each table appear in the order of its C array.  The 68 constants of the code that carry a C literal in a comment equal that literal's bits, the elements of the short arrays appear in the code, except the last of each array `threshold`, which the chains do not compare with, and every hexadecimal literal of the C code outside the tables appears in the port except `0x1.a8b12fc6e4892p+4`, the bound of the test of the underflow flag.  The journal records the script's output.

## Theorems

The theorems are in [the error function's theorem module](ErfTheorem.lean) and [the file module](ErfFile.lean), in the namespaces `Library.Numerics.Float64.Erf.ErfTheorem` and `Library.Numerics.Float64.Erf.ErfFile`.  `x` is a Lean `Float`, `a = value x.toBits`, and `Ready` is the store invariant of the exponential's theorem for this module: the allocator invariant, `Exp.expTable` borrowed at address 4096, and a memory cap of at most 65,535 pages.  The byte theorem uses `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `erf_within_one` | For finite `x`, `WithinSteps 1 (RealErf.erf a) (Erf.erf x).toBits`, from `ErfOdd.erfWith_within_one`. |
| `erf_pos_zero`, `erf_neg_zero` | `erf (+0)` has the bits `0` and `erf (-0)` the bits `0x8000000000000000`. |
| `erf_pos_infinity`, `erf_neg_infinity` | `erf (+∞)` has the bits `0x3FF0000000000000` and `erf (-∞)` the bits `0xBFF0000000000000`. |
| `erf_nan` | For a NaN `x`, the result has the bits `Wasm.IEEE64.canonicalNaN`. |
| `ready_initial` | The module's initial store satisfies `Ready`. |
| `erf_entry_call` | A call of function 11 from a store satisfying `Ready` returns, without a trap, the bits of `Erf.erf x`, and leaves a store satisfying `Ready` in which every heap region keeps its bytes. |
| `erf_export` | Function 11 is exported as `erf`. |
| `erf_bytes_accuracy` | `Erf.compiled.module` encodes to bytes that decode to it, exports function 11 as `erf`, starts in a `Ready` store, and every call from a `Ready` store returns the bits of `Erf.erf x`, within one step for finite `x`, and leaves a `Ready` store, so the statement covers every call in a sequence of calls to `erf`. |
| `erf_module_accuracy` | The encoding and decoding of the module, from `erf_bytes_accuracy`, for the file module. |
| `erf_file` | `build/verified/erf.wasm` holds `encode Erf.compiled.module`. |
| `erf_file_decode` | `build/verified/erf.wasm` decodes to the module of `erf_module_accuracy`. |

Each declaration of `ErfTheorem.lean` has a `#print axioms` line, and all eleven report `[propext, Classical.choice, Quot.sound]`.  `tests/verified/run.sh` builds `Library.Numerics.Float64.Erf.ErfTheorem`, checks `ErfFile.lean` against the `erf.wasm` it has written, and fails unless both file theorems report exactly the three permitted axioms.  A run of the script passed this check for its entry `erf:ErfTheorem:ErfFile`.

`ErfcTheorem.erfc_within_one` states `F64SignedRounding.WithinSteps 1 (RealErf.erfc (value x.toBits)) (Erfc.erfc x).toBits` for every finite `x`, with only `propext`, `Classical.choice`, and `Quot.sound`.  Its paths take `FmaSpec.FmaNearest` as a hypothesis, which `FmaSpecTheorem.fma_nearest` proves.  [The byte theorem](../Erfc/ErfcBytes.lean), `ErfcBytes.erfc_bytes_accuracy`, has the form of `erf_bytes_accuracy` with the seven tables of `Erfc.lean` borrowed: the bytes decode to the module, whose function 49 is the export `erfc`, and a call from a ready store returns `(Erfc.erfc x).toBits` without a trap, leaves a ready store, and lies within one step of `erfc x` for finite `x`.  [The file theorem](../Erfc/ErfcFile.lean) takes the module from `erfc_bytes_accuracy`, so its axiom report in `tests/verified/run.sh` covers the byte theorem.  [The section on its proof](#the-proof-of-core-maths-erfc) lists the modules.

## Proof

### Modules

The chain of `erf`'s proof has 33 modules of its own in `Verified/Examples/`, and it imports the exponential's chain and `ExpTightFloat`.  The table lists them by stage, each stage in dependency order.  [The root `Verified` import](../../../../Verified.lean) includes `ErfTheorem`, and the file check of `tests/verified/run.sh` builds it as well.

| Stage | Modules | Content |
|---|---|---|
| Kernels | `ErfKernelSmall`, `ErfKernelMiddle`, `ErfTailBase`, `ErfTailCoeffs`, `ErfTailPieces0` to `ErfTailPieces7`, `ErfTailKernel` | The approximation error of each rational function against `erf` or `log (x erfcx x)`. |
| Small range | `ErfSmallBase`, `ErfSmallPieces0`, `ErfSmallPieces1`, `ErfSmall` | `[2^-28, 0.84375)`, in 74 intervals. |
| Middle range | `ErfMiddleBase`, `ErfMiddle` | `[0.84375, 1.25)`, in 13 intervals. |
| Ends | `ErfEnds`, `ErfSub` | Below `2^-28`, the subnormal inputs, and from 6 on. |
| Tail | `ErfTailSplit`, `ErfTailEval`, `ErfTailCompose`, `ErfTailErfBase`, `ErfTailErf` | `[1.25, 6)`, in 30 intervals: the exact split of `x²`, the argument of the second exponential, and the composition. |
| Paths and sign | `ErfBranches`, `ErfBits`, `ErfPositive`, `ErfNegative`, `ErfOdd` | The code's path for each range, positive arguments, and negative arguments by oddness. |
| Assembly | `ErfTheorem`, `ErfFile` | The exceptional values and the byte and file theorems. |

### Real analysis

[The real error function module](../../../../LeanExe/ProofKit/RealErf.lean) proves the facts that the kernels need, from Mathlib's fundamental theorem of calculus, `integral_gaussian_Ioi`, and the 20-digit bounds `pi_gt_d20` and `pi_lt_d20` on `π` [8].  `scale_bounds` encloses `2/√π` between `333038747416263463341/2^68` and `333038747416263463344/2^68`.  `erf_neg` gives oddness (DLMF 7.4.1), `hasDerivAt_erf` the derivative `(2/√π) exp (-x²)`, and `tendsto_erf` the limit 1 at infinity from the Gaussian integral.

| Theorem | Statement | DLMF |
|---|---|---|
| `erf_series` | For every real `x`, the partial sum of `n` terms of the series of 7.6.1 errs by at most `(2/√π) \|x\|^(2n+1)/(n! (2n+1))`, by integrating `exp_nonpos_remainder`, the Taylor remainder of `exp` at a nonpositive argument. | 7.6.1 |
| `erfc_asym` | For `x > 0` and every `N`, `(-1)^N (erfc x - asym N x) ≥ 0`, where `asym N` is the sum of the first `N` terms of the asymptotic expansion: the remainder has the sign of the first omitted term. | 7.12.1 and the remark after it for real `x` |
| `hasDerivAt_erfcx` | `erfcx' = 2 x erfcx - 2/√π`. | |
| `erfcx_backward`, and `RealErfScaled.ode_backward` for `erfcxN = erfcx/(2/√π)` | If a function `p` satisfies the equation within `η` on `[a, b]` with `0 ≤ a` and lies within `σ` of `erfcx` at `b`, then it lies within `σ + η (b - x)` at every `x` in `[a, b]`: errors shrink toward smaller `x`. | |

`RealErfScaled` divides out `2/√π`, so that the models of the tail carry no error from the enclosure of `π`.  DLMF states the remainder's sign for real arguments in the paragraph after 7.12.1, and `erfc_asym` proves it for this case from the sign of the derivative of `erfc - asym N` and the common limit 0.  The comparison lemma needs a known value at the right end of an interval, and the asymptotic enclosure at 28 supplies it.

### Kernel bounds

Each kernel bound is a polynomial inequality on rational intervals that [the polynomial bound](../../../../LeanExe/ProofKit/PolyBound.lean) and [its extensions](../../../../LeanExe/ProofKit/PolyChecks.lean) check with `decide +kernel`.  The small and middle kernels compare the rational function with a partial sum of the series, 20 terms on the first range and 26 on the middle range, the latter shifted to `s` by `PolyBound.shift`.  The tail kernels follow `erfcxN` with 32 polynomial models of degree 16 from 28 down to 1.25, each checked against the differential equation and chained downward with `ode_backward` from the asymptotic enclosure at 28, and they bound the derivative of the kernel's error on each piece and its value at 41 anchors.

| Kernel | Proved bound | Largest error found | `s_erf.c`'s statement | Theorem |
|---|---|---|---|---|
| `pp/qq` on `\|x\| ≤ 0.84375` | `(21/32) 2^-55 \|x\|` | `2^-55.86`, at `z = 0` | `2^-57.90` | `ErfKernelSmall.small_kernel_error` |
| `P/Q` on `-5/32 ≤ s ≤ 1/4` | `(21/16) 2^-58` | `2^-58.20`, at `s = 1/4` | `2^-59.06` | `ErfKernelMiddle.middle_kernel_error` |
| `R_a/S_a` on `[1.25, tailB2]`, `tailB2 ≈ 2.8571434` the double with high word `0x4006DB6E` | `2^-56` | `2^-58.27`, near `x = 1.455` | `2^-62.57` | `ErfTailKernel.tail_kernel_a` |
| `R_b/S_b` on `[tailB1, 28]`, `tailB1 ≈ 2.8571415` the double with high word `0x4006DB6D` | `2^-56` | `2^-59.34`, at `x = 28` | `2^-61.52` | `ErfTailKernel.tail_kernel_b` |

The errors found exceed the source's statements for all four kernels.  On the first range the largest error lies at `z = 0`, where `pp0` is `2/√π - 1` rounded one unit below `efx`, which the source's figure leaves out.  The tail figures come from 401 sample points per kernel against a 60-digit evaluation in the scratch scripts of the proof, so the source's statements do not bound the absolute error of `R/S` against `log (x erfcx x) + 0.5625`.  The uniform `2^-56` of the tail kernels is the level the proof's budgets were set to, and it costs about `0.125 u` in the budget of the computed `erfc`.

### Error budget of `erf`

Let `u = 2^-53`.  On most ranges the proof bounds the error before the final rounding and applies one of two criteria.  `F64RelativeSteps.within_steps_relative` turns a relative error of `(m + 3/8) u` into `m` steps for `|y| ≥ (17/16) 2^-1022`, and `F64AddNearest.within_of_nearest` uses the fact that a rounded positive sum is a nearest double of the exact sum, so that an exact sum within `m` spacings of the reference rounds within `m` steps of it.  `F64RelativeSteps.within_steps_low` handles absolute errors below `(2m + 1)/2 · 2^-1074`, the subnormal case.

| Range of `\|x\|` | Code | Bound and allowance | Margin | Theorem |
|---|---|---|---|---|
| `0` | `(8 x + efx8 · x)/8` | the word, computed | exact | `erf_pos_zero`, `erf_neg_zero` |
| `(0, 2^-1022)` | `(8 x + efx8 · x)/8` | absolute error below `1.26 · 2^-1074`, against `1.5 · 2^-1074` | 16 percent | `ErfSub.erf_subnormal` |
| `[2^-1022, 2^-1015)` | the same | `8 x` and the division by 8 exact, `1.21 u` relative, against `1.375 u` | 12 percent | `ErfSub.erf_sub_normal` |
| `[2^-1015, 2^-28)` | `x + efx · x` | `1.25 u` relative, against `1.375 u` | 9 percent | `ErfEnds.erf_tiny` |
| `[2^-28, 0.84375)` | `x + x · pp/qq (x · x)` | 74 intervals, final sum rounded to nearest; relative criterion below 0.48 and the spacing `2^-53` above; pre-rounding error `0.983` spacings near 0.84 | 1.7 percent near `x = 0.84` | `ErfSmall.small_erf` |
| `[0.84375, 1.25)` | `erx + pa/qa (x - 1)` | 13 intervals of `s`, at most `0.51` of the spacing `2^-53` | 49 percent | `ErfMiddle.middle_erf_all` |
| `[1.25, 6)` | `1 - exp (-z² - 9/16) exp (t)/x` | 30 intervals, relative error of the computed `erfc` at most `11.2 u` times `erfc 1.25 ≤ 0.0772`, below the spacing `2^-53` | 14 percent near 1.25 | `ErfTailErf.tail_erf_a`, `tail_erf_b` |
| `[6, ∞)` | `1 - tiny`, the word of 1 | `erfc 6 ≤ 2^-54` (`ErfEnds.erfc_six`), so the reference is 1 | large | `ErfEnds.erf_large` |

The figures of the table come from [the journal section of the proof](../../../../devnotes.md#2026-10-11-error-function-real-analysis-track-erf).  On the small range the Horner bound `F64Horner.hornerErr` charges each step with the magnitude of its partial polynomial on the interval, and the intervals near 0.84 have width `1/256`.  On the tail, `tail_compose` combines the two exponentials' relative errors `k = 1.405 u`, the error `δ` of the computed second argument, the kernel's `τ`, and the roundings of the product and the quotient into `(1 + k)² (1 + u)² (1 + d + d²) - 1` with `d = δ + τ`, using `x erfc x = exp (-z² - 9/16) exp ((z - x)(z + x) + R/S - tailF)`.

Negative arguments reduce to positive ones.  Below 0.84375 the code applies the same operations to `x`, and [the negation lemmas](../../../../LeanExe/ProofKit/F64NegateOps.lean) show that negating the operands negates rounded sums, products, and quotients, unless an exact sum is zero, which `ErfNegative.add_ne_zero_of_within` excludes.  From 0.84375 on the code negates its final result through the sign flag, and `RealErf.erf_neg` with `F64SignedRounding.within_negate` carries the step from `-x` to `x`.

### Shared modules

Beyond the arithmetic chain and the modules of the exponential's proof, the analysis uses [the real error function](../../../../LeanExe/ProofKit/RealErf.lean), [the scaled complement](../../../../LeanExe/ProofKit/RealErfScaled.lean), [polynomial bounds](../../../../LeanExe/ProofKit/PolyBound.lean), [polynomial checks](../../../../LeanExe/ProofKit/PolyChecks.lean), [polynomial calculus](../../../../LeanExe/ProofKit/PolyCalculus.lean), [Taylor remainders](../../../../LeanExe/ProofKit/TaylorRemainder.lean), [Horner evaluation](../../../../LeanExe/ProofKit/F64Horner.lean), [rounded division](../../../../LeanExe/ProofKit/F64DivApprox.lean), [nearest sums](../../../../LeanExe/ProofKit/F64AddNearest.lean), [steps from relative errors](../../../../LeanExe/ProofKit/F64RelativeSteps.lean), [negated operations](../../../../LeanExe/ProofKit/F64NegateOps.lean), [exact products](../../../../LeanExe/ProofKit/F64ExactProduct.lean), [error tracking](../../../../LeanExe/ProofKit/F64ErrorTrack.lean), [the signed rounding reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean), and [the borrowed table frame](../../../../LeanExe/ProofKit/BorrowedKept.lean).  This proof added `F64Horner`, `F64DivApprox`, `F64AddNearest`, `F64RelativeSteps`, and `F64NegateOps`, and `ExpRelative`, which `ExpTightFloat` has since replaced.  `ExpTheorem.borrowed_kept` applies the shared theorem `BorrowedKept.borrowed_kept`.

### Kernel-checked facts

| Fact | Declarations |
|---|---|
| The small kernel's two one-sided weighted bounds on two intervals, the positivity of `qq`, and the series partial sum | `ErfKernelSmall.small_up_1`, `small_up_2`, `small_lo_1`, `small_lo_2`, `qq_check`, `series_check` |
| The middle kernel's bounds on eight intervals of `s` per side | `ErfKernelMiddle.middle_up_1` to `middle_up_8`, `middle_lo_1` to `middle_lo_8` |
| The positivity of `S_a` and `S_b` | `ErfTailCoeffs.sa_check`, `sb_check` |
| For each of the 32 tail pieces, the defect of the model, its range, the derivative checks, and the anchors | `ErfTailPieces0` to `ErfTailPieces7`, four pieces each |
| The rounding conditions of the 74 small, 13 middle, and 30 tail intervals | `ErfSmallPieces0`, `ErfSmallPieces1`, `ErfMiddle.ok0` to `ok12`, `ErfTailErf.tok0` to `tok29` and `tcrit0` to `tcrit29` |
| The exceptional words and the export | `ErfTheorem.erf_pos_zero` to `erf_neg_infinity`, `erf_export` |
| The file's bytes equal the encoder's | `ErfFile.erf_file` |

### The proof of CORE-MATH's `erfc`

The proof of `Erfc.erfc` has two parts: lemmas that bound the fast path `cr_erfc_fast` within `(15/16) u erfc x` for `-95/16 < x ≤ 0x1.713786d9c7c09p+1`, and modules that bound the accurate path, the hard cases, and the remaining ranges and prove `ErfcTheorem.erfc_within_one`.  The paths take `FmaSpec.FmaNearest` as a hypothesis: for finite `a`, `b`, `c` with `|a b + c| ≤ 2^1023`, `Fma.fma a b c` is finite and nearest to `a b + c` among the finite doubles.  `FmaSpecTheorem.fma_nearest` proves this property of the software fused multiply-add, and `erfc_within_one` applies it in place of the hypothesis.  The proof does not use CORE-MATH's error bounds `err`: when the rounding test passes, the result is a nearest double of the fast path's `h + l` (`ErfcTest.test_near`), so each path needs `|h + l - erfc x| ≤ (15/16) u erfc x` for one step through `F64NearestRelative.within_rel_of`, or an absolute error below `2^-1074` for subnormal results.  [The journal](../../../../devnotes.md#2026-10-12-core-maths-erfc-track-trig) records the plan, the measured margins, and the runs.

The rounding analysis follows each float with an ideal real value and bounds on the value and on the error (`ErfcTrack.Tr`), and each double-double with bounds on the error of its sum and on its low part (`ErfcTrack.Pr`).  For a row of a table, a generated structure holds the bound of every stage, a function computes them from the row's coefficients, and one kernel check confirms the conditions of the stages: the dominance of each `fast_two_sum` and the absence of overflow.  Each polynomial of `C` is checked against the series of `erf` at 0, multiplied by a common denominator so that the shift to the row's center runs on integers (`ErfcSeriesI`), cut after degree 8 to 12 with the rest bounded by the sum of its coefficients, and compared with `PolyBound.check`.  `ErfcSeries` encloses `2/√π` in an interval of width `2^-160` from the enclosure of `π` by Machin's formula in `BesselConstants`.  The checks for the 94 rows use 8 to 129 terms of the series and at most one bisection (`ErfcFastPlan`), and a Python model recorded in the journal finds the rounding error of `cr_erf_fast` at most `5·10^-5` of the target.

| Module | Main results |
|---|---|
| `FmaSpec` | `FmaNearest` |
| `ErfcEft`, `ErfcEft2` | `fast_two_sum` and `two_sum`: Dekker's and Knuth's sums are exact |
| `ErfcOps` | the errors of sums, differences, products, `Fma.fma`, `Erfc.fastTwoSum`, `Erfc.twoSum`, and `Erfc.aMul` on Floats |
| `ErfcTrack`, `ErfcTrack2`, `ErfcTrack3` | the stages of `cr_erf_fast`, of its case below `1/16`, and of `cr_erf_accurate` |
| `ErfcRound` | `roundEven_spec`, `floorF_spec`: `Erfc.roundEven` and `Erfc.floorF` give the nearest integer and the integer part; exact products by powers of two |
| `ErfcSeries`, `ErfcSeriesI` | `row_sound`, `row_soundI`: a polynomial within a checked bound of `erf` near a rational center; `erfc_ge` |
| `ErfcFastMain`, `ErfcFastRow` | `core_pr`, `row_err`: `Erfc.erfFastMain` on row `i` of `C` within the row's target of `erf x` |
| `ErfcFastPlan`, `ErfcFastRows0` to `ErfcFastRows11` | the targets of the 94 rows of `C` and their kernel checks: `(7/8) u erfcLo` at the row's top for the rows that positive arguments reach, `(7/8) u` for the others |
| `ErfcFastTiny` | `tiny_err`: `Erfc.erfFastTiny` within `(7/8) u erfcLo (1/16)` of `erf z` for `\|z\| ≤ 1/16` |
| `ErfcTest` | `test_near`, `near_within`: the rounding test gives a nearest float of `h + l`, and a nearest float of `s` with `\|s - y\| ≤ (15/16) u y` lies within one step of `y` |
| `ErfcCast` | `qc`, a tactic that transfers a rational inequality to the reals |
| `ErfcFastAll` | `erfFast_err`: `cr_erf_fast` on `[0, 95/16)` within its row's target of `erf z`, with the low part below `2 u`; `zTarget_abs`, `zTarget_rel` |
| `ErfcFastPath` | `erfcFast_neg`, `erfcFast_pos`: `cr_erfc_fast` within `(15/16) u erfc x` for `-95/16 < x ≤ 0x1.713786d9c7c09p+1`; `fast_within`: one step when the rounding test passes |
| `ErfcAccMain` | `acc_core_pr`: the rounding error of `cr_erf_accurate`'s evaluation of a row of `C2` against the row's polynomial, from one kernel check of the stage bounds |
| `ErfcAccTiny` | `tacc_core_pr`: the rounding error of `cr_erf_accurate` below `1/8` (`Erfc.erfAccurateTiny`) against `z Q (z²)`, for the coefficients of a checked bound structure `TAccHyp` |
| `ErfcSeriesZ` | `rowBoundZ_eq`: the tail bound of `ErfcSeriesI` with the shift of the series in integer arithmetic, which the kernel computes faster |
| `ErfcAccRow`, `ErfcAccPlan`, `ErfcAccRows0` to `ErfcAccRows5` | `acc_row_err`: `cr_erf_accurate` on row `i` of `C2` within the row's target of `erf x`; the kernel checks of the 47 rows |
| `ErfcAccAll` | `erfAcc_err`: `cr_erf_accurate` on `[0, 47/8)` within `aTarget z` of `erf z`, with the low part below `2 u`; `aTarget_abs`, `aTarget_rel` |
| `ErfcTrack4` | `pr_dMul`, `pr_sMul`, `pr_fastSum`, `fts_any`: the double-double products and sums of `exp_1`, `q_1`, and `erfc_asympt_fast` |
| `ErfcExpBits`, `ErfcExpTab`, `ErfcExp1Red`, `ErfcQ1`, `ErfcExp1` | `exp1_err`: `exp_1` within `2^-60 exp (xh + xl)` of `exp (xh + xl)` for `-700 ≤ xh ≤ -8`, with the low part below `2^-30 exp (xh + xl)`; the split of the index into bits, the tables `T1` and `T2` within `2^-95` relative, the reduction, and `q_1` |
| `ErfcRecip`, `ErfcRel`, `ErfcAsymIdx` | `recip_pr`, `usq_pr`: `1/x` and `1/x²` as double-doubles for `3/2 ≤ x ≤ 32`, within `4 u²/x` and `14 u²/x²`; `pr_dMul_rel`: `Erfc.dMul` with bounds relative to the product; `fast_index`, `acc_index`, `dom_lo`, `dom_hi`: the rows of the asymptotic tables that `1/x` selects |
| `ErfcAsymPoly` | `asym_core_pr`: the rounding error of `erfc_asympt_fast`'s evaluation of a row of `T` at the double-double `uh + ul` against the row's polynomial, from one kernel check of the stage bounds |
| `ErfcAsymCert`, `ErfcAsymPlan`, `ErfcAsymRowsT`, `ErfcAsymRowsA0`, `ErfcAsymRowsA1` | `cert_sound`: a polynomial `Z` in `1/x²` within `ρ x erfcx x` of `x erfcx x` on an interval from one `PolyBound.check` against a model of `erfcxN` of `ErfTailPieces0` to `ErfTailPieces7`; `ErfcAsymRowsT.row0` to `row5` and `ErfcAsymRowsA0.row0` to `ErfcAsymRowsA1.row9`: each row of `T` and `Tacc` within `2^-61 x erfcx x` on the interval of `x` that its index allows |
| `ErfcAsymZ`, `ErfcAsymFast` | `G_bounds`: `0.49 ≤ x erfcx x ≤ 0.57` for `x ≥ 2`; `z_row`: the computed polynomial of a row of `T` within `2^-60 x erfcx x` of `x erfcx x`; `asym_fast_err`: `erfc_asympt_fast` within `2^-57 erfc x` of `erfc x` for `0x1.713786d9c7c09p+1 < x < 0x1.9db1bb14e15cap+4`, with both parts at most 1 |
| `ErfcTrack5`, `ErfcTaccLoop`, `ErfcTaccData` | `pr_tStep`, `pr_tStepB`, `loopA`, `loopB`: the stages and the two loops of the polynomial of `erfc_asympt_accurate`, with the bounds of the states of the ten rows of `Tacc` that the kernel checks step by step |
| `ErfcEAccPoly`, `ErfcEAcc` | `eacc_core_pr`, `expAcc_err`: `exp_accurate` for `-742 ≤ xh ≤ -2` within `2^-76 exp (xh + xl - K log 2)`, with the exact reduction `yh = fma (-K, log2h, xh)` |
| `ErfcAsymAccHL`, `ErfcAsymAccFin` | `aa_hl`: `erfc_asympt_accurate` before its final scaling within `2^-56 erfc x`; `finA_within`: the scaling `ldexp`, with the correction of a subnormal result, within one step |
| `ErfcHardBase`, `ErfcHardRows`, `ErfcHardAsym0`, `ErfcHardAsym1`, `ErfcHardAsym`, `ErfcHardNeg`, `ErfcHardPos` | `hard_within`, `ser_row`, `asym_row`, `table`: each of the 68 hard cases returns a fixed word within one step, from a rational enclosure of `erfc` at its input by the series of `erf` or by a model of `erfcxN` and ten squarings of `exp (-x²/1024)` |
| `ErfcSpecial` | `special_within`: the input `0x1.a8f7bfbd15495p+4`, whose `erfc` lies in the subnormal range, within one step |
| `ErfcAccPath` | `acc_within`: `cr_erfc_accurate` within one step for `-47/8 < x < 0x1.b39dc41e48bfdp+4`, `x ≠ 0` |
| `ErfcMainPath` | `main_within`: the main path within one step, the fast path when its rounding test passes and the accurate path otherwise |
| `ErfcTheorem` | `erfc_within_one`: one step for `Erfc.erfc x` at every finite `x`, through the ranges that return constants or `fma (-x, 2^-54, 1)` and the main path |
| `ErfcBytes` | `erfc_bytes_accuracy`: the compiled module's export `erfc` returns `(Erfc.erfc x).toBits` from every ready store and leaves a ready store, with the bound of `erfc_within_one` |

The axiom reports of these modules list only `propext`, `Classical.choice`, and `Quot.sound`, and `FmaSpec` and `ErfcFastPlan` contain definitions only.  `erfc_within_one` and the four theorems of `ErfcBytes` report the same three axioms.  [The journal](../../../../devnotes.md#2026-10-14-the-accuracy-theorem-of-the-port-of-core-maths-erfc-track-trig) records the repairs of the first build of the 18 modules from `ErfcTrack5` to `ErfcTheorem`.

### History

Below about 8 the asymptotic series of `erfc` is too inaccurate and the power series loses the result to cancellation, which is why the tail kernels rest on polynomial models of `erfcx` checked against its differential equation instead of on either series.  The `decide` tactic did not reduce on `Rat`, so every check uses `decide +kernel`, and the middle checks, of degree 57 with numbers of about 930 bits, are split into eight declarations per side of about 10 seconds each.  [The journal](../../../../devnotes.md#2026-10-12-integration-of-expm1-tanh-erf-log1p-atan-atan2-asin-and-acos-first-push) records the integration of this proof with the ports of `expm1`, `tanh`, `log1p`, `atan`, `atan2`, `asin`, and `acos`.

For `erfc` an estimate of the reachable bound preceded any theorem.  The same analysis as `erf`'s tail gives about `10.2 u` near 1.25, ten steps.  Charging each Horner step with the magnitude of its partial result on 400 intervals and taking `1.04 u` for each exponential, the relative error that corresponds to Arm's stated 0.52 units, lowers it to `7.54 u`, seven steps through the nearest rounding of the final quotient.  The four rounded operations after the arguments of the exponentials, the two exponentials, their product, and the quotient, cost about `4.1 u` alone, and the middle range reaches `3.97` spacings before its final rounding near 1.25, so the decided four steps were out of reach for a worst-case proof, which led to the decision for CORE-MATH's `erfc`.

## Tests

[The accuracy check](../../../../tests/TestSupport/Numerics/ErfAccuracy.lean) compares `Erf.erf` natively with the doubles nearest to the values of [the integer reference](../../../../tests/TestSupport/Numerics/ErfReference.lean), and it fails at the first result further than one step.  Until 2026-10-15 it also checked fdlibm's `erfc` within four steps.  Below 6 the reference computes `erf x = (2/√π) x exp (-x²) Σ (2x²)^n/(1 · 3 ⋯ (2n+1))`, the series of positive terms of DLMF 7.6.2 [4], with 64 guard bits, and `erfc = 1 - erf`.  From 6 on it computes `√π exp (x²) erfc x` from Laplace's continued fraction `1/(x + (1/2)/(x + 1/(x + (3/2)/(x + ⋯))))`, in exact integer arithmetic, stopping when two successive convergents, which lie on alternate sides of the value, agree within a relative `2^-(q+2)`.  An equivalence transformation takes this fraction to the form of DLMF 7.9.1 [4], and the journal records that Python models of the references agreed with 260-digit decimal computations of `erf` and `erfc` at 750 arguments and that the continued fraction reproduced the C library's `erfc` at 2, 3, and 6.

The 222,136 arguments are 100,001 evenly spaced values from -7 to 7, 20,001 from 6 to 28, 100,000 hashed values with exponents from `2^-60` to `2^6` and both signs, the five doubles at and around each of the ten thresholds with both signs, 2,001 values from 27.2 to 27.3, where `erfc` falls from the smallest subnormals to zero, 14 special values, and the 19 inputs of `WorstCases.erf` and `WorstCases.erfc`.  Those 19 are the double-precision inputs with the largest known errors of `erf` and `erfc` in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [9], whose Table 3 lists 1.02 units for FreeBSD 15.1's `erf` and 4.08 for its `erfc`.  Each of the 19 inputs enters the checks of both functions.

In a run of `tests/verified/run.sh` from before 2026-10-15, all 222,136 results of `erf` lie within one step of the reference, and 8,947 of them differ from it, so the largest measured distance equals the proved bound.  In that run all 222,136 results of fdlibm's `erfc` lay within four steps, 28,338 differed from the reference, and the four-step result is at `0x1.527f4fb0d9331p+0`, the input of Musl's largest `erfc` error in Table 7 of the report.  A Python model of the port found another result three steps away at `0x1.5ea52c08eb7ccp+0`, which the check does not contain ([the review of the worst inputs](../../../../devnotes.md#2026-10-11-zimmermanns-inputs-in-the-accuracy-checks)), so the fdlibm `erfc` met its four steps with no margin at the known inputs.  Lean has no binding of the C library's `erf` and `erfc`, so the check reports no library distance, and the truncation errors that the reference's docstrings state are not proved.

[The check of the CORE-MATH port](../../../../tests/TestSupport/Numerics/ErfcAccuracy.lean) compares `Erfc.erfc` with the same reference, rounded to the nearest double, and requires equality.  Its 223,592 arguments are those of the fdlibm check without the inputs of `WorstCases.erf`, and with the doubles next to the thresholds of CORE-MATH's code in place of fdlibm's: the five doubles at and around each of the 10 bounds of the special ranges and of the paths, the 96 multiples of `1/16` from `1/16` to 6, which end the intervals of the polynomials of `erf`, and the reciprocals of the 16 bounds of the intervals of `1/x`, with both signs, and the five doubles at and around each of the 69 inputs of the hard cases.  It also calls `Erfc.erfcAccurate`, the accurate path, at every eighth argument in its range and at the 69 hard-case inputs, 24,895 calls.  In a run of the check, every one of the 223,592 results and of the 24,895 results of the accurate path equals the reference.

## Limits

The theorem is about Talos's semantics of WebAssembly, with the Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode` trusted, as [the design notes](../../../../docs/design.md#scope-of-the-theorem) record and the exponential's document describes.  The file theorem trusts the elaborator `binary_file%`.  Talos implements the deterministic profile, in which every NaN result is canonical [7], and an engine outside that profile, such as a browser, may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, so the theorem covers only the canonical NaN among the NaN words a WebAssembly caller can pass, although for another NaN word the compiled code reaches `±1 + 1/x`, which gives the canonical NaN in Talos.  `erf_bytes_accuracy` covers sequences of calls to `erf` only.  The module also exports `erfWith`, the rational functions, the exponential's functions, its memory, and the allocator's globals, and a host that calls another export or writes the table between calls to `erf` needs a theorem that the action preserves `Ready`.

`ErfcBytes.erfc_bytes_accuracy`, for the port of CORE-MATH's `erfc`, has the same limits and covers sequences of calls to that module's `erfc` export only.  The results of `erf` can differ in the last bit from FreeBSD's, because the port calls Arm's exponential, and the theorem bounds `erf` against the real function, so FreeBSD's results play no part in it.  The tail kernels rest on the chain of 32 models from the asymptotic enclosure at 28, which is proved, and the source's stated kernel errors play no part in the proof.

## References

1. FreeBSD, [`lib/msun/src/s_erf.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_erf.c).  Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with the notice preserved.
2. FreeBSD, [`lib/msun/src/e_exp.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_exp.c), same commit: fdlibm's exponential, with its stated error below one unit in the last place.
3. Arm Limited, optimized-routines, [`math/exp.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/exp.c), which [the exponential's document](../Exp/README.md) describes.
4. F. W. J. Olver et al., eds., *NIST Digital Library of Mathematical Functions*, chapter 7: [§7.2](https://dlmf.nist.gov/7.2) (definitions 7.2.1 and 7.2.2), [§7.4](https://dlmf.nist.gov/7.4) (symmetry, 7.4.1 and 7.4.2), [§7.6](https://dlmf.nist.gov/7.6) (power series 7.6.1 and 7.6.2), [§7.9](https://dlmf.nist.gov/7.9) (continued fraction 7.9.1), and [§7.12](https://dlmf.nist.gov/7.12) (asymptotic expansion 7.12.1 and the sign of its remainder for real arguments).
5. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): Table 9.1 of clause 9.2 lists the recommended operations, and the error functions are not among them.
6. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.5.1, and F.9.5.2, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
7. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
8. The Mathlib Community, Mathlib: [`Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean) (`integral_gaussian_Ioi`) and [`Mathlib/Analysis/Real/Pi/Bounds.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/Real/Pi/Bounds.lean) (`pi_gt_d20`, `pi_lt_d20`).
9. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
10. The CORE-MATH project, [`src/binary64/erfc/erfc.c`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/src/binary64/erfc/erfc.c): "Correctly-rounded complementary error function for the binary64 format", Copyright (c) 2022-2026 Alexei Sibidanov, Paul Zimmermann, Tom Hubrecht and Claude-Pierre Jeannerod, MIT license.  The [project page](https://core-math.gitlabpages.inria.fr/) describes the project.
