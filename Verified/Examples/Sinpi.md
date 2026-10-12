# The sine, cosine, and tangent of π x

[The implementation](Sinpi.lean) exports `sinpi`, `cospi`, and `tanpi`, ports of Steven G. Kargl's `sinpi`, `cospi`, and `tanpi` as FreeBSD's msun has them [1, 2, 3, 4], which call fdlibm's kernels of [the sine and cosine](Trig.md) and [the tangent](Tan.md).  The decided bound is one representable step from the nearest-even rounding of the real function, `F64SignedRounding.WithinSteps 1`, with exact equalities for the signed zeros and infinities that IEEE 754-2019 specifies.  No accuracy theorem exists in this checkout: the compiler's generated theorems state that the module computes the Lean definitions, and a native check samples the accuracy.  The proof is assigned to track `trig`, which finished `tan` first, and its open obligations are listed under the proof below.

## Specification

`sinpi x`, `cospi x`, and `tanpi x` are `sin (π x)`, `cos (π x)`, and `tan (π x)` for the value `x` of the argument, the functions that IEEE 754-2019 names `sinPi`, `cosPi`, and `tanPi` [5] and C23 names `sinpi`, `cospi`, and `tanpi` [6].  Every finite double is in the domain of `sinpi` and `cospi`.  `tanpi` has poles at `n + 1/2` for integers `n`, where the result is an infinity by rule, and Mathlib's `Real.tan`, which is 0 where the cosine vanishes, cannot state it, so a theorem must treat those inputs as exceptional.  `WithinSteps` places both zeros at position 0, so the sign of a zero result also needs an equality of its own, as the ports track recommended ([the stage 6 ports](../../devnotes.md#2026-10-10-ports-of-sinpi-cospi-tanpi-erf-and-erfc)).

| Input | Result | Source of the rule |
|---|---|---|
| `sinpi (±0)`, `tanpi (±0)` | `±0` | IEEE 754-2019 9.2.1; C23 F.10.1.13 and F.10.1.14 |
| `sinpi (±n)`, positive integer `n` | `±0` | IEEE 754-2019 9.2.1; C23 F.10.1.13 |
| `cospi (±0)` | `1` | IEEE 754-2019 9.2.1; C23 F.10.1.12 |
| `cospi (n + 1/2)`, integer `n` | `+0` | IEEE 754-2019 9.2.1; C23 F.10.1.12 |
| `tanpi n`, integer `n ≠ 0` | `+0` for positive even and negative odd `n`, `-0` for positive odd and negative even `n` | IEEE 754-2019 9.2.1; C23 F.10.1.14 |
| `tanpi (n + 1/2)`, integer `n` | `+∞` for even `n`, `-∞` for odd `n` | IEEE 754-2019 9.2.1 (with the divideByZero exception); C23 F.10.1.14 |
| `±∞` | NaN, the canonical NaN in the deterministic profile [7] | IEEE 754-2019 Table 9.1 (outside the domain); C23 F.10.1.12 to F.10.1.14 |
| NaN | the canonical NaN | IEEE 754-2019 9.2; C23 F.10 paragraph 14 |

The sources state the same rules in their comments [1, 2, 3].  `s_tanpi.c` also lists `tanpi (±n + 1/4) = ±1` for positive integers `n`, which IEEE 754-2019 and C23 do not list, and the kernel returns 1 exactly at `1/4`.  From `2^52` on every double is an integer, so `sinpi` and `tanpi` return signed zeros there and `cospi` returns `±1` by parity, and from `2^53` on every double is even, so `cospi` returns 1.  IEEE 754-2019 asks for correct rounding of these operations in clause 9.2, Kargl states no error bound, and the one-step bound is weaker than correct rounding.

## Algorithm

Kargl's method avoids multiplying the argument by `π` until it has been reduced to `[0, 1/4]` [1].  For `|x| < 1` the functions reflect `|x|` with `sin (π x) = cos (π (1/2 - x))` and the similar identities: `sinpi` uses the sine kernel on `[0, 1/4)`, the cosine kernel at `1/2 - x` on `[1/4, 1/2)` and at `x - 1/2` on `[1/2, 3/4)`, and the sine kernel at `1 - x` on `[3/4, 1)`, and `cospi` and `tanpi` follow the same pattern.  The differences `1/2 - x`, `x - 1/2`, and `1 - x` are exact by Sterbenz's lemma ([ProofKit's statement](../../LeanExe/ProofKit/F64Sterbenz.lean)), since `x` lies within a factor of 2 of the constant on each interval.  For `1 ≤ |x| < 2^52` the functions subtract the integer part `j0` of `|x|`, which is exact, and use `sin (π (j0 + r)) = (-1)^j0 sin (π r)`, the same for `cos`, and `tan (π (j0 + r)) = tan (π r)` [1, 2, 3].

The kernels form `π r` as `hi + lo` for `r` in `[0, 1/4]` [4].  `hi = (float) r` rounds `r` to 24 bits, `lo = r - hi` is exact, `π` is the sum of `pi_hi`, which has 26 significant bits, and `pi_lo`, and `hi · pi_hi` is exact, since its product has at most 50 bits.  The tail `lo · (pi_lo + pi_hi) + hi · pi_lo` and a Fast2Sum (`_2sumF`) give `hi + lo` with `|lo|` below half a unit of `hi`, which `__kernel_sin`, `__kernel_cos`, or `__kernel_tan` takes as its argument and tail.  `pi_hi + pi_lo` lies within `2^-79.4` of `π`, by this document's comparison with a 600-bit `π`, which agrees with `s_tanpi.c`'s description of "an 80-bit approximation of pi" [3].

Below `2^-29` in magnitude, `sinpi x` and `tanpi x` are `π x`, computed from `x` scaled by `2^53` and split at its high 32 bits, so that subnormal inputs lose no bits, and scaled back by `2^-53` [1, 3].  `cospi` returns 1 there.  `tanpi` above `1/4` uses `tan (π r) = 1/tan (π (1/2 - r))`, through the kernel's `-1/tan` form, and returns 1 at `1/4` exactly.

## Implementation

The sources are `s_sinpi.c`, `s_cospi.c`, `s_tanpi.c`, `k_sinpi.h`, and `k_cospi.h` at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1, 2, 3, 4], each "Copyright (c) 2017, 2023 Steven G. Kargl" under the BSD-2-Clause license, whose conditions require that redistributions of source code retain the notice, the conditions, and the disclaimer, and that redistributions in binary form reproduce them in the documentation or other materials provided with the distribution.  The kernels they call are fdlibm's, under Sun's notice, which [the sine and cosine document](Trig.md#implementation) quotes.  The module docstring of [the implementation](Sinpi.lean) cites the files and the license.  The port is written in the Verified dialect, the subset of Lean that [the Verified compiler](../README.md) translates to WebAssembly with a correctness theorem.

`verified_compile compiled := [Trig.kernelSin, Trig.kernelCos, Tan.kernelTan, toSingle, piProduct, kernelSinpi, kernelCospi, kernelTanpi, piTiny, ffloor, oddPart, sinpi, cospi, tanpi]` generates the module, so the reflector compiles the Lean definitions of the three fdlibm kernels again into it.  Its functions are `alloc` (0), `release` (1), the listed definitions from 2 on, `sinpi` (13), `cospi` (14), and `tanpi` (15).  The module has no tables.

| C code | Port | Reason |
|---|---|---|
| `hi = (float) x` | `toSingle x`, which rounds the 52-bit fraction to 23 bits, ties to even, with any carry into the exponent field | The dialect has no single precision.  `toSingle` is `(float) x` for zero and for every double whose single-precision value is normal, which covers every kernel argument, 0 or from `2^-54` to `1/2`. |
| `FFLOOR (x, j0, ix, lx)` | `ffloor ix lx` on 64-bit words with 32-bit masks | The macro of `math_private.h` [8] on words. |
| `if (j0 > 30) x -= 0x1p30; j0 = (uint32_t) x; if (j0 & 1)` in `sinpi` and `cospi` | `oddPart`: the same subtraction, then the parity from `toUInt64` | C leaves the conversion to `uint32_t` undefined above `2^32`.  The parity of the integer is what the code intends, and `s_tanpi.c` takes it from `(uint64_t) x & 1`. |
| `__kernel_sinpi`, `__kernel_cospi`, `__kernel_tanpi` | `kernelSinpi`, `kernelCospi`, `kernelTanpi`, sharing `piProduct` | The three kernels start with the same computation of `π x` as `hi + lo`. |
| `_2sumF (hi, lo)` | `w = hi + lo` and `(hi - w) + lo` | The macro's definition without `DEBUG` [8]. |
| `π x` below `2^-29` | `piTiny x hx` | The shared computation of `s_sinpi.c` and `s_tanpi.c`. |
| `vzero / vzero`, `1 / vzero`, `odd / vzero` | `0.0 / 0.0`, `1.0 / 0.0`, `odd / 0.0` | `vzero` is a volatile zero that prevents constant folding, and the dialect has no such qualifier. |
| `(int) ax == 0` in `cospi` | `ax.toUInt64 == 0` | Both truncations give 0 wherever the test runs. |
| `copysign (0, x)` | `if neg then -0.0 else 0.0` | `neg` is the sign bit of `x`. |

| Constant | Bits | Value |
|---|---|---|
| `pi_hi` | `0x400921FB58000000` | `3.1415926814079285`, 26 significant bits |
| `pi_lo` | `0xBE5DDE973DCB3B3A` | `-2.7818135228334233e-08` |
| `0x1p53`, `0x1p-53` | `0x4340000000000000`, `0x3CA0000000000000` | the scale factors of the tiny path |

For this document a script compared the two words of `π` with the three source files, which print them beside their decimal values, and both agree, and each decimal value rounds to its word.  The ports track compared `toSingle` with C's conversion, through Python's `struct` module, at 200,000 random doubles from `2^-60` to 1 and 500,000 doubles at and next to the rounding ties, and found no difference.  This document repeated the comparison at 300,000 random doubles from `2^-54` to 1 and 600,000 at and next to ties from `2^-54` to `1/2`, and also found none.

## Theorems

No theorem about the accuracy or the exceptional values of `sinpi`, `cospi`, or `tanpi` exists in this checkout, and no module `SinpiTheorem`, `SinpiBytes`, or `SinpiFile`.  The `verified_compile` command generates, as for every module, the theorems that the bytes of `Sinpi.compiled.module` decode to the module, that the module starts in a store satisfying the runtime invariant, and that each exported function computes its Lean definition without a trap.  These theorems say nothing about how well the definitions approximate `sin (π x)`, `cos (π x)`, and `tan (π x)`.  `tests/verified/run.sh` writes `build/verified/sinpi.wasm`, validates it with `wasm-tools`, and runs the accuracy check, and it has no file-theorem entry for the module.

## Proof

The remaining work belongs to track `trig`: [the transcendental plan](../../transcendentals.md#functions) lists the three functions as "Assigned to track `trig` after `tan`", and the last checklist of [the tangent section](../../devnotes.md#2026-10-11-the-tan-theorem-track-trig) leaves "`Sinpi.sinpi`, `cospi`, and `tanpi`" open.  Much of the floating-point analysis exists.  `TrigKernelSpec.sinTail_spec` and `TrigCosKernel.cos_spec` bound the sine and cosine kernels for an argument `y0 + y1` with `2^-70 ≤ |y0| ≤ 0.78541` and `|y1| ≤ |y0|/2^52`, `TrigStep.sin_final` and `cos_final` turn those bounds into one step against any real `r` within `|r|/2^59` of `y0 + y1`, and `TanWith.kernel_within` does the same for the tangent kernel.  `TrigTiny.self_step` and the signed reference of `F64SignedRounding` apply unchanged.

The open obligations are specific to the `π x` functions.  None of them has a module in this checkout, and the journal records no plan beyond the open checklist item.  The table lists them as this document reads the code, so its division may differ from the track's.

| Obligation | Content |
|---|---|
| `toSingle` | The result is `x` rounded to 24 bits for every kernel argument, and `x - toSingle x` is exact. |
| `piProduct` | `hi · pi_hi` is exact, the tail's two roundings are small, the Fast2Sum is exact, and `hi + lo` lies within `\|π r\|/2^59` of `π r` with `\|lo\| ≤ \|hi\|/2^52`, using `\|pi_hi + pi_lo - π\| < 2^-79` from a bound on `π`. |
| Reflections | `1/2 - x`, `x - 1/2`, and `1 - x` are exact by Sterbenz's lemma, and the identities between `sin (π x)` and `cos (π (1/2 - x))` and between `tan (π x)` and `1/tan (π (1/2 - x))` hold. |
| Integer part | `ffloor` gives the integer part of `\|x\|` for `1 ≤ \|x\| < 2^52`, the subtraction is exact, and `oddPart` and the parity of `tanpi` give its parity. |
| Tiny path | `piTiny` lies within one step of `π x` for `0 < \|x\| < 2^-29`, subnormal inputs and results included. |
| Exceptional values | The signed zeros at integers, `cospi (n + 1/2) = +0`, the infinities of `tanpi` at `n + 1/2`, `tanpi (n + 1/4) = ±1`, the values from `2^52` on, and NaN for infinities and NaN, as equalities of bits. |
| Composition | `WithinSteps 1` against `Real.sin (π a)`, `Real.cos (π a)`, and `Real.tan (π a)` away from the exceptional inputs, a byte theorem in the form of `exp_bytes_accuracy` without tables, a file module, and an entry in `tests/verified/run.sh`. |

The kernels receive arguments up to `π/4` in magnitude, inside the range `0.78541` on which the existing kernel bounds hold.  The cosine kernel's `(7/5) u` and the sine kernel's bound leave margins of 4 to 17 percent in [the sine and cosine proof](Trig.md#error-budget), and `piProduct` adds an error of a relative size near `2^-79` and the roundings of its tail, which the proof must place inside those margins.  The tiny path of `sinpi` and `tanpi` and the exceptional values need arguments of their own, since no existing lemma covers them.

## Tests

[The accuracy check](SinpiAccuracy.lean) compares the three functions natively with references from `Reference.sinCosTurns` at `|x|/2` turns, with 64 bits above the precision of `x`, rounded to the nearest double, and it requires each result within one step and, where the reference is a zero or an infinity, its exact bits.  The references take the zeros, poles, and signs from the rules in the table above rather than from the series.  Its 204,631 arguments are 100,001 evenly spaced values from -4 to 4, the five doubles at and around each multiple of `1/4` from -100 to 100, the five doubles at and around `±(2^k + 1/2)` for `k` from 0 to 51, 100,000 hashed values from `2^-60` to below `2^60` with both signs, the five doubles at and around the seven thresholds of the code with both signs, 13 special values, and the 22 inputs of `WorstCases.sinpi`, `cospi`, and `tanpi`.  Those 22 are the double-precision inputs that give the largest known errors of these functions in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [9], whose Table 3 lists 0.812, 0.812, and 0.969 units for FreeBSD 15.1 and 1.86, 1.86, and 2.85 for GNU libc 2.44.

In `opus-verified-tests-13.log` the 204,631 results of each function lie within one step of the reference with the signs of the zeros and infinities, and 4,641 of `sinpi`, 4,596 of `cospi`, and 5,185 of `tanpi` differ from it.  Lean has no binding of these functions, so the check reports no library distance.  The ports track's Python models of the ports also lay within one step at FreeBSD's worst inputs, and Python models of the references agreed with 260-digit decimal computations at 1,353 arguments.  These samples support the decided bound but do not prove it.

## Limits

Nothing about the accuracy of the three functions is proved, so the module's results rest on the sampled check alone.  When a theorem exists, the limits of [the sine and cosine theorems](Trig.md#limits) will apply: Talos, `Module.initialStore`, the decoder, and `binary_file%` are trusted, the argument is a Lean `Float`, which has only the canonical NaN, and a byte theorem covers sequences of calls to its exports.  The port's `toSingle` is `(float) x` only where the single-precision value is normal, which covers every argument the code passes to it but not every double.

## References

1. Steven G. Kargl, FreeBSD msun, [`lib/msun/src/s_sinpi.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_sinpi.c), commit `20381bce4b63975494a2f4bc84257f6932e6d379`.  Copyright (c) 2017, 2023 Steven G. Kargl, BSD-2-Clause.  The comment describes the method and the special cases.
2. Steven G. Kargl, FreeBSD msun, [`s_cospi.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_cospi.c), same commit and license.
3. Steven G. Kargl, FreeBSD msun, [`s_tanpi.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_tanpi.c), same commit and license, with its kernel `__kernel_tanpi`.
4. Steven G. Kargl, FreeBSD msun, [`k_sinpi.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_sinpi.h) and [`k_cospi.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_cospi.h), same commit and license.
5. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229).  Clause 9.2 with Table 9.1 (domains and exceptions of `sinPi`, `cosPi`, and `tanPi`) and clause 9.2.1 (their special values) were read.
6. ISO/IEC 9899:2024, *Programming languages — C* (C23), clauses 7.12.4.12 to 7.12.4.14 and Annex F, clauses F.10.1.12 to F.10.1.14, as in WG14 working draft [N3220](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3220.pdf) (February 2024).  The published standard was not consulted.
7. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
8. FreeBSD, msun, [`math_private.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/math_private.h), same commit: `FFLOOR` and `_2sumF`.
9. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
