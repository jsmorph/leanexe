# The inverse hyperbolic functions

[The implementation](Asinh.lean) exports `asinh`, `acosh`, and `atanh`, ports of fdlibm's `s_asinh.c`, `e_acosh.c`, and `e_atanh.c` as FreeBSD's msun has them at commit `20381bce` [1, 2, 3].  Each writes its function as a logarithm of an algebraic expression and evaluates it with [the logarithm](Log.lean), [the logarithm of one plus its argument](Log1p.lean), and the square root, in a form chosen for each range.  The decided bound is two steps for each function, and on 2026-10-12 the coordinator allowed three steps for `asinh` and `acosh` on a subrange if their compositions with `log1p` cannot be closed.  This checkout, at commit `77ce56f4`, holds the port and its accuracy check but no theorem about the accuracy of these functions: [the plan](../../transcendentals.md#functions) records the large and middle ranges as proved and the branches through `log1p` as in progress on the track `arc`.

## Specification

`asinh` computes `Real.arsinh a`, `acosh` computes `log (a + √(a² - 1))`, and `atanh` computes `(1/2) log ((1 + a)/(1 - a))`, where `a` is the value of the argument.  The domains are every finite double for `asinh`, `[1, ∞)` for `acosh`, and `(-1, 1)` for `atanh`.  The bounds are to be stated as `F64SignedRounding.WithinSteps 2`, defined in [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean).  None of the three overflows on a finite input inside its domain, since `asinh` and `acosh` of the largest double are about 710.48.

| Input | Port's result | Source of the rule |
|---|---|---|
| `asinh (±0)`, `asinh (±∞)` | the argument, by `x` below `2^-28` and `x + x` | IEEE 754-2019 9.2.1 [4]; C99 F.9.2.2 [5] |
| `acosh 1` | `+0` | IEEE 754-2019 9.2.1; C99 F.9.2.1 |
| `acosh x` for `x < 1`, `±0` and `-∞` included | NaN, by `(x - x)/(x - x)` | IEEE 754-2019 Table 9.1 (domain `[+1, +∞]`, invalid operation below 1); C99 F.9.2.1 |
| `acosh (+∞)` | `+∞`, by `x + x` | IEEE 754-2019 9.2.1; C99 F.9.2.1 |
| `atanh (±0)` | the argument | IEEE 754-2019 9.2.1; C99 F.9.2.3 |
| `atanh (±1)` | `±∞`, by `x/0` | IEEE 754-2019 9.2.1 (with the divideByZero exception); C99 F.9.2.3 |
| `atanh x` for `\|x\| > 1` and `±∞` | NaN, by `(x - x)/(x - x)` | IEEE 754-2019 Table 9.1; C99 F.9.2.3 |
| NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [6] |

No theorem in this checkout states any of these results.  IEEE 754-2019 lists the three functions among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [4].  fdlibm states no error bound for any of them [1, 2, 3].

## Algorithm

`asinh` and `atanh` reduce to `|x|` by oddness, and all three rewrite the logarithm's argument by the identities below, which fdlibm's comments state as formulas [1, 2, 3].  The identities are `|x| + √(x² + 1) - 1 = |x| + x²/(1 + √(1 + x²))`, `|x| + √(x² + 1) = 2|x| + 1/(√(x² + 1) + |x|)`, `x + √(x² - 1) - 1 = t + √(2t + t²)` with `t = x - 1`, `x + √(x² - 1) = 2x - 1/(x + √(x² - 1))`, and `(1 + x)/(1 - x) - 1 = 2x/(1 - x) = 2x + 2x²/(1 - x)`.  Above `2^28` the square root differs from `|x|` by less than `2^-57 |x|`, and the code returns `log |x| + ln 2`.

| Function | Range of `\|x\|` | Form |
|---|---|---|
| `asinh` | below `2^-28` | `x` |
| `asinh` | `2^-28` to 2 | `±log1p (\|x\| + x²/(1 + √(1 + x²)))` |
| `asinh` | 2 to `2^28` | `±log (2\|x\| + 1/(√(x² + 1) + \|x\|))` |
| `asinh` | above `2^28` | `±(log \|x\| + ln 2)` |
| `acosh` | 1 to 2 | `log1p (t + √(2t + t²))`, `t = x - 1` |
| `acosh` | 2 to `2^28` | `log (2x - 1/(x + √(x² - 1)))` |
| `acosh` | from `2^28` | `log x + ln 2` |
| `atanh` | below `2^-28` | `x` |
| `atanh` | `2^-28` to `1/2` | `±(1/2) log1p (2\|x\| + 2\|x\| · \|x\|/(1 - \|x\|))` |
| `atanh` | `1/2` to 1 | `±(1/2) log1p (2\|x\|/(1 - \|x\|))` |

## Implementation

The sources are FreeBSD's `lib/msun/src/s_asinh.c`, `e_acosh.c`, and `e_atanh.c` at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1, 2, 3].  Each carries the notice "Copyright (C) 1993 by Sun Microsystems, Inc.  All rights reserved.  Developed at SunPro (`s_asinh.c`) or SunSoft (the others), a Sun Microsystems, Inc. business.  Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved."  The module docstring of [the implementation](Asinh.lean) names the copyright and summarizes the permission as "freely distributable with this notice", without the notice's full text.

The port is written in the Verified dialect, which [the Verified compiler](../README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [Log.logNear1, Log.logCore, Log.logWith, Log1p.log1pTail, Log1p.log1p, asinhWith, acoshWith, atanh, asinh, acosh]` lists the definitions of the earlier ports first, so that the module contains them.  `asinhWith` and `acoshWith` take the logarithm's two tables, `asinh` and `acosh` pass `Log.logTable` and `Log.logTable2`, and `atanh` needs none.

| fdlibm calls | Port calls | Same function |
|---|---|---|
| `log` (`e_log.c`) | `Log.logWith Log.logTable Log.logTable2`, Arm's `log` | No.  fdlibm's comment bounds its `log` below one unit in the last place [8], Arm's comments give `0.5 + 2.06/N` units plus small terms, about 0.52 with `N = 128`, and 0.507 near 1 [9], and their results can differ in the last bit. |
| `log1p` (`s_log1p.c`) | `Log1p.log1p` | Yes |
| `sqrt` | `Float.sqrt`, compiled to `f64.sqrt` | Yes: IEEE 754-2019 requires the square root of clause 5.4.1 to be rounded from its exact value, as clause 5.1 requires of every arithmetic operation [4]. |

| C code | Port | Reason |
|---|---|---|
| `if (huge + x > one) return x` and `(huge + x) > zero` | the tests kept | The expressions raise the inexact flag in C, and the tests hold for every `\|x\| < 2^-28`. |
| `x/zero` with `zero = 0.0` | `x / 0.0` | Same value. |
| signed `int32_t hx` | the word `x.toBits >>> 32`, with `hx >>> 31 == 1` for a negative sign | The dialect has unsigned words only.  `acosh` tests `hx >>> 31 == 1 \|\| hx < 0x3ff00000` for C's signed `hx < 0x3ff00000`. |
| `if (hx > 0) return w; else return -w;` in `asinh` | `if hx >>> 31 == 0 then w else -w` | The two differ only for a positive `x` whose high word is 0, which returns earlier as tiny. |
| `(lx \| (-lx)) >> 31` on `u_int32_t` in `atanh` | `(lx \|\|\| ((0 - lx) &&& 0xFFFFFFFF)) >>> 31` | The negation is taken modulo `2^32`, as in C. |
| `SET_HIGH_WORD (x, ix)` in `atanh` | `Float.ofBits ((ix <<< 32) \|\|\| lx)` | The word of `\|x\|`. |
| `fabs` | `Float.abs`, compiled to `f64.abs` | |
| floating-point flags, `errno` | none | WebAssembly has no floating-point status flags. |

For this document a script compared the port's constants with the C sources at the pinned commit: `ln2 = 6.93147180559945286227e-01` has the bits `0x3FE62E42FEFA39EF` given in both sources, `huge` is `1.0e+300` with the bits `0x7E37E43C8800759C`, and `one` is the literal `1.0`.  Every high word that the C code compares with appears in the port: `0x3e300000` (`2^-28`), `0x41b00000` (`2^28`), `0x40000000` (2), `0x3ff00000` (1), and `0x3fe00000` (`1/2`).  The ports track records the same audit ([its journal section](../../devnotes.md#2026-10-10-ports-of-sinh-cosh-asinh-acosh-and-atanh)).

## Theorems

This checkout has no theorem about the accuracy or the exceptional values of `Asinh.asinh`, `Asinh.acosh`, or `Asinh.atanh`.  `verified_compile` generates `Asinh.compiled` with its `bytes`, `initial`, and `implements` theorems, which state that the compiled module computes the Lean definitions, as [the compiler's documentation](../README.md#running-it) describes.  No byte theorem with a numerical bound and no file theorem exist for `asinh.wasm`, and `tests/verified/run.sh` writes and validates the module and runs the accuracy check only.

The coordinator assigned the three theorems to the track `arc` after `log1p`, `atan`, `atan2`, `asin`, and `acos`, at two steps each through `Log.logWith` and `Log1p.log1p`, and the last item of that track's journal section, "`asinh`, `acosh`, `atanh`", is unchecked ([its journal section](../../devnotes.md#2026-10-10-full-theorems-for-atan-and-log1p-track-arc)).  [The plan](../../transcendentals.md#functions) records the large and middle ranges as proved and the `log1p` branches as in progress, without naming theorems.  No module of that work is in this checkout, and no log in the primary checkout's `build/transcendentals/` names one.

## Proof

This checkout holds no proof module for these functions.  The proved results they can build on are `LogTheorem.log_within_one` and `Log1pTheorem.log1p_within_one`, one step each against `Real.log`, and the relative error of the rounded square root, which [the square-root bounds](../../LeanExe/ProofKit/F64SqrtBounds.lean) state.  A step bound on `log (y)` or `log1p (y)` at a computed `y` does not give a bound on the function by itself, since the error of `y` passes into the result: a relative error `δ` of `y` moves `log1p y` by `δ y/(1 + y)`, which is at most `δ log1p (y)` relative when `y > 0`, and moves `log y` by `δ` absolute.

The branches through `log1p` are the ones the plan lists as open, and the coordinator's decision of 2026-10-12 to allow three steps on a subrange concerns `asinh` and `acosh` there ([the integration entry](../../devnotes.md#2026-10-12-integration-of-expm1-tanh-erf-log1p-atan-atan2-asin-and-acos-first-push)).  On those branches the argument of `log1p` is itself a sum of rounded terms: `|x| + x²/(1 + √(1 + x²))` for `asinh` and `t + √(2t + t²)` for `acosh`, so a proof composes the errors of the square root, the quotient, and the sum with the error of `log1p`, as the proof of `tanh` composes the errors of `expm1` with its quotient.  The ports track recommended one step for `asinh` from the sampled checks, and Zimmermann's FreeBSD input `-0x1.02657ff36d5f3p-2` raised it to two ([the review](../../devnotes.md#2026-10-10-review-of-the-options-for-stages-7-and-8)).

## Tests

[The accuracy check](AsinhAccuracy.lean) compares the three functions natively with the doubles nearest to their values, computed by [the hyperbolic references](HyperbolicReference.lean) from `Reference.log` and `Reference.atanhFixed` with Lean's integers, and it fails at the first result more than two steps away.  The arguments of `asinh` are 100,001 evenly spaced values from -10 to 10, 100,000 hashed values over every exponent field with both signs, the doubles around three thresholds with both signs, 16 special values, and the ten inputs of `WorstCases.asinh`.  The arguments of `acosh` are 100,001 evenly spaced values from 1 to 10, 100,000 hashed values from 1 up, the 52 doubles `1 + 2^-k`, the doubles around three thresholds with both signs, the special values, and ten worst inputs.  The arguments of `atanh` are 100,001 evenly spaced values from -1 to 1, 100,000 hashed values below 1 in magnitude, the 106 doubles `±(1 - 2^-k)`, the doubles around three thresholds with both signs, the special values, and ten worst inputs.  The worst inputs are those of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [7], whose Table 3 lists 1.92 units for `asinh`, 2.25 for `acosh`, and 1.81 for `atanh` in FreeBSD 15.1 and OpenLibm.

| Function | Results | Largest distance | Unequal | C library |
|---|---|---|---|---|
| `asinh` | 200,057 | 2 steps | 23,065 | 2 steps, 23,068 unequal |
| `acosh` | 200,109 | 2 steps | 31,744 | 2 steps, 31,744 unequal |
| `atanh` | 200,163 | 2 steps | 18,856 | 2 steps, 18,855 unequal |

The table gives the results of `opus-verified-tests-13.log` of 2026-10-11.  For `asinh` the two-step results lie at `-0x1.02657ff36d5f3p-2` (Tables 6, 7, and 9) and `-0x1.0240f2bdb3f25p-2` (Table 7), and no other argument of the check lies two steps away, as a probe of the ports track found ([the worst inputs entry](../../devnotes.md#2026-10-11-zimmermanns-inputs-in-the-accuracy-checks)).  The references' truncation errors are stated in their docstrings and are not proved, and the references' Python models agreed with a 120-digit decimal computation at 3,000 random arguments each.

## Limits

The checkout gives no proved bound for these functions, so every claim about their accuracy here rests on the sampled check.  When the theorems arrive they will rest on the trusted base of the other functions: Talos's semantics of WebAssembly, `Module.initialStore`, and the decoder, as [the design notes](../../docs/design.md#scope-of-the-theorem) record.  The module calls Arm's logarithm where fdlibm calls its own, so results can differ from FreeBSD's in the last bit, and Zimmermann's errors for FreeBSD describe a related but different function.

## References

1. FreeBSD, `lib/msun/src/s_asinh.c`, commit [`20381bce4b63975494a2f4bc84257f6932e6d379`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_asinh.c).  Copyright (C) 1993 by Sun Microsystems, Inc.  The comment states the method.
2. FreeBSD, `lib/msun/src/e_acosh.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_acosh.c).  Copyright (C) 1993 by Sun Microsystems, Inc.
3. FreeBSD, `lib/msun/src/e_atanh.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_atanh.c).  Copyright (C) 1993 by Sun Microsystems, Inc.
4. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clauses 5.1 and 5.4.1 (the rounding of the square root), clause 9.2 and Table 9.1 (the recommended operations and their domains), and clause 9.2.1 (special values).
5. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.2.1, F.9.2.2, and F.9.2.3, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
6. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
7. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
8. FreeBSD, `lib/msun/src/e_log.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_log.c): "according to an error analysis, the error is always less than 1 ulp".
9. Arm Limited, optimized-routines, [`math/log.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/log.c), commit `503fafe311c177de0e571c458c7c337b1ca5f522`: the comments on the worst-case errors of its two paths.
