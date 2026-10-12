# The hyperbolic sine and cosine

[The implementation](Sinh.lean) exports `sinh` and `cosh`, ports of fdlibm's `e_sinh.c` and `e_cosh.c` with the helpers `__frexp_exp` and `__ldexp_exp` of `k_exp.c`, as FreeBSD's msun has them at commit `20381bce` [1, 2, 3].  Both compute from `expm1 |x|` below a threshold and from `exp |x|` above it, and the port calls [the exponential minus one](Tanh.lean) and Arm's exponential in [the exponential's module](Exp.lean) where fdlibm calls `expm1` and `exp`.  The decided bounds are one step for `cosh` and three for `sinh`, and both are proved for every finite input: `CoshTheorem.cosh_within_one` and `SinhTheorem.sinh_within_three`, carried to the decoded module by `SinhBytes.sinh_bytes_accuracy` and `cosh_bytes_accuracy`, with `SinhFile` connecting that module to `build/verified/sinh.wasm`.  `sinh` stays at three steps because the proof's bound would fail two steps by a factor of 0.83 near `|x| = 0.443`, while sampling and Zimmermann's worst inputs find two.  Every accepted theorem reports only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`sinh` computes `Real.sinh a` and `cosh` computes `Real.cosh a`, where `a` is the value of the argument.  Every finite double is in both domains.  The bounds are stated as `F64SignedRounding.WithinSteps 1` for `cosh` and `WithinSteps 3` for `sinh`, with `WithinSteps` defined in [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean).  Both functions overflow where `e^|a|/2` reaches the threshold `2^1024 - 2^970` of IEEE 754-2019 clause 4.3.1 [4], at `|a| ≈ 710.47586`.

| Input | `sinh` | `cosh` | Source of the rule | Port |
|---|---|---|---|---|
| `+0`, `-0` | the same zero | `1` | IEEE 754-2019 9.2.1 [4]; C99 F.9.2.5 and F.9.2.4 [5] | `x` below `2^-28`, and `1 + expm1 0` |
| `+∞`, `-∞` | the same infinity | `+∞` | IEEE 754-2019 9.2.1; C99 F.9.2.5 and F.9.2.4 | `x + x` and `x · x` |
| NaN | the canonical NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [6] | `x + x` and `x · x` |
| finite, beyond the overflow threshold | `±∞` | `+∞` | IEEE 754-2019 4.3.1 | `x · 10^307` and `10^300 · 10^300` |

`SinhTheorem` proves the rows of `sinh` as equalities of bits (`sinh_zero`, `sinh_pos_infinity`, `sinh_neg_infinity`, `sinh_nan`), and `CoshTheorem` proves the infinite and NaN rows of `cosh` (`cosh_pos_infinity`, `cosh_neg_infinity`, `cosh_nan`).  No theorem states `cosh (±0) = 1` exactly; `cosh_within_one` places the result within one step of 1.  IEEE 754-2019 lists `sinh` and `cosh` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [4].  fdlibm states no error bound for either function [1, 2].

## Algorithm

Both functions reduce to `|x|` by symmetry, `sinh` with the sign `h = ±1/2` of `x` and `cosh` with none [1, 2].  With `E = expm1 |x|` and `e = exp |x|`, the identities `sinh |x| = (E + E/(E + 1))/2` and `cosh |x| = 1 + E²/(2 (E + 1)) = (e + 1/e)/2` give forms that keep relative accuracy where `e` is near 1.  The table lists the form of each range, with the thresholds that the code compares with the high word of `|x|`.

| Range of `\|x\|` | `sinh` | `cosh` |
|---|---|---|
| below `2^-28` | `x` | |
| below `2^-55` | | `1 + E`, which is 1 |
| below `0.5 ln 2` | `h (2E - E²/(E + 1))` | `1 + E²/(2 (1 + E))` |
| `0.5 ln 2` to 1 | `h (2E - E²/(E + 1))` | `e/2 + (1/2)/e` |
| 1 to 22 | `h (E + E/(E + 1))` | `e/2 + (1/2)/e` |
| 22 to 709.78 (high word `0x40862E42`) | `h e` | `e/2` |
| to high word `0x408633CE`, about 710.476 | `2h · __ldexp_exp (\|x\|, -1)` | `__ldexp_exp (\|x\|, -1)` |
| above | `x · 10^307` | `10^300 · 10^300` |

Below 1 the code evaluates `2E - E²/(E + 1)`, which equals `E + E/(E + 1)`, and fdlibm's comment gives only the second form.  From 22 on, `e^-|x|` is below `2^-63` of `e^|x|` and drops out.  Near the overflow threshold `e^|x|` itself overflows although `e^|x|/2` does not, so `__ldexp_exp (x, -1)` computes `exp (x - kln2)` with `k = 1799` and `kln2` the double nearest `1799 ln 2`, sets the exponent field of that result to 2046, and multiplies by the power of two that restores the scale, `2^(k - 1 + f - 2046)` with `f` the old exponent field [3].  David Schultz's comment states that `k` was chosen to minimize `|exp (kln2) - 2^k|` [3].

## Implementation

The sources are FreeBSD's `lib/msun/src/e_sinh.c`, `e_cosh.c`, and `k_exp.c` at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1, 2, 3].  `e_sinh.c` and `e_cosh.c` carry the notice "Copyright (C) 1993 by Sun Microsystems, Inc.  All rights reserved.  Developed at SunSoft, a Sun Microsystems, Inc. business.  Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved."  `k_exp.c` carries "Copyright (c) 2011 David Schultz", `SPDX-License-Identifier: BSD-2-Clause`, and the two conditions and the disclaimer of that license.  The module docstring of [the implementation](Sinh.lean) names both copyrights, summarizes Sun's permission, and gives the SPDX identifier, without the notices' full text.

The port is written in the Verified dialect, which [the Verified compiler](../README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Tanh.expm1Kernel, Tanh.expm1, frexpExp, ldexpExp, sinhWith, coshWith, sinh, cosh]` lists the definitions of the earlier ports first, so that the module contains them.  `sinhWith` and `coshWith` take the exponential's table as a parameter, and `sinh` and `cosh` pass `Exp.expTable`, as the base-2 exponential's module does.

| fdlibm calls | Port calls | Same function |
|---|---|---|
| `expm1` (`s_expm1.c`) | `Tanh.expm1` | Yes |
| `exp` (`e_exp.c`) | `Exp.expWith Exp.expTable`, Arm's `exp` | No.  Both state errors below one unit in the last place [8], Arm's 0.511 units, and their results can differ in the last bit. |
| `__ldexp_exp`, `__frexp_exp` (`k_exp.c`) | `Sinh.ldexpExp`, `Sinh.frexpExp` | Yes, with Arm's `exp` inside |

| C code | Port | Reason |
|---|---|---|
| `if (shuge + x > one) return x` | the test kept | The expression raises the inexact flag in C, and the test holds for every `\|x\| < 2^-28`. |
| `h = 0.5; if (jx < 0) h = -h;` | `if jx >>> 31 == 1 then -0.5 else 0.5` | One `let`. |
| `int` exponents `expt` and `ex_expt` | two's complement words, the caller's `-1` as `0 - 1` | The dialect has unsigned words only. |
| `INSERT_WORDS (scale, (0x3ff + expt) << 20, 0)` | the low 32 bits of `(0x3ff + expt) <<< 20`, shifted into the high half | The C expression is a 32-bit `int`. |
| `GET_HIGH_WORD`, `SET_HIGH_WORD` | the top half of the 64-bit word | |
| `fabs` | `Float.abs`, compiled to `f64.abs` | |
| floating-point flags, `errno` | none | WebAssembly has no floating-point status flags. |

For this document a script compared the port's constants with the C sources at the pinned commit, and each decimal converts to the port's bits.  `kln2 = 1246.97177782734161156` has the bits `0x40937BE319BA0DA4`, and a 60-digit decimal computation of `1799 ln 2 = 1246.9717778273416116416…` confirms that it is the double nearest that number, as the journal also records.  Every high word that the C code compares with appears in the port.

| Constant | Bits | Value |
|---|---|---|
| `shuge` | `0x7FAC7B1F3CAC7433` | `1.0e+307` |
| `huge` | `0x7E37E43C8800759C` | `1.0e+300` |
| `kln2` | `0x40937BE319BA0DA4` | `1246.97177782734161156` |
| `0x3ff + 1023` | 2046 | the exponent field that `__frexp_exp` sets |

| High word | Value | Test |
|---|---|---|
| `0x3e300000` | `2^-28` | `sinh` returns `x` below it |
| `0x3c800000` | `2^-55` | `cosh` returns `1 + E` below it |
| `0x3fd62e43` | about `0.5 ln 2` | `cosh` switches from `expm1` to `exp` |
| `0x3ff00000` | 1 | `sinh` switches forms |
| `0x40360000` | 22 | `expm1` below it |
| `0x40862E42` | 709.78 | `exp \|x\|` below it |
| `0x408633CE` | 710.4756 to 710.4761 | `__ldexp_exp` up to it |

## Theorems

The theorems are in [the cosh theorem module](CoshTheorem.lean), [the sinh theorem module](SinhTheorem.lean), [the byte theorems](SinhBytes.lean), and [the file module](SinhFile.lean).  `x` is a Lean `Float` and `a = value x.toBits` its real value.

| Theorem | Statement |
|---|---|
| `CoshTheorem.cosh_within_one` | For finite `x`, `WithinSteps 1 (Real.cosh a) (Sinh.cosh x).toBits`. |
| `SinhTheorem.sinh_within_three` | For finite `x`, `WithinSteps 3 (Real.sinh a) (Sinh.sinh x).toBits`. |
| `sinh_zero`, `sinh_pos_infinity`, `sinh_neg_infinity`, `sinh_nan` | `sinh (±0)` returns its argument's bits, `±∞` give `±∞`, and a NaN gives the canonical NaN. |
| `cosh_pos_infinity`, `cosh_neg_infinity`, `cosh_nan` | Both infinities give `+∞`, and a NaN gives the canonical NaN. |
| `SinhBytes.ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant, `Exp.expTable` borrowed at address 4096, and a memory cap of at most 65,535 pages. |
| `sinh_bytes_accuracy`, `cosh_bytes_accuracy` | In the form of `ExpTheorem.exp_bytes_accuracy`: the module's bytes decode to it, functions 11 and 12 are exported as `sinh` and `cosh`, and every call from a `Ready` store returns the bits of the Lean function, within the bound above for finite `x`, and leaves a `Ready` store. |
| `sinh_module_accuracy` | The two byte theorems together. |
| `SinhFile.sinh_file`, `sinh_file_decode` | `build/verified/sinh.wasm` holds `encode Sinh.compiled.module` and decodes to the module of the byte theorems; the decode theorem takes its bytes from `sinh_module_accuracy`, so its axiom report covers both byte theorems. |

The track built and checked the modules on minideb2 (`expm1-merge-1.log`, `expm1-sinhfile-1.log` in its worktree).  The merge into `transcendentals` built on minideb1 with 9,452 jobs and reported the three permitted axioms for both byte theorems (`opus-merge-sinh-1.log`), and `tests/verified/run.sh` checks the file theorem through its entry `sinh:SinhBytes:SinhFile` (`opus-verified-tests-14.log`).

## Proof

The proof modules, in dependency order, are `ExpTightPoly`, `ExpTight`, and `ExpTightFloat`, which tighten the exponential's bound; `SinhWords`; `CoshSmall`, `CoshMid`, `CoshLarge`, and `CoshTheorem`; `SinhLdexpBits` and `SinhLdexp`; `Expm1NearPos`, `SinhExpm1`, and `SinhCore`; `SinhSmall`, `SinhSmallCases`, `SinhMid`, and `SinhMidCases`; `SinhSign`, `SinhOverflow`, `SinhRanges`, and `SinhTheorem`; and `SinhBytes` and `SinhFile`.  Three ProofKit modules were added for them: [`F64NearestHalf`](../../LeanExe/ProofKit/F64NearestHalf.lean) (a nearest rounding of `s` in `[2^-1022, 2^1022)` lies within `u s`), [`F64NearestBand`](../../LeanExe/ProofKit/F64NearestBand.lean) (one step when the rounded real lies less than a spacing above the target and less than three quarters of a spacing below it), and [`F64NearestHalve`](../../LeanExe/ProofKit/F64NearestHalve.lean) (halving keeps a word nearest).

`ExpTightFloat.exp_relative` proves `|exp x - e^a| ≤ 1.033 · 2^-53 · e^a` for `-708 ≤ a ≤ 709.7827`, and `exp_near` states the result as the nearest rounding of a real within `2^-53/32` relative of `e^a` on `(-512, 709.7827]`, with `negative_near` and `positive_near` for the special paths.  The bound `ExpRelative.expWith_relative` of `1.405 · 2^-53`, which the error function's proof uses, gives `cosh` a margin factor of only 0.68 on `[0.3466, 22)`; with the tight bound and `F64NearestBand`, `cosh` reaches one step there.  On `[709.78, 710.476]` both functions call `ldexpExp`, and `SinhLdexp.ldexp_within` covers any target within `e^-a/2` of `e^a/2`, using that `kln2` lies within `9 · 10^-17` of `1799 ln 2` and that `|x| - kln2` is exact.

| Range of `|a|` | `sinh` | Reason |
|---|---|---|
| below `2^-28` | one step | The result is `x`. |
| `2^-28` to 1 | three steps | Between 0.347 and 0.481, `expm1` takes its `k = 1` path; after tightening its bound, the relative error before the last rounding still reaches `2.55 u` at `0.443`, which is 2.41 spacings: a margin factor of 0.83 against two steps and 1.15 against three. |
| 1 to 22 | three steps | An analysis by spacings would allow two, but the criterion used does not handle the binade edges. |
| from 22 | one step | `e^a/2`, or the `ldexpExp` form near overflow. |

The ports track recommended one step for `cosh` and two for `sinh` from the sampled distances, and it noted that each function adds roundings to a helper whose error is already near half a unit, for example two products and a sum to `exp` in `cosh` ([its journal section](../../devnotes.md#2026-10-10-ports-of-sinh-cosh-asinh-acosh-and-atanh)).  In `sinh` below 1 the code rounds `E²`, `E + 1`, the quotient, and the difference, and from 1 to 22 it rounds `E + 1`, the quotient, and the sum of two terms of the same sign, each on top of the error of `E`.  Its fallback for `cosh` was two steps if a proof could not keep the final word within one and a half spacings of the exact value.  On `[0.5 ln 2, 22)` the result is `e/2 + (1/2)/e`, and a relative error `δ` of `e` moves the exact value of that expression by `δ (e - 1/e)/(e + 1/e)` relative, a factor that tends to 1 as `|x|` grows.  The two products and the sum add their roundings to that, so a relative bound of `1.405 · 2^-53` on `e` leaves less room within one and a half spacings than the `1.033 · 2^-53` of the tight bound.

## Tests

[The accuracy check](SinhAccuracy.lean) compares `Sinh.sinh` and `Sinh.cosh` natively with the doubles nearest to `sinh x` and `cosh x`, computed by [the hyperbolic references](HyperbolicReference.lean) from `Reference.expm1` with Lean's integers, and it fails at the first `sinh` result more than two steps away or `cosh` result more than one step away.  Its 208,106 arguments are 100,001 evenly spaced values from -30 to 30, 4,001 evenly spaced values from 709 to 711 and their negations, 100,000 hashed values with exponents from `2^-60` to `2^9` and both signs, the doubles around the seven thresholds of the code with both signs, 12 special values, and the 21 inputs of `WorstCases.sinh` and `WorstCases.cosh`.  The worst inputs are those of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [7], whose Table 3 lists 1.88 units for `sinh` and 1.47 for `cosh` in FreeBSD 15.1 and OpenLibm.

In `opus-verified-tests-13.log` of 2026-10-11 all 208,106 results of `sinh` lie within two steps of the reference, 30,646 of them unequal to it, and all results of `cosh` within one step, 19,040 unequal.  The C library's `sinh` and `cosh` both lie within two steps, with 30,709 and 19,132 results unequal.  The ports track's Python models of the ports, with the C library standing in for the helpers, found the same distances, and the references' Python models agreed with a 120-digit decimal computation at 3,000 random arguments each ([its journal section](../../devnotes.md#2026-10-10-ports-of-sinh-cosh-asinh-acosh-and-atanh)).  The references' truncation errors are stated in their docstrings and are not proved.

## Limits

The theorems rest on the trusted base of the other functions: Talos's semantics of WebAssembly, `Module.initialStore`, the decoder, and the elaborator `binary_file%` of the file theorem, as [the design notes](../../docs/design.md#scope-of-the-theorem) record.  As for `exp`, they cover the canonical NaN argument only and sequences of calls to `sinh` and `cosh` without other host actions.  The proved three steps of `sinh` exceed the two steps that the check and the worst inputs find.  The module calls Arm's exponential where fdlibm calls its own, so results can differ from FreeBSD's `sinh` and `cosh` in the last bit, and Zimmermann's errors for FreeBSD describe a related but different function.

## References

1. FreeBSD, `lib/msun/src/e_sinh.c`, commit [`20381bce4b63975494a2f4bc84257f6932e6d379`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_sinh.c).  Copyright (C) 1993 by Sun Microsystems, Inc.  The comment states the method and the special cases.
2. FreeBSD, `lib/msun/src/e_cosh.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_cosh.c).  Copyright (C) 1993 by Sun Microsystems, Inc.
3. FreeBSD, `lib/msun/src/k_exp.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_exp.c).  Copyright (c) 2011 David Schultz, BSD-2-Clause.
4. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clause 4.3.1 (the overflow threshold), clause 9.2 and Table 9.1 (the recommended operations `sinh` and `cosh`), and clause 9.2.1 (special values).
5. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.2.4, and F.9.2.5, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
6. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
7. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
8. FreeBSD, `lib/msun/src/e_exp.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_exp.c): "according to an error analysis, the error is always less than 1 ulp".
