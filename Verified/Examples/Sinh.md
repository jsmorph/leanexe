# The hyperbolic sine and cosine

[The implementation](Sinh.lean) exports `sinh` and `cosh`, ports of fdlibm's `e_sinh.c` and `e_cosh.c` with the helpers `__frexp_exp` and `__ldexp_exp` of `k_exp.c`, as FreeBSD's msun has them at commit `20381bce` [1, 2, 3].  Both compute from `expm1 |x|` below a threshold and from `exp |x|` above it, and the port calls [the exponential minus one](Tanh.lean) and Arm's exponential in [the exponential's module](Exp.lean) where fdlibm calls `expm1` and `exp`.  The decided bounds are one step for `cosh` and two steps for `sinh` in the decision table of [the plan](../../transcendentals.md#decisions), while its status table gives `sinh` two or three steps.  This checkout, at commit `77ce56f4`, holds the port, its accuracy check, and no theorem about the accuracy of either function.  The plan records `cosh` as proved and `sinh` as in progress on the branch of the track `expm1`, and a merge build of that work, running on the build host when this document was written, reports theorems named `CoshTheorem.cosh_within_one` and `SinhTheorem.sinh_within_three`.

## Specification

`sinh` computes `Real.sinh a` and `cosh` computes `Real.cosh a`, where `a` is the value of the argument.  Every finite double is in both domains.  The bounds are to be stated as `F64SignedRounding.WithinSteps n`, defined in [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean), as for `tanh`.  Both functions overflow where `e^|a|/2` reaches the threshold `2^1024 - 2^970` of IEEE 754-2019 clause 4.3.1 [4], at `|a| ≈ 710.47586`.

| Input | `sinh` | `cosh` | Source of the rule | Port |
|---|---|---|---|---|
| `+0`, `-0` | the same zero | `1` | IEEE 754-2019 9.2.1 [4]; C99 F.9.2.5 and F.9.2.4 [5] | `x` below `2^-28`, and `1 + expm1 0` |
| `+∞`, `-∞` | the same infinity | `+∞` | IEEE 754-2019 9.2.1; C99 F.9.2.5 and F.9.2.4 | `x + x` and `x · x` |
| NaN | the canonical NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [6] | `x + x` and `x · x` |
| finite, beyond the overflow threshold | `±∞` | `+∞` | IEEE 754-2019 4.3.1 | `x · 10^307` and `10^300 · 10^300` |

No theorem in this checkout states any of these results.  IEEE 754-2019 lists `sinh` and `cosh` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [4].  fdlibm states no error bound for either function [1, 2].

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

This checkout has no theorem about the accuracy or the exceptional values of `Sinh.sinh` or `Sinh.cosh`.  `verified_compile` generates `Sinh.compiled` with its `bytes`, `initial`, and `implements` theorems, which state that the compiled module computes the Lean definitions, as [the compiler's documentation](../README.md#running-it) describes.  No byte theorem with a numerical bound and no file theorem exist for `sinh.wasm`, and `tests/verified/run.sh` writes and validates the module and runs the accuracy check only.

[The plan](../../transcendentals.md#functions) records `CoshTheorem.cosh_within_one` as proved on branch `w/expm1`, from a tight bound on the exponential, `ExpTightFloat.exp_relative`, of `1.033 · 2^-53` relative.  The bound that this checkout states, `ExpRelative.expWith_relative`, allows `1.405 · 2^-53`.  The plan records `sinh` as in progress, at two steps if the `k = 1` path of `expm1` can be tightened and at three otherwise.  A build of a merge of that work into the primary checkout, logged in `opus-merge-sinh-1.log`, was running on the build host when this document was written, with its last output at 20:31 on 2026-10-11 by the build host's clock.  Its output names the modules `ExpTight`, `ExpTightPoly`, `ExpTightFloat`, `CoshSmall`, `CoshMid`, `CoshLarge`, `CoshTheorem`, `SinhWords`, `SinhSign`, `SinhExpm1`, `SinhCore`, `SinhSmall`, `SinhSmallCases`, `SinhMid`, `SinhMidCases`, `SinhLdexpBits`, `SinhLdexp`, `SinhOverflow`, `SinhRanges`, `SinhTheorem`, and `SinhBytes`.  It reports 84 of their declarations, among them `CoshTheorem.cosh_within_one`, `SinhTheorem.sinh_within_three`, `SinhBytes.sinh_bytes_accuracy`, `cosh_bytes_accuracy`, and `sinh_module_accuracy`, each depending on `propext`, `Classical.choice`, and `Quot.sound` only.  The name `sinh_within_three` points to three steps, against the two steps of the plan's decision table.  None of these modules is in this checkout, so this document states neither their hypotheses nor their proofs.

## Proof

This checkout holds no proof module for `sinh` or `cosh`.  The proved results that the proofs can build on are `Expm1Theorem.expm1_within_one` and the errors of the `expm1` paths before their last rounding in `Expm1Near`, described in [the expm1 and tanh document](Tanh.md), and `ExpRelative.expWith_relative` and `ExpTheorem.exp_one_step`, described in [the exponential's document](Exp.md).  `Expm1Near` covers negative arguments and positive arguments from 2 to 44, while `sinh` calls `expm1` on `[0, 22)` and `cosh` on `[0, 0.5 ln 2)`, so the paths for positive arguments below 2 need their own errors before the last rounding.

The ports track recommended one step for `cosh` and two for `sinh` from the sampled distances, and it noted that each function adds roundings to a helper whose error is already near half a unit, for example two products and a sum to `exp` in `cosh` ([its journal section](../../devnotes.md#2026-10-10-ports-of-sinh-cosh-asinh-acosh-and-atanh)).  In `sinh` below 1 the code rounds `E²`, `E + 1`, the quotient, and the difference, and from 1 to 22 it rounds `E + 1`, the quotient, and the sum of two terms of the same sign, each on top of the error of `E`.  Its fallback for `cosh` was two steps if a proof could not keep the final word within one and a half spacings of the exact value.  On `[0.5 ln 2, 22)` the result is `e/2 + (1/2)/e`, and a relative error `δ` of `e` moves the exact value of that expression by `δ (e - 1/e)/(e + 1/e)` relative, a factor that tends to 1 as `|x|` grows.  The two products and the sum add their roundings to that, so a relative bound of `1.405 · 2^-53` on `e` leaves less room within one and a half spacings than the `1.033 · 2^-53` of the tight bound.

## Tests

[The accuracy check](SinhAccuracy.lean) compares `Sinh.sinh` and `Sinh.cosh` natively with the doubles nearest to `sinh x` and `cosh x`, computed by [the hyperbolic references](HyperbolicReference.lean) from `Reference.expm1` with Lean's integers, and it fails at the first `sinh` result more than two steps away or `cosh` result more than one step away.  Its 208,106 arguments are 100,001 evenly spaced values from -30 to 30, 4,001 evenly spaced values from 709 to 711 and their negations, 100,000 hashed values with exponents from `2^-60` to `2^9` and both signs, the doubles around the seven thresholds of the code with both signs, 12 special values, and the 21 inputs of `WorstCases.sinh` and `WorstCases.cosh`.  The worst inputs are those of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [7], whose Table 3 lists 1.88 units for `sinh` and 1.47 for `cosh` in FreeBSD 15.1 and OpenLibm.

In `opus-verified-tests-13.log` of 2026-10-11 all 208,106 results of `sinh` lie within two steps of the reference, 30,646 of them unequal to it, and all results of `cosh` within one step, 19,040 unequal.  The C library's `sinh` and `cosh` both lie within two steps, with 30,709 and 19,132 results unequal.  The ports track's Python models of the ports, with the C library standing in for the helpers, found the same distances, and the references' Python models agreed with a 120-digit decimal computation at 3,000 random arguments each ([its journal section](../../devnotes.md#2026-10-10-ports-of-sinh-cosh-asinh-acosh-and-atanh)).  The references' truncation errors are stated in their docstrings and are not proved.

## Limits

The checkout gives no proved bound for either function, so every claim about their accuracy here rests on the sampled check.  When the theorems arrive they will rest on the trusted base of the other functions: Talos's semantics of WebAssembly, `Module.initialStore`, and the decoder, as [the design notes](../../docs/design.md#scope-of-the-theorem) record.  The module calls Arm's exponential where fdlibm calls its own, so results can differ from FreeBSD's `sinh` and `cosh` in the last bit, and Zimmermann's errors for FreeBSD describe a related but different function.

## References

1. FreeBSD, `lib/msun/src/e_sinh.c`, commit [`20381bce4b63975494a2f4bc84257f6932e6d379`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_sinh.c).  Copyright (C) 1993 by Sun Microsystems, Inc.  The comment states the method and the special cases.
2. FreeBSD, `lib/msun/src/e_cosh.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_cosh.c).  Copyright (C) 1993 by Sun Microsystems, Inc.
3. FreeBSD, `lib/msun/src/k_exp.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_exp.c).  Copyright (c) 2011 David Schultz, BSD-2-Clause.
4. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clause 4.3.1 (the overflow threshold), clause 9.2 and Table 9.1 (the recommended operations `sinh` and `cosh`), and clause 9.2.1 (special values).
5. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.2.4, and F.9.2.5, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
6. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
7. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
8. FreeBSD, `lib/msun/src/e_exp.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_exp.c): "according to an error analysis, the error is always less than 1 ulp".
