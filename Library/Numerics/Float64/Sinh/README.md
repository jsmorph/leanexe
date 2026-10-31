# The hyperbolic sine and cosine

[The implementation](Program.lean) exports `sinh` and `cosh`, ports of fdlibm's `e_sinh.c` and `e_cosh.c` with the helpers `__frexp_exp` and `__ldexp_exp` of `k_exp.c`, as FreeBSD's msun has them [1, 2, 3].  Both compute from `expm1 |x|` below a threshold and from `exp |x|` above it, and the port calls [the exponential minus one](../Tanh/Program.lean) and Arm's exponential in [the exponential's module](../Exp/Program.lean) where fdlibm calls `expm1` and `exp`.  The decided bounds are one step for `cosh` and three for `sinh`, and both are proved for every finite input: `CoshTheorem.cosh_within_one` and `SinhTheorem.sinh_within_three`, carried to the decoded module by `SinhBytes.sinh_bytes_accuracy` and `cosh_bytes_accuracy`, with `SinhFile` connecting that module to `build/verified/sinh.wasm`.  `sinh` stays at three steps because the two-step allowance is about 0.83 times the composed error bound near `|x| = 0.443`, while sampling and Zimmermann's worst inputs find two.  Every accepted theorem reports only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`sinh` computes `Real.sinh a` and `cosh` computes `Real.cosh a`, where `a` is the value of the argument.  Every finite double is in both domains.  The bounds are `F64SignedRounding.WithinSteps 1` for `cosh` and `WithinSteps 3` for `sinh`, with `WithinSteps` defined in [the signed rounding reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean): the word is not a NaN, and its position in the ordered line of doubles, with both zeros at 0, lies within `n` of the position of the nearest-even rounding of the real value.  Both functions overflow where `e^|a|/2` reaches the threshold `2^1024 - 2^970` of IEEE 754-2019 clause 4.3.1 [4], at `|a| ≈ 710.47586`.

| Input | `sinh` | `cosh` | Source of the rule | Port |
|---|---|---|---|---|
| `+0`, `-0` | same zero | `1` | IEEE 754-2019 9.2.1 [4]; C99 F.9.2.5 and F.9.2.4 [5] | `x` below `2^-28`, and `1 + expm1 0` |
| `+∞`, `-∞` | same infinity | `+∞` | IEEE 754-2019 9.2.1; C99 F.9.2.5 and F.9.2.4 | `x + x` and `x · x` |
| NaN | canonical NaN | canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [6] | `x + x` and `x · x` |
| finite, beyond the overflow threshold | `±∞` | `+∞` | IEEE 754-2019 4.3.1 | `x · 10^307` and `10^300 · 10^300` |

`SinhTheorem` proves the rows of `sinh` as equalities of bits (`sinh_zero`, `sinh_pos_infinity`, `sinh_neg_infinity`, `sinh_nan`), and `CoshTheorem` proves the infinite and NaN rows of `cosh` (`cosh_pos_infinity`, `cosh_neg_infinity`, `cosh_nan`).  For `cosh (±0)` no theorem states the word: `cosh_within_one` places the result within one step of 1.  IEEE 754-2019 lists `sinh` and `cosh` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [4], and fdlibm states no error bound for either function [1, 2].

## Algorithm

Both functions reduce to `|x|` by symmetry, `sinh` with the sign `h = ±1/2` of `x` and `cosh` with none [1, 2].  With `E = expm1 |x|` and `e = exp |x|`, the identities `sinh |x| = (E + E/(E + 1))/2` and `cosh |x| = 1 + E²/(2 (E + 1)) = (e + 1/e)/2` give forms that keep relative accuracy where `e` is near 1.  The code compares each threshold of the table with the high word of `|x|`.

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

Below 1 the code evaluates `2E - E²/(E + 1)`, which equals `E + E/(E + 1)`, and fdlibm's comment gives only the second form.  From 22 on, `e^-|x|` is below `2^-63` of `e^|x|` and drops out.  Near the overflow threshold `e^|x|` itself overflows although `e^|x|/2` does not, so `__ldexp_exp (x, -1)` computes `exp (x - kln2)` with `k = 1799` and `kln2` the double nearest `1799 ln 2`, sets the exponent field of that result to 2046, and multiplies by the power of two that restores the scale, `2^(k - 1 + f - 2046)` with `f` the old exponent field [3].  The comment of `k_exp.c` states that `k` was chosen to minimize `|exp (kln2) - 2^k|` [3].

## Implementation

The sources are FreeBSD's `lib/msun/src/e_sinh.c`, `e_cosh.c`, and `k_exp.c` [1, 2, 3].  `e_sinh.c` and `e_cosh.c` carry the notice "Copyright (C) 1993 by Sun Microsystems, Inc.  All rights reserved.  Developed at SunSoft, a Sun Microsystems, Inc. business.  Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved."  `k_exp.c` carries "Copyright (c) 2011 David Schultz", `SPDX-License-Identifier: BSD-2-Clause`, and the two conditions and the disclaimer of that license.  The module docstring of [the implementation](Program.lean) quotes both notices verbatim, with the conditions and the disclaimer of the BSD license.

The port is written in the verified compiler's dialect, which [the verified compiler](../../../../Verified/README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Tanh.expm1Kernel, Tanh.expm1, frexpExp, ldexpExp, sinhWith, coshWith, sinh, cosh]` lists the definitions of the earlier ports first, so that the module contains them, and with the runtime's `alloc` and `release` first, `sinh` is function 11 and `cosh` function 12.  `sinhWith` and `coshWith` take the exponential's table as a parameter, and `sinh` and `cosh` pass `Exp.expTable`, as the base-2 exponential's module does.

| fdlibm calls | Port calls | Same function |
|---|---|---|
| `expm1` (`s_expm1.c`) | `Tanh.expm1` | Yes |
| `exp` (`e_exp.c`) | `Exp.expWith Exp.expTable`, Arm's `exp` | No.  fdlibm states an error below one unit in the last place [8] and Arm 0.511 units ([the exponential's document](../Exp/README.md)), and their results can differ in the last bit. |
| `__ldexp_exp`, `__frexp_exp` (`k_exp.c`) | `Sinh.ldexpExp`, `Sinh.frexpExp` | Yes, with Arm's `exp` inside |

| C code | Port | Reason |
|---|---|---|
| `if (shuge + x > one) return x` | test kept | The expression raises the inexact flag in C, and the test holds for every `\|x\| < 2^-28`. |
| `h = 0.5; if (jx < 0) h = -h;` | `if jx >>> 31 == 1 then -0.5 else 0.5` | One `let`. |
| `int` exponents `expt` and `ex_expt` | two's complement words, the caller's `-1` as `0 - 1` | The dialect has unsigned words only. |
| `INSERT_WORDS (scale, (0x3ff + expt) << 20, 0)` | low 32 bits of `(0x3ff + expt) <<< 20`, shifted into the high half | The C expression is a 32-bit `int`. |
| `GET_HIGH_WORD`, `SET_HIGH_WORD` | top half of the 64-bit word | |
| `fabs` | `Float.abs`, compiled to `f64.abs` | |
| floating-point flags, `errno` | none | WebAssembly has no floating-point status flags. |

The C sources annotate none of these constants with bit patterns, and each decimal converts to the port's bits, as a script that compares the port with the C sources at the pinned commit confirms.  `kln2 = 1246.97177782734161156` has the bits `0x40937BE319BA0DA4`, and `1799 ln 2 = 1246.9717778273416116416…` to 60 digits, so `kln2` is the double nearest that number, as the journal also records.  Every high word that the C code compares with appears in the port.

| Constant | Bits | Value |
|---|---|---|
| `shuge` | `0x7FAC7B1F3CAC7433` | `1.0e+307` |
| `huge` | `0x7E37E43C8800759C` | `1.0e+300` |
| `kln2` | `0x40937BE319BA0DA4` | `1246.97177782734161156` |
| `0x3ff + 1023` | 2046 | exponent field that `__frexp_exp` sets |

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

The theorems are in [the cosh theorem module](CoshTheorem.lean), [the sinh theorem module](SinhTheorem.lean), [the byte theorems](SinhBytes.lean), and [the file module](SinhFile.lean), each in the namespace `Library.Numerics.Float64.Sinh` followed by the module's name.  `x` is a Lean `Float` and `a = value x.toBits` its real value.  The byte theorems use `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `CoshTheorem.cosh_within_one` | For finite `x`, `WithinSteps 1 (Real.cosh a) (Sinh.cosh x).toBits`. |
| `SinhTheorem.sinh_within_three` | For finite `x`, `WithinSteps 3 (Real.sinh a) (Sinh.sinh x).toBits`. |
| `SinhTheorem.sinh_zero`, `sinh_pos_infinity`, `sinh_neg_infinity`, `sinh_nan` | `sinh (±0)` returns its argument's bits, `±∞` give `±∞`, and a NaN gives the canonical NaN. |
| `CoshTheorem.cosh_pos_infinity`, `cosh_neg_infinity`, `cosh_nan` | Both infinities give `+∞`, and a NaN gives the canonical NaN. |
| `SinhBytes.ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant, `Exp.expTable` borrowed at address 4096, and a memory cap of at most 65,535 pages. |
| `SinhBytes.sinh_entry_call`, `cosh_entry_call` | A call of function 11 or 12 from a `Ready` store returns, without a trap, the bits of `Sinh.sinh x` or `Sinh.cosh x`, and leaves a `Ready` store in which every heap region keeps its bytes. |
| `SinhBytes.sinh_bytes_accuracy`, `cosh_bytes_accuracy` | In the form of `ExpTheorem.exp_bytes_accuracy`: the module's bytes decode to it, functions 11 and 12 are exported as `sinh` and `cosh`, and every call from a `Ready` store returns the bits of the Lean function, within the bound above for finite `x`, and leaves a `Ready` store. |
| `SinhBytes.sinh_module_accuracy` | Conjunction of the two byte theorems. |
| `SinhFile.sinh_file`, `sinh_file_decode` | `build/verified/sinh.wasm` holds `encode Sinh.compiled.module` and decodes to the module of `sinh_module_accuracy`. |

Each theorem of the table has a `#print axioms` line.  The library build and a run of `tests/verified/run.sh` report `[propext, Classical.choice, Quot.sound]` for every theorem of the table except the two file theorems.  `tests/verified/run.sh` builds `Library.Numerics.Float64.Sinh.SinhBytes`, checks `SinhFile.lean` against the `sinh.wasm` it has written, and fails unless both file theorems report exactly the three permitted axioms.  That run passed this check for the `sinh` entry of `tests/verified/numerics.txt`, and since `sinh_file_decode` takes its bytes from `sinh_module_accuracy`, the axiom report of `sinh_file_decode` covers both byte theorems.

## Proof

### Modules

The proof has its own modules in `Library/Numerics/Float64/Sinh/`, and it builds on the chains of [the exponential](../Exp/README.md) and of [the exponential minus one and the hyperbolic tangent](../Tanh/README.md).  The table lists them by stage, in dependency order.  [The library aggregate](../../../../Library.lean) includes `SinhBytes`, so `lake build Verified Library` builds the chain.

| Stage | Modules | Content |
|---|---|---|
| Tight exponential | `ExpTightPoly`, `ExpTight`, `ExpTightFloat` | Arm's `exp` as the nearest word of a real within `u/32` of `e^a`, and within `1.033 u e^a` relative. |
| Words | `SinhWords` | Word of 0.5, exact halving, absolute value of a `Float`, and `e^a ≥ 1.4142` above `0.3466`. |
| `cosh` ranges | `CoshSmall`, `CoshMid`, `CoshLarge` | One step below `0.3466`, on `[0.3466, 22)`, and on `[22, 709.78]`. |
| Near overflow | `SinhLdexpBits`, `SinhLdexp` | Words of `frexpExp` and `ldexpExp`, and one step for any target within `e^-a/2` of `e^a/2`. |
| `cosh` theorem | `CoshTheorem` | `cosh_within_one` and the exceptional values. |
| `expm1` for `sinh` | `Expm1NearPos`, `SinhExpm1`, `SinhCore` | Paths `k = 1` and `k = 2` of `expm1` for positive arguments, and real identities of `sinh` below 22. |
| `sinh` ranges | `SinhSign`, `SinhSmall`, `SinhSmallCases`, `SinhMid`, `SinhMidCases`, `SinhOverflow`, `SinhRanges` | Sign `h = ±1/2`, three steps below 1 and from 1 to 22, and ranges outside `[2^-28, 22)`. |
| `sinh` theorem | `SinhTheorem` | `sinh_within_three` and the exceptional values. |
| Bytes | `SinhBytes`, `SinhFile` | Byte and file theorems. |

### Error budget

`ExpTightFloat.exp_relative` proves `|exp x - e^a| ≤ 1.033 · 2^-53 · e^a` for `-708 ≤ a ≤ 709.7827`, and `exp_near` states the result as the nearest rounding of a real within `2^-53/32` relative of `e^a` on `(-512, 709.7827]`, with `negative_near` and `positive_near` for the special paths.  With the earlier relative bound of about `1.4 · 2^-53` for `exp` (`ExpCoreBounds.core_error`, and `ExpRelative.expWith_relative` at `1.405 · 2^-53`) and a relative step criterion, the budget of `cosh` on `[0.3466, 22)` had a margin factor of only 0.68 for one step.  The tight bound and [the band criterion](../../../../LeanExe/ProofKit/F64NearestBand.lean) give one step on that range: `CoshMid` writes the error of the computed `T/2 + B` as `(T - e)/2 (1 - 1/(T e)) + (B - 1/(2 T))`, so the error of `T` enters with a factor below 1/2, and for `cosh a < 2` the error before the last rounding is at most `1.48 u` against the `1.5 u` that the band allows below the target.  Below 22, `sinh` evaluates `f t = t + t/(1 + t)` for `t = expm1 |x|`, with `2 sinh a = f τ` for `τ = e^a - 1`, and `SinhCore.f_diff` writes `f T - f τ = (T - τ)(1 + 1/((1 + T)(1 + τ)))`, so the error of `t` enters with a factor below 2.

| Range of `\|a\|` | `sinh` | `cosh` |
|---|---|---|
| below `2^-28` | one step: the result is `x`, within `(4/3) \|x\|³` (`SinhRanges.tiny_sinh`) | one step (`CoshSmall.cosh_tiny` below `2^-55`, `cosh_small` above): `t` within `2 u τ`, total error below `0.68 u` against `63/64 u` |
| `2^-28` to `0.3466` | three steps (`SinhSmallCases`): `t` within `2 u τ` | as above |
| `0.3466` to 1 | three steps: `t` within `0.4802 u` below `0.443`, `0.7302 u` to `τ = 1.49`, and `0.9802 u` above, plus the half spacing of `t` | one step (`CoshMid.cosh_mid`): the band of `F64NearestBand` |
| 1 to 22 | three steps (`SinhMidCases`): `t` within `1.9803 u` on `k = 1`, `u τ + 1.9605 u` on `k = 2`, and `1.8501 u τ` from `k = 3` | as above |
| 22 to `709.7822265625` | one step (`SinhRanges.sinh_large`) | one step (`CoshLarge.cosh_large`): the half of `exp` is the nearest word to a real within `u/64 e^a` of `e^a/2` |
| to `710.47607421875` | one step (`SinhRanges.sinh_ldexp`) | one step (`SinhLdexp.ldexp_within`) |
| above | `x · 10^307` is the infinity of the sign of `x` (`SinhRanges.sinh_overflow`) | `10^300 · 10^300` is infinite (`CoshTheorem`) |

`F64NearestRelative.within_rel_of` gives `sinh` three steps from a relative error below `2.9375 u`.  Between `0.347` and `0.481`, on the path `k = 1` of `expm1`, the relative error of the exact value before the last rounding reaches `2.55 u` at `|a| = 0.443`, which is 2.41 spacings of the binade of `sinh a`: a margin factor of 0.83 against two steps and 1.15 against three.  From 1 to 22 the worst relative error is `2.3 u`, on the path `k = 2`, and the spacing count there, at most 1.5, would allow two steps with a criterion near the binade boundaries that the proof does not have.  On `[709.78, 710.476]` both functions call `ldexpExp`, and `SinhLdexp.ldexp_within` covers any target within `e^-a/2` of `e^a/2`, using that `kln2` lies within `9 · 10^-17` of `1799 ln 2` (`kln2_delta`) and that `|x| - kln2` is exact (`sub_kln2`).  [The journal sections on `cosh` and `sinh`](../../../../devnotes.md#2026-10-10-exponential-minus-one-and-hyperbolic-tangent-track-expm1) record the budgets and the commits.

### Shared modules

The proof added the three ProofKit modules of the table.  It also uses the modules of the `tanh` proof, among them [the nearest sums](../../../../LeanExe/ProofKit/F64NearestSum.lean), [the nearest quotient](../../../../LeanExe/ProofKit/F64NearestDiv.lean), and [the relative step criteria](../../../../LeanExe/ProofKit/F64NearestRelative.lean), together with [one step against the full reference](../../../../LeanExe/ProofKit/F64FullStep.lean) in the top binade and [the borrowed table frame](../../../../LeanExe/ProofKit/BorrowedKept.lean).

| Module | Content |
|---|---|
| `F64NearestHalf`, [the half-spacing bound](../../../../LeanExe/ProofKit/F64NearestHalf.lean) | A nearest rounding of `s` in `[2^-1022, 2^1022)` lies within `u s`. |
| `F64NearestBand`, [the band criterion](../../../../LeanExe/ProofKit/F64NearestBand.lean) | One step when the rounded real lies less than a spacing above the target and less than three quarters of a spacing below it. |
| `F64NearestHalve`, [the nearest halving](../../../../LeanExe/ProofKit/F64NearestHalve.lean) | Halving keeps a word nearest, for targets from `2^-1020` to `2^1022`. |

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| Arm's polynomial differs from the Taylor polynomial of degree 9 by at most `2^-65` on `\|r\| ≤ 0.002708` | `ExpTightPoly.poly_check` |
| The exponent field of `kln2` is 1033 | `SinhLdexp.kln2_exponent` |
| Functions 11 and 12 are exported as `sinh` and `cosh` | `SinhBytes.sinh_export`, `cosh_export` |
| The file's bytes equal the encoder's | `SinhFile.sinh_file` |

### History

The plan first set two steps for `sinh` and one for `cosh` from the sampled distances.  The first budget, with the proved `1.4 u` for `exp`, reached two steps for `cosh` and three for `sinh`, so the exponential's bound was tightened first ([the journal](../../../../devnotes.md#2026-10-10-exponential-minus-one-and-hyperbolic-tangent-track-expm1)).  With the tighter bound `cosh` reaches one step, and `sinh` stays at three because of the path `k = 1` of `expm1`.

## Tests

[The accuracy check](../../../../tests/TestSupport/Numerics/SinhAccuracy.lean) compares `Sinh.sinh` and `Sinh.cosh` natively with the doubles nearest to `sinh x` and `cosh x`, computed by [the hyperbolic references](../../../../tests/TestSupport/Numerics/HyperbolicReference.lean) from `Reference.expm1` with Lean's integers, and it fails at the first `sinh` result more than two steps away or `cosh` result more than one step away.  Its 208,106 arguments are 100,001 evenly spaced values from -30 to 30, 4,001 evenly spaced values from 709 to 711 and their negations, 100,000 hashed values with exponents from `2^-60` to `2^9` and both signs, the five doubles around each of the seven thresholds of the code with both signs, 12 special values, and the 21 inputs of `WorstCases.sinh` and `WorstCases.cosh`.  The worst inputs are those of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [7], whose Table 3 lists 1.88 units for `sinh` and 1.47 for `cosh` in FreeBSD 15.1 and OpenLibm.

In the test run, all 208,106 results of `sinh` lie within two steps of the reference, 30,646 of them unequal to it, and all results of `cosh` within one step, 19,040 unequal.  The C library's `sinh` and `cosh` both lie within two steps, with 30,709 and 19,132 results unequal.  Python models of the ports, with the C library standing in for the helpers, found the same distances, and Python models of the references agreed with a 120-digit decimal computation at 3,000 random arguments each ([the journal section of the ports](../../../../devnotes.md#2026-10-10-ports-of-sinh-cosh-asinh-acosh-and-atanh)).  The references' truncation errors are stated in their docstrings and are not proved.

## Limits

The theorems rest on the trusted base of the other functions: Talos's semantics of WebAssembly, `Module.initialStore`, the decoder, and the elaborator `binary_file%` of the file theorem, as [the design notes](../../../../docs/design.md#scope-of-the-theorem) record.  Talos implements the deterministic profile, in which every NaN result is canonical [6], and an engine outside that profile may return other NaN bits.  As for `exp`, the theorems cover the canonical NaN argument only, and the byte theorems cover sequences of calls to `sinh` and `cosh`, so a host that calls another export or writes the memory between calls needs a theorem that the action preserves `Ready`.

The proved three steps of `sinh` exceed the two steps that the check and the worst inputs find, and no theorem states the word of `cosh (±0)`.  The module calls Arm's exponential where fdlibm calls its own, so results can differ from FreeBSD's `sinh` and `cosh` in the last bit.  Zimmermann's errors for FreeBSD therefore describe a related function with a different exponential.

## References

1. FreeBSD, [`lib/msun/src/e_sinh.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_sinh.c).
2. FreeBSD, [`lib/msun/src/e_cosh.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_cosh.c).
3. FreeBSD, [`lib/msun/src/k_exp.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_exp.c).
4. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229), clauses 4.3.1 and 9.2, Table 9.1, and clause 9.2.1.
5. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.2.4, and F.9.2.5, WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf), September 7, 2007.
6. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html).
7. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026, Table 3 and Tables 4 to 11.
8. FreeBSD, [`lib/msun/src/e_exp.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_exp.c).
