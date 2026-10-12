# The inverse hyperbolic functions

[The implementation](Asinh.lean) exports `asinh`, `acosh`, and `atanh`, ports of fdlibm's `s_asinh.c`, `e_acosh.c`, and `e_atanh.c` as FreeBSD's msun has them at commit `20381bce` [1, 2, 3].  Each writes its function as a logarithm of an algebraic expression and evaluates it with [the logarithm](Log.lean), [the logarithm of one plus its argument](Log1p.lean), and the square root, in a form chosen for each range.  The decided bound is two steps for each function ([the plan](../../transcendentals.md#functions)), which allowed three steps for `acosh` on `1 < x ≤ 2` if two could not be proved there.  `transcendentals` holds the port and its accuracy check but no theorem about the accuracy of these functions.  Branch `w/poly`, not yet merged, proves all three within two steps, with their exceptional values, the byte theorems of the three exports, and the file theorem of `asinh.wasm`.

## Specification

`asinh` computes `Real.arsinh a`, `acosh` computes `Real.arcosh a`, and `atanh` computes `Real.artanh a`, where `a` is the value of the argument and the pinned Mathlib defines the three as `log (a + √(1 + a²))`, `log (a + √(a² - 1))`, and `log √((1 + a)/(1 - a))`.  The domains are every finite double for `asinh`, `[1, ∞)` for `acosh`, and `(-1, 1)` for `atanh`.  The bound is `F64SignedRounding.WithinSteps 2`, defined in [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean): the word is not a NaN, and its position in the ordered line of doubles, with both zeros at 0, lies within two of the position of the nearest-even rounding of the real value.  None of the three overflows on a finite input inside its domain, since `asinh` and `acosh` of the largest double are about 710.48.

| Input | Port's result | Source of the rule | Theorem on `w/poly` |
|---|---|---|---|
| `asinh (±0)`, `asinh (±∞)` | the argument, by `x` below `2^-28` and `x + x` | IEEE 754-2019 9.2.1 [4]; C99 F.9.2.2 [5] | `AsinhTheorem.asinh_zero`, `asinh_neg_zero`, `asinh_inf`, `asinh_neg_inf` |
| `acosh 1` | `+0` | IEEE 754-2019 9.2.1; C99 F.9.2.1 | `AcoshTheorem.acosh_one` |
| `acosh x` for `x < 1`, `±0` and `-∞` included | NaN, by `(x - x)/(x - x)` | IEEE 754-2019 Table 9.1 (domain `[+1, +∞]`, invalid operation below 1); C99 F.9.2.1 | `AcoshTheorem.acosh_nan` |
| `acosh (+∞)` | `+∞`, by `x + x` | IEEE 754-2019 9.2.1; C99 F.9.2.1 | `AcoshTheorem.acosh_inf` |
| `atanh (±0)` | the argument | IEEE 754-2019 9.2.1; C99 F.9.2.3 | `AtanhTheorem.atanh_zero`, `atanh_neg_zero` |
| `atanh (±1)` | `±∞`, by `x/0` | IEEE 754-2019 9.2.1 (with the divideByZero exception); C99 F.9.2.3 | `atanh_one`, `atanh_neg_one` |
| `atanh x` for `\|x\| > 1` and `±∞` | NaN, by `(x - x)/(x - x)` | IEEE 754-2019 Table 9.1; C99 F.9.2.3 | `atanh_nan` |
| NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [6] | `asinh_nan`, `acosh_nan`, `atanh_nan` |

`transcendentals` has no theorem that states any of these results, and the theorems of the last column are on branch `w/poly`.  IEEE 754-2019 lists the three functions among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [4].  fdlibm states no error bound for any of them [1, 2, 3].

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

The code compares high words, so the boundaries at 2 and `2^28` of `asinh` and at 2 of `acosh` fall at `2 (1 + 2^-20)` and `2^28 (1 + 2^-20)`, the first values whose high word exceeds that of 2 or `2^28`.  The table gives the boundaries in round numbers.  The proofs on branch `w/poly` follow the exact boundaries.

## Implementation

The sources are FreeBSD's `lib/msun/src/s_asinh.c`, `e_acosh.c`, and `e_atanh.c` at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1, 2, 3].  Each carries the notice "Copyright (C) 1993 by Sun Microsystems, Inc.  All rights reserved.  Developed at SunPro (`s_asinh.c`) or SunSoft (the others), a Sun Microsystems, Inc. business.  Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved."  The module docstring of [the implementation](Asinh.lean) names the copyright and summarizes the permission as "freely distributable with this notice", without the notice's full text, and [the plan](../../transcendentals.md#corrections-found-by-the-documentation-review) lists the quotation of the full notice as a correction for the resumed work.

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

A script that compares the port with the C sources at the pinned commit finds that `ln2 = 6.93147180559945286227e-01` has the bits `0x3FE62E42FEFA39EF` given in both sources, that `huge` is `1.0e+300` with the bits `0x7E37E43C8800759C`, and that `one` is the literal `1.0`.  Every high word that the C code compares with appears in the port: `0x3e300000` (`2^-28`), `0x41b00000` (`2^28`), `0x40000000` (2), `0x3ff00000` (1), and `0x3fe00000` (`1/2`).  The journal records the same audit of the port ([its journal section](../../devnotes.md#2026-10-10-ports-of-sinh-cosh-asinh-acosh-and-atanh)).

## Theorems

`transcendentals` has no theorem about the accuracy or the exceptional values of `Asinh.asinh`, `Asinh.acosh`, or `Asinh.atanh`.  `verified_compile` generates `Asinh.compiled` with its `bytes`, `initial`, and `implements` theorems, which state that the compiled module computes the Lean definitions, as [the compiler's documentation](../README.md#running-it) describes.  `tests/verified/run.sh` writes and validates `asinh.wasm` and runs the accuracy check, and it has no file-theorem entry for this module.

Branch `w/poly`, in the worktree `/home/somebody/src/lt-poly` on minideb2, holds the theorems of the table, none of them merged into `transcendentals` ([the plan](../../transcendentals.md#state-of-each-track)).  `x` is a Lean `Float` and `a = value x.toBits` its real value.  Each theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.  `arc-acosh-13.log`, the build of `AsinhBytes`, lists the axiom report of every module of the chain, and `arc-file-6.log` lists that of `AsinhFile`, both under `build/transcendentals/` of that worktree.

| Theorem | Commit | Statement |
|---|---|---|
| `AtanhTheorem.atanh_within_two` | `b3d93058` | For finite `x` with `\|a\| < 1`, `WithinSteps 2 (Real.artanh a) (Asinh.atanh x).toBits`. |
| `AtanhTheorem.atanh_nan`, `atanh_one`, `atanh_neg_one`, `atanh_zero`, `atanh_neg_zero` | `b3d93058` | A NaN, an infinity, or a finite `x` with `\|a\| > 1` gives the canonical NaN, `±1` give `±∞`, and `±0` give `±0`. |
| `AsinhTheorem.asinh_within_two` | `e91fcfd9` | For finite `x`, `WithinSteps 2 (Real.arsinh a) (Asinh.asinh x).toBits`. |
| `AsinhTheorem.asinh_nan`, `asinh_inf`, `asinh_neg_inf`, `asinh_zero`, `asinh_neg_zero` | `e91fcfd9` | A NaN gives the canonical NaN, `±∞` give `±∞`, and `±0` give `±0`. |
| `AcoshTheorem.acosh_within_two` | `w/poly` | For finite `x` with `a ≥ 1`, `WithinSteps 2 (Real.arcosh a) (Asinh.acosh x).toBits`. |
| `AcoshTheorem.acosh_nan`, `acosh_inf`, `acosh_one` | `w/poly` | A NaN or a word below that of 1 or with the sign bit set, which includes `±0`, `-∞`, and every finite `x < 1`, gives the canonical NaN, `+∞` gives `+∞`, and 1 gives `+0`. |
| `AsinhBytes.atanh_bytes_accuracy`, `asinh_bytes_accuracy`, `acosh_bytes_accuracy` | `w/poly` | The bytes of `Asinh.compiled.module` decode to the module, functions 9, 10, and 11 are exported as `atanh`, `asinh`, and `acosh`, and the initial store is ready.  A call of each entry from a ready store returns without a trap the bits of the Lean function, within two steps of the reference on the domain of the accuracy theorem, and leaves a ready store in which every region of the heap before the call keeps its bytes. |
| `AsinhBytes.asinh_module_accuracy` | `w/poly` | The three byte theorems. |
| `AsinhFile.asinh_file`, `asinh_file_decode` | `w/poly` | `build/verified/asinh.wasm` holds `encode Asinh.compiled.module` and decodes to the module of `asinh_module_accuracy`. |

A ready store satisfies the allocator invariant, holds `Log.logTable` at address 4096 and `Log.logTable2` at address 6152 as borrowed arrays, and has a memory cap of at most 65,535 pages (`AsinhBytes.Ready`).  Each call leaves a ready store, so the byte theorems cover every sequence of calls to the three entries from the initial store.  `asinh_file_decode` depends on `asinh_module_accuracy`, so its axiom report covers the three byte theorems.  `arc-file-6.log` checks the file theorems against the `asinh.wasm` that `tools/Emit.lean` wrote from `Asinh.compiled.module`, since `tests/verified/run.sh` has no entry for `AsinhFile`.  The entry `asinh:AsinhBytes:AsinhFile` in its list of file modules would check them in each run, and `Verified.lean` must import the new modules, changes that the worker rules leave to the coordinator.

## Proof

### Results available in `transcendentals`

`transcendentals` holds no proof module for these functions.  The proved results they build on are `LogTheorem.log_within_one` and `Log1pTheorem.log1p_within_one`, one step each against `Real.log`, and the relative error of the rounded square root, which [the square-root bounds](../../LeanExe/ProofKit/F64SqrtBounds.lean) state.  A step bound on `log y` or `log1p y` at a computed `y` gives no bound on the function by itself, since the error of `y` passes into the result: a relative error `δ` of `y` moves `log1p y` by `δ y/(1 + y)`, at most `δ log1p y` when `y > 0`, and moves `log y` by `δ`.

### Method on branch `w/poly`

The proofs compose the theorems of `log` and `log1p` with the error of the computed argument.  `F64Compose.within_two_of_close` turns one step at `y₁` into two steps at `y₂` when `y₁` and `y₂` are positive and closer than one spacing of a binade whose start lies below both, and `F64Compose.error_of_within` bounds a word within one step by 1.5 spacings, or 2.5 in the top two spacings of a binade.  `F64RelError` tracks relative errors of positive values over ranges too wide for the scaled chains of `F64Approx`, and `F64Near.Near c y E` states that the word `c` is a nearest rounding of a real within `E` of `y`.

On the `log1p` branches one step of `log1p` at the computed argument is too weak.  An analysis with dense sampling and per-operation worst cases found that the rounding of the argument costs up to one spacing of the target, which `log1p` passes on with the factor `1/(1 + u)`, and that at some inputs the nearest word of `log1p` at the computed argument already lies two steps from the reference.  The proofs therefore use `Log1pTheoremNear.log1p_near`, which bounds the exact value `S` of the last operation of `log1p`, whose result is the nearest word of `S`, so that two steps follow when `|S - Y| < 2` spacings of the target `Y` (`F64TwoSteps.within_two_of_rounded`).  For `x ≥ 2^-29` its bound `errBound x` is `1.74 · 2^-53 x² + 2^-59 x` up to 0.285, between `0.43 · 2^-54` and `1.33 · 2^-54` from there to `2^53`, after a split of the case `K = 1`, `f < -0.175` at `f = -0.2501` and `f = -0.2199`, and `6 · 2^-54` above.

| Function and range | Method | State on `w/poly` |
|---|---|---|
| `asinh` and `atanh` below `2^-28` | The result is `x`, and `arsinh x` and `artanh x` lie within `\|x\|³` and `2 \|x\|³` of `x` (`AsinhTheoremTiny.arsinh_tiny`, `artanh_tiny`). | Proved, `c4cf80e2` |
| `asinh` and `acosh` from `2^28` | `Log.log \|x\| + ln2`: the error of `log` from `error_of_within`, then the nearest rounding of the sum (`AsinhTheoremLarge.log_ln2`). | Proved, `a5077186` |
| `asinh` on `[2, 2^29)`, `acosh` on `[2, 2^28]` | The argument within `1.32 · 2^-53` and `1.77 · 2^-53` relative, then `within_two_of_close` in `[1, 2)` (`AsinhTheoremMid`, `AcoshTheoremMid`). | Proved, `5ede907a`, `f8d93194` |
| `atanh` on `[2^-28, 1/2)` | `log1p_near` at the computed argument, moved to `2 artanh a` and halved (`F64Near.Near.half`): four ranges with a relative bound below `a = 0.1244`, the largest `1.892 · 2^-53`, and four with constant bounds above, the largest 0.973 of two spacings (`AtanhTheoremSmallCases`). | Proved, `5e37bd91` |
| `atanh` on `[1/2, 1)` | `2a` and `1 - a` exact, one division with relative error `2^-53`, and `2 artanh a ≥ log 3`: 0.42 of two spacings (`AtanhTheoremLarge`). | Proved, `5d7845b1` |
| `asinh` on `[2^-28, 2 (1 + 2^-20)]` | `log1p_near` at the computed argument: five ranges with a relative bound below `\|x\| = 0.2526`, the largest `1.966 · 2^-53`, and twenty with constant bounds above, the largest 0.981 of two spacings at `\|x\|` in `[1.155, 1.1753]` (`AsinhTheoremSmallCases.piece0` to `piece24`). | Proved, `8fc2f7de`, `e91fcfd9` |
| `acosh` on `(1, 2 (1 + 2^-20))` | `log1p (t + √(2t + t²))` with `t = x - 1` exact: half-spacing bounds of the sum `2t + t²` and of the root (`F64SqrtHalf.sqrt_half`, `AcoshTheoremSmall.acosh_s`), then `log1p_near` at the last sum `t + s` (`acosh_core`).  The 79 ranges of `t` in `AcoshTheoremPieces0` to `AcoshTheoremPieces3` split where `2t + t²` passes a power of 2.  In 53 of them the last sum is exact inside the binade of `s` (`add_exact`, `acosh_piece_exact`), and in 26 it carries a half-spacing bound (`acosh_piece_half`).  The largest share of two spacings is 0.988, for `t` from 0.0833 to 0.1006. | Proved: the lemmas in `027bc2a9`, `ad63d2c6`, and `98ed43a6`, and the ranges and the dispatcher on `w/poly` |

A model of the `acosh` branch with relative rounding errors reaches 1.25 to 1.32 times the two-step budget for every `t`, so relative bounds cannot give two steps on any part of it.  The model reaches 0.983 of the budget, near `t = 0.083`, only with half-spacing bounds of the root and of the sum `2t + t²` and an exact last sum, which the lemmas above provide.  The proof reaches 0.988 there, since each range charges its worst end to all of its points.  The constants of each range come from a generator in the track's scratch directory that checks every hypothesis of the range lemmas in exact rational arithmetic, and `norm_num` checks them again in each piece.  The journal of branch `w/poly` records these analyses and the logs `arc-near-1.log` to `arc-near-9.log` of the bound of `log1p`, in its section on the full theorems of the track `arc`.  The journal of `transcendentals` holds that section without these entries ([the section](../../devnotes.md#2026-10-10-full-theorems-for-log1p-atan-atan2-asin-and-acos-track-arc-minideb2)).

The modules on `w/poly` build in this order: the ProofKit modules `F64Near` and `F64SqrtHalf`; `Log1pTheoremNearTail` and `Log1pTheoremNear`, the bound of `log1p`; `AsinhTheoremBranches`, which states each branch of `asinh` and `acosh` as an equation, `AsinhTheoremTiny`, `AsinhTheoremLarge`, `AsinhTheoremMid`, `AcoshTheoremMid`, and `AsinhTheoremCompose`; `AtanhTheoremBranches`, `AtanhTheoremSmall`, `AtanhTheoremSmallCases`, `AtanhTheoremLarge`, and `AtanhTheorem`; `AsinhTheoremSmall`, `AsinhTheoremSmallCases`, and `AsinhTheorem`; `AcoshTheoremSmall`, `AcoshTheoremPieces0` to `AcoshTheoremPieces3`, `AcoshTheoremSmallCases`, and `AcoshTheorem`; and `AsinhBytes` and `AsinhFile`.  The dispatchers `AtanhTheorem`, `AsinhTheorem`, and `AcoshTheorem` turn the code's tests on the high and low words into comparisons of values (`F64PositiveOrder.value_le_iff`).  The exceptional values of `atanh` and `asinh` at `±1` and `±∞` follow from the definitions of `Wasm.IEEE64.div` and `Wasm.IEEE64.add` by `simp only` (`AtanhTheorem.div_zero_word`, `AsinhTheorem.inf_add_self`).

### History

The decided bound of `asinh` was first one step, from the sampled checks, and Zimmermann's FreeBSD input `-0x1.02657ff36d5f3p-2`, at which a model of the port lies two steps from the reference, raised it to two ([the review](../../devnotes.md#2026-10-10-review-of-the-options-for-stages-7-and-8)).  The integration entry of 2026-10-12 allowed three steps for `asinh` and `acosh` on a subrange if their compositions with `log1p` could not be closed ([the entry](../../devnotes.md#2026-10-12-integration-of-expm1-tanh-erf-log1p-atan-atan2-asin-and-acos-first-push)).  `asinh` and `acosh` both reached two steps on branch `w/poly`, so the proofs do not use the allowance.

## Tests

[The accuracy check](AsinhAccuracy.lean) compares the three functions natively with the doubles nearest to their values, computed by [the hyperbolic references](HyperbolicReference.lean) from `Reference.log` and `Reference.atanhFixed` with Lean's integers, and it fails at the first result more than two steps away.  The arguments of `asinh` are 100,001 evenly spaced values from -10 to 10, 100,000 hashed values over every exponent field below 2047 with both signs, the five doubles around each of three thresholds with both signs, 16 special values, and the ten inputs of `WorstCases.asinh`.  The arguments of `acosh` are 100,001 evenly spaced values from 1 to 10, 100,000 hashed values from 1 up, the 52 doubles `1 + 2^-k`, the doubles around three thresholds with both signs, the special values, and ten worst inputs.  The arguments of `atanh` are 100,001 evenly spaced values from -1 to 1, 100,000 hashed values below 1 in magnitude, the 106 doubles `±(1 - 2^-k)`, the doubles around three thresholds with both signs, the special values, and ten worst inputs.  The worst inputs are those of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [7], whose Table 3 lists 1.92 units for `asinh`, 2.25 for `acosh`, and 1.81 for `atanh` in FreeBSD 15.1 and OpenLibm.

| Function | Results | Largest distance | Unequal | C library |
|---|---|---|---|---|
| `asinh` | 200,057 | 2 steps | 23,065 | 2 steps, 23,068 unequal |
| `acosh` | 200,109 | 2 steps | 31,744 | 2 steps, 31,744 unequal |
| `atanh` | 200,163 | 2 steps | 18,856 | 2 steps, 18,855 unequal |

The table gives the results of `opus-verified-tests-14.log`, under `build/transcendentals/` of the primary checkout on minideb1.  For `asinh` the two-step results lie at `-0x1.02657ff36d5f3p-2` (Tables 6, 7, and 9) and `-0x1.0240f2bdb3f25p-2` (Table 7), and a probe found no other argument of the check two steps away ([the worst inputs entry](../../devnotes.md#2026-10-11-zimmermanns-inputs-in-the-accuracy-checks)).  The analysis on branch `w/poly` found further inputs, outside the check, at which the compiled functions lie two steps from the reference: the words `0x3fe0a9ff5094e9cc` for `asinh`, `0x3fd9147494025dc1` for `atanh`, and `0x3ff000007ffee997` for `acosh`.  The references' truncation errors are stated in their docstrings and are not proved, and the references' Python models agreed with a 120-digit decimal computation at 3,000 random arguments each.  The proved bound on branch `w/poly`, two steps for each function, equals the largest measured distance.

## Limits

`transcendentals` gives no proved bound for these functions, so every claim about their accuracy there rests on the sampled check.  The theorems on branch `w/poly` take the argument as a Lean `Float`, so they cover only the canonical NaN among the NaN words a WebAssembly caller can pass.  The byte theorems rest on the trusted base of the other functions, Talos's semantics of WebAssembly, `Module.initialStore`, and the decoder, and the file theorems on the elaborator `binary_file%`, as [the design notes](../../docs/design.md#scope-of-the-theorem) record.  The byte theorems cover sequences of calls to `atanh`, `asinh`, and `acosh` from a `Ready` store.  The module also exports `alloc`, `release`, `logNear1`, `logCore`, `logWith`, `log1pTail`, `log1p`, `asinhWith`, and `acoshWith`, and a host that calls another export or writes the tables between calls needs a theorem that the action preserves `Ready`.

The module calls Arm's logarithm where fdlibm calls its own, so results can differ from FreeBSD's in the last bit.  Zimmermann's errors for FreeBSD therefore describe a related function with a different logarithm.  The proofs bound the distance from the nearest-even rounding of the real function, and they do not show that any result is correctly rounded.

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
