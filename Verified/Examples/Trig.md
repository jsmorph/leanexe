# The sine and cosine

[The implementation](Trig.lean) exports `sin` and `cos`, ports of fdlibm's `sin`, `cos`, and their kernels as FreeBSD's msun has them [1, 2, 3], with fdlibm's argument reduction below `2^20 · π/2` [4] and a Payne–Hanek reduction in 64-bit word arithmetic above it [7, 8, 9].  The decided bound is one representable step from the nearest-even rounding of the real function, `F64SignedRounding.WithinSteps 1`.  The proof establishes the bound for every finite binary64 input and the exceptional values as exact words, and `TrigTheorem.sin_bytes_accuracy` and `cos_bytes_accuracy` carry both to the decoded WebAssembly module, with `TrigFile.trig_file` connecting that module to the file `build/verified/trig.wasm`.  No accepted theorem depends on an axiom other than `propext`, `Classical.choice`, and `Quot.sound`.  [The tangent](Tan.md) compiles the reduction's Lean definitions into its own module, and [the sine, cosine, and tangent of `π x`](Sinpi.md) compile the kernels into theirs.

## Specification

`sin` and `cos` compute `Real.sin` and `Real.cos` of the value of their argument.  Every finite double is in the domain, and the results lie in `[-1, 1]`, so neither function overflows.  The reduction needs a lower bound on the distance of each double from the multiples of `π/2`, which `TrigDistance.quadrant_distance` gives for every double from 1/2 on.

The bound is stated with [the signed reference](../../LeanExe/ProofKit/F64SignedRounding.lean).  `F64SignedRounding.roundNearestEven y` is the nearest-even binary64 word of `y`, the negation of the nonnegative reference of `|y|` for negative `y`.  `position w` places every word on the ordered line of doubles, with both zeros at 0 and each infinity next to the largest finite value of its sign.  `WithinSteps n y w` states that `w` is not a NaN and that its position differs from that of the reference of `y` by at most `n`.  For finite `x`, `TrigSinCos.sin_within` states `WithinSteps 1 (Real.sin (value x.toBits)) (Trig.sin x).toBits`, and `cos_within` the same for `Real.cos`.

| Input | `sin` | `cos` | Source of the rule | Theorems |
|---|---|---|---|---|
| `+0` | `+0` | `1` | IEEE 754-2019 9.2.1 [10]; C99 F.9.1.5 and F.9.1.6 [11] | `sin_pos_zero`, `cos_pos_zero` |
| `-0` | `-0` | `1` | the same | `sin_neg_zero`, `cos_neg_zero` |
| `±∞` | the canonical NaN | the canonical NaN | IEEE 754-2019 9.2, Table 9.1 (outside the domain, a quiet NaN); C99 F.9.1.5 and F.9.1.6 | `sin_nonfinite`, `cos_nonfinite` |
| NaN | the canonical NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [12] | `sin_nonfinite`, `cos_nonfinite` |
| finite nonzero `x` with `\|x\| < 2^-26` | `x` | | the one-step bound | `sin_within` |

IEEE 754-2019 lists `sin` and `cos` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [10].  The one-step bound is weaker than correct rounding, and the port is not correctly rounded: the accuracy check finds 7,400 results that differ from the nearest double.  The pinned `s_sin.c` and `s_cos.c` state only that "TRIG(x) returns trig(x) nearly rounded" [3].  The theorems say nothing about floating-point exceptions, which the port does not compute.

## Algorithm

Up to `π/4`, as the high-word test `ix ≤ 0x3fe921fb` reads it, the kernels evaluate minimax polynomials: `sin x ≈ x + S1 x³ + ... + S6 x¹³` and `cos x ≈ 1 - x²/2 + C1 x⁴ + ... + C6 x¹⁴` [1, 2].  Above that the reduction writes `x = N π/2 + r` with `|r| ≤ π/4 + 2^-17`, and `N mod 4` selects `sin r`, `cos r`, `-sin r`, or `-cos r`, as the table in `s_sin.c` lists [3].  The reduction returns `r` as an unevaluated sum `y0 + y1`, and the kernels take the tail `y1` to first order: `sin (y0 + y1) ≈ sin y0 + (1 - y0²/2) y1` and `cos (y0 + y1) ≈ cos y0 - y0 y1`.  The cosine kernel computes `w = 1 - z/2` and adds `(1 - w) - z/2`, which recovers the rounding error of `w`.

The reduction has three regimes [4].  Up to `9π/4` the high word of `x` fixes `N` from 1 to 4, and one step subtracts `N · pio2_1` exactly, where `pio2_1` holds the first 33 bits of `π/2`, and then `N · pio2_1t`, the rounded remainder of `π/2`.  This splitting of the constant into a head whose products are exact and a tail is Cody and Waite's reduction [5, 6].  Below `2^20 · π/2`, `N` is the integer nearest to the rounded product of `x` and `invpio2`, 53 bits of `2/π`, found by adding and subtracting `1.5 · 2^52`.  The code subtracts `π/2` in three 33-bit pieces with compensation, in one step good to 85 bits, a second when the first cancels more than 16 bits, and a third when the second cancels more than 49.  The high words near `π/2`, `π`, `3π/2`, and `2π` go to this medium reduction, since the one-step subtraction cancels there.

From `2^20 · π/2` on, the reduction follows Payne and Hanek [7] as K. C. Ng's report describes the method [8].  For `x = m · 2^e` with an integer `m < 2^53`, the bits of `2/π` of weight at least `2^(2-e)` contribute multiples of 4 to `x · 2/π` and can be dropped, and the bits far below contribute less than the needed precision, so a window of `2/π` selected by the exponent gives `x · 2/π` modulo 4.  The port computes that product in 64-bit words, as Go's `math.trigReduce` does [9]: the 192-bit window of `2/π` from bit `e - 1` on times `m` gives `x · 2/π` modulo 4 with 190 bits of fraction, exact to `2^-137`.  The fraction is rounded to the nearer quadrant, normalized, multiplied by `π/2` held as a 128-bit integer, and the top 106 bits of the product become `y0 + y1` by an exact two-sum.

A relative bound on `r` needs a lower bound on `|r|`.  Ng reports that Kahan and McDonald's continued-fraction search found the double closest to a multiple of `π/2`, `6381956970095103 · 2^797`, with fractional quadrant `f ≈ 2.98 · 10^-19 > 2^-62` [8].  The proof replaces that search with `TrigDistance.quadrant_distance`, which proves the bound `2^-63` from 1,025 rational approximations that the kernel checks, one per binade, and the smallest checked bound, `2^-61.54`, falls in the binade of Ng's worst case, which agrees with Ng's `f`.

## Implementation

The sources are FreeBSD msun's `k_sin.c`, `k_cos.c`, `s_sin.c`, `s_cos.c`, and `e_rem_pio2.c` [1, 2, 3, 4], with the table `ipio2` of `k_rem_pio2.c` [13].  Each file carries "Copyright (C) 1993 by Sun Microsystems, Inc." and the notice "Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved".  The module docstring of [the implementation](Trig.lean) names the five files and quotes their notices verbatim, as the notices require.  The port is written in the Verified dialect, the subset of Lean that [the Verified compiler](../README.md) translates to WebAssembly with a correctness theorem.

`verified_compile compiled := [kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window, mulTop, shiftTop, remLarge, remPio2, sinWith, cosWith, sin, cos]` generates the module.  Its functions are `alloc` (0), `release` (1), the listed definitions from 2 on, `sin` (15), and `cos` (16).  The module places the tables `invPi` (20 words) and `halfPi` (2 words) in data segments at addresses 4096 and 4264, and `sinWith` and `cosWith` take them as borrowed parameters, so that no call allocates.  [The tangent](Tan.lean) lists `Trig.remPio2` and the functions it calls in its own `verified_compile`, and [the `π x` functions](Sinpi.lean) list `Trig.kernelSin` and `Trig.kernelCos`, so the reflector compiles the same Lean definitions into those modules.

| C code | Port | Reason |
|---|---|---|
| `__ieee754_rem_pio2 (x, y)` on signed `x`, with a signed count | `remPio2 inv half x.abs`, with the count a word, and the sign of `sin` restored afterwards | `sin (-x) = -sin x` and `cos (-x) = cos x`, so only positive arguments reach the reduction, and the count needs no sign. |
| `x - pio2_1`, `x - 2*pio2_1`, and the other one-step cases, with constant multiples of `pio2_1` and `pio2_1t` | `remSmall x k`, which forms `k * pio2_1` and `k * pio2_1t` at run time | One function serves the four cases, and the products round to the same doubles as C's `2*pio2_1` and the others. |
| `__kernel_rem_pio2`, floating-point arithmetic on 24-bit pieces of `x` and `2/π` with recomputation | `remLarge`, Payne–Hanek in 64-bit words with a fixed 192-bit window, `mul64`, `mulTop`, `clz64`, and `shiftTop` | The word method has a fixed number of steps, reads two constant tables, and needs no loop over pieces.  Ng's analysis bounds its window. |
| `if ((int) x == 0) return x;` in `sin`, and `return 1.0` under the same test in `cos` | `x` and `1.0` without the test | The truncation of `x` is 0 for every `x` the tests guard, and the test exists only to raise the inexact flag, which WebAssembly lacks. |
| `rnint ((double_t) x * invpio2)` and `irint (fn)` | `x * invpio2 + 1.5 · 2^52 - 1.5 · 2^52` and `fn.toUInt64` | `rnint` is that sum in `math_private.h` [14], and `fn` is a nonnegative integer at most `2^20`. |
| `i = j - ((high >> 20) & 0x7ff); if (i > 16)` | `((y0.toBits >>> 52) &&& 0x7ff) + 16 < j` | The same comparison on unsigned exponent fields. |
| `switch (n & 3)` | comparisons of `n &&& 3` | The dialect has no `switch`. |

| Constant | Bits | Value |
|---|---|---|
| `S1` to `S6` | `0xBFC5555555555549`, `0x3F8111111110F8A6`, `0xBF2A01A019C161D5`, `0x3EC71DE357B1FE7D`, `0xBE5AE5E68A2B9CEB`, `0x3DE5D93A5ACFD57C` | the sine kernel's coefficients |
| `C1` to `C6` | `0x3FA555555555554C`, `0xBF56C16C16C15177`, `0x3EFA01A019CB1590`, `0xBE927E4F809C52AD`, `0x3E21EE9EBDB4B1C4`, `0xBDA8FAE9BE8838D4` | the cosine kernel's coefficients |
| `invpio2` | `0x3FE45F306DC9C883` | 53 bits of `2/π` |
| `pio2_1`, `pio2_1t` | `0x3FF921FB54400000`, `0x3DD0B4611A626331` | the first 33 bits of `π/2` and the rounded remainder |
| `pio2_2`, `pio2_2t` | `0x3DD0B4611A600000`, `0x3BA3198A2E037073` | the second 33 bits and the remainder |
| `pio2_3`, `pio2_3t` | `0x3BA3198A2E000000`, `0x397B839A252049C1` | the third 33 bits and the remainder |
| `halfPi` | `0xC90FDAA22168C234`, `0xC4C6628B80DC1CD1` | `π · 2^126`, truncated |
| `invPi` | word 0 is 0, and words 1 to 19 hold 1,216 bits | `2/π`, truncated after 1,216 bits |

The 19 distinct words that `Trig.lean` writes as `Float.ofBits` are words that `k_sin.c`, `k_cos.c`, and `e_rem_pio2.c` print beside their decimal values, and every decimal value in those files rounds to its printed word.  Words 1 to 19 of `invPi` are the first 1,216 bits of the 66 entries of `ipio2` that serve double precision, and they equal `2/π · 2^1216` truncated.  `halfPi` equals `π · 2^126` truncated.  [The journal](../../devnotes.md#2026-10-12-pause-of-the-proof-work) records the comparison of every port's constants with its C source at the pinned commit.  `TrigPi.table_bounds` and `half_bounds` prove the two table relations in the kernel, and `TrigAccuracy.lean` checks them natively against a 2,400-bit `π`.

## Theorems

The theorems are in [the trigonometric theorem module](TrigTheorem.lean), [the accuracy module](TrigSinCos.lean), and [the file module](TrigFile.lean).  `x` is a Lean `Float`, `value x.toBits` its real value, and a word is the `UInt64` bit pattern of a double.  The byte theorems use `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `TrigSinCos.sin_within`, `cos_within` | For finite `x`, `WithinSteps 1` of `Real.sin` and `Real.cos` of `value x.toBits` and the word of `Trig.sin x` and `Trig.cos x`. |
| `TrigTheorem.sin_pos_zero`, `sin_neg_zero` | `sin (+0)` has the bits `0` and `sin (-0)` the bits `0x8000000000000000`. |
| `cos_pos_zero`, `cos_neg_zero` | `cos (±0)` has the bits `0x3FF0000000000000`. |
| `sin_nonfinite`, `cos_nonfinite` | For an infinity or a NaN, the result has the bits `Wasm.IEEE64.canonicalNaN`. |
| `ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant, `invPi` borrowed at 4096, `halfPi` at 4264, and a memory cap of at most 65,535 pages. |
| `sin_entry_call`, `cos_entry_call` | A call of function 15 or 16 from a `Ready` store returns, without a trap, the bits of `Trig.sin x` or `Trig.cos x`, and leaves a `Ready` store in which every heap region keeps its bytes. |
| `sin_export`, `cos_export` | Functions 15 and 16 are exported as `sin` and `cos`. |
| `sin_bytes_accuracy`, `cos_bytes_accuracy` | `Trig.compiled.module` encodes to bytes that decode to it, exports the function, starts in a `Ready` store, and every call from a `Ready` store returns the bits of the Lean function, within one step for finite `x`, and leaves a `Ready` store.  The statements cover every call in a sequence of calls to `sin` and `cos`. |
| `TrigFile.trig_file` | `build/verified/trig.wasm` holds `encode Trig.compiled.module`. |
| `trig_file_decode` | The file decodes to the module of both byte theorems, whose bytes it takes from `And.intro` of the two, so its axiom report covers both. |
| `TrigReduce.remPio2_spec` | For a positive finite double from `0x3FE921FC00000000` on, the reduction returns a count congruent modulo 4 to an integer `N` with `r = x - N π/2`, `2^-63 ≤ \|r\| ≤ π/4 + 2^-17`, `\|y0 + y1 - r\| ≤ \|r\|/2^60`, and `\|y1\| ≤ \|y0\|/2^52`. |
| `TrigNear.sin_near`, `cos_near` | For finite `x`, the word of `Trig.sin x` or `Trig.cos x` is finite and lies within `(71/50) · 2^-53` of `Real.sin` or `Real.cos` of `value x.toBits` (`F64Approx.FApprox`).  The proofs of the Bessel functions use these distances, which are tighter than the one-step bound next to 1. |
| `TrigDistance.quadrant_distance` | For every exponent field from 1022 to 2046 and every significand `m` from `2^52` to `2^53 - 1`, `m · 2^(E-1075) · 2/π` lies more than `2^-63` from every integer. |

Each module ends with `#print axioms` lines.  `tests/verified/run.sh` builds `Verified.Examples.TrigTheorem`, checks `TrigFile.lean` against the `trig.wasm` it has written, and fails unless both file theorems report exactly the three permitted axioms.  In its run of 2026-10-11, which passed that check, every `#print axioms` line of the trigonometric modules reports `propext`, `Classical.choice`, and `Quot.sound` or a subset of them, and `sin_within`, `cos_within`, `sin_bytes_accuracy`, and `cos_bytes_accuracy` report all three, as [the journal](../../devnotes.md#2026-10-11-integration-of-the-sine-cosine-and-log2-theorems) also records.  `TrigNear.sin_near` and `cos_near` report the same three axioms.

## Proof

### Modules

The table groups the proof modules in `Verified/Examples/` by stage.  `TrigFile` adds the file theorem.  [The root `Verified` import](../../Verified.lean) includes `TrigTheorem`, and `tests/verified/run.sh` builds it before checking `TrigFile`.

| Stage | Modules | Content |
|---|---|---|
| `π` and its tables | `TrigPi`, `TrigWindows` | `π` within `2^-1270` from Machin's formula, the two tables, and the windows of `invPi` for every exponent field from 1043 to 2046. |
| Kernel polynomials | `TrigKernelPoly`, `TrigKernelWide` | The polynomials against `sin` and `cos` on `\|x\| ≤ 0.7854` and on `\|x\| ≤ 0.78541`. |
| Kernel rounding | `TrigApprox`, `TrigKernelWords`, `TrigSinTail`, `TrigSinDirect`, `TrigKernelSpec`, `TrigCosKernel` | Error tracking with magnitude bounds, the kernels on words, and the evaluated kernels against `sin (x + y)` and `cos (x + y)`. |
| Distance | `TrigDistance` | `quadrant_distance`. |
| Large reduction | `TrigWords`, `TrigLargeInt`, `TrigLargeFloat`, `TrigLarge`, `TrigLargeSpec` | The word routines, the integer stages, the exact two-sum, and `remLarge_spec`. |
| Small and medium reductions | `TrigSmall`, `TrigMediumConst`, `TrigMediumFn`, `TrigMediumCases`, `TrigMediumA`, `TrigMediumB`, `TrigMediumC`, `TrigMedium` | The one-step reduction for `k` from 1 to 4, the six pieces of `π/2`, the count, and the three outcomes of the medium reduction. |
| Assembly | `TrigReduce`, `TrigStep`, `TrigQuadrant`, `TrigSinCos`, `TrigTheorem` | `remPio2_spec`, the final steps, the quadrants, `sin_within`, `cos_within`, and the byte theorems. |

### Reduction

Every branch of `remPio2` satisfies `TrigReduce.Reduced`: `y0 + y1` lies within `|r|/2^60` of `r = x - N π/2`.  `TrigSmall.remSmallW_spec` shows that `k · pio2_1` and `x - k · pio2_1` are exact and that `y0 + y1` equals `z - fl (k · pio2_1t)`, so the result lies within `2^-60 |r|` of `r` for `2^-22 ≤ |r| ≤ π/4 + 2^-17`, with `pio2_1 + pio2_1t` within `2^-86` of `π/2` (`pio2_checked`).  `TrigMediumFn.fn_spec` shows that the count is the integer `N` within `1/2 + 2^-30` of `x · 2/π`, and the pieces of `π/2` have at most 32 significant bits (`TrigMediumConst.consts_checked`), so their products with `N ≤ 2^20` are exact.  `TrigMediumConst.comp_step` with `TrigNearest.small_two_diff` shows that fdlibm's compensated step `w' = A - ((t - r) - w)` loses nothing but the rounding of `w'`.  The relative bound alone could not show that `(t - r) - w` is exact when `w` lies far below the last place of `t`, which is why `TrigNearest` proves that a rounded sum is a nearest word.

The large reduction is split into five stages that `TrigLargeInt.remLarge_eq` composes.  `TrigWindows.windows_eq` checks in the kernel, for every exponent field from 1043 to 2046, that the three words `remLarge` reads are the 192 bits of `2/π` from the right position.  `TrigWords` gives natural-number specifications of `mul64`, `mulTop`, `clz64`, and `shiftTop`, `TrigLarge` bounds the product and the cut into 53-bit words, and `TrigLargeFloat` shows that the final two-sum is exact.  `TrigLargeSpec.remLarge_spec` concludes `|y0 + y1 - r| ≤ |r|/2^72`, `2^-63 ≤ |r| ≤ π/4 + 2^-134`, and `|y1| ≤ |y0|/2^53`.

`TrigDistance.quadrant_distance` is the lower bound on `|r|` that both the medium and the large reductions use.  For each exponent field `E` from 1022 to 2046, a pair `(p, q)` with `gcd p q = 1` and `q ≥ 2^53` gives a rational approximation to `β = 2^(E-1075) · invPi` modulo 1, and the kernel checks `1/q - 2^53 |β - p/q| > 2^-62`.  Since `q` cannot divide `m p` for `0 < m < q`, `|m p/q - n| ≥ 1/q` for every integer `n`, so `|m β - n| > 2^-62` for every significand `m`.  `invPi` lies within `2^-1216` of `2/π`, so `x · 2/π` lies more than `2^-63` from every integer for every double `x` from 1/2 on.  These fractions are convergents of the continued fractions of the binades' `β`, computed offline with Python and checked by `decide +kernel` in `certs_checked`, so the offline program is not trusted.

The one-step branches accept more than `|r| ≤ π/4`: the high-word thresholds `0x4015fdbc` and `0x401c463b` lie above `7π/4` and `9π/4`, so `|r|` reaches `π/4 + 4.79 · 10^-6` for `k = 4`.  The kernel bounds of `TrigKernelPoly` hold for `|x| ≤ 0.7854`, and `TrigKernelWide` reruns their checks on `|x| ≤ 0.78541` with the same allowances, since the largest errors lie inside `[0, 0.7854]`.  `cos_final` and `sin_final` therefore take reduced arguments up to `0.78541` in magnitude.

### Error budget

Let `u = 2^-53` and `X = |y0|`.  The polynomial bounds compare each kernel polynomial with the Taylor polynomial of degree 11 in `x²` by `PolyBound.check`, which the kernel evaluates, and add the Taylor remainder of `TaylorRemainder`.  The rounding analysis tracks each operation with `F64ErrorTrack.Approx` and a bound on the operation's exact value (`TrigApprox.AB`), and the sine kernel's bounds are polynomials in `X`, so the error keeps its relative size for small arguments.  The sampled errors in the table are from [the journal](../../devnotes.md#2026-10-10-polynomial-bounds-and-taylor-remainders-track-poly-minideb2).

| Stage | Bound | Lemma |
|---|---|---|
| Sine polynomial against `sin x`, relative to `x` | `(65/64) · 2^-58` (fdlibm states `2^-58`, and the largest sampled error is `2^-57.994` at `x ≈ 0.765`) | `TrigKernelWide.sin_kernel_error_wide` |
| Cosine polynomial against `cos x` | `2^-59` (the largest sampled error is `2^-59.83`) | `cos_kernel_error_wide` |
| Evaluated sine kernel, before its last rounding, against `sin (y0 + y1)`, with the reduction's tail | `u (33/40 X³ + X/30)` | `TrigKernelSpec.sinTail_spec`, `sinDirect_spec` |
| Evaluated cosine kernel, its last rounding included | `(7/5) u`, of which the omitted term `y1 (sin y0 - y0)` contributes up to `0.127 u` | `TrigCosKernel.cos_spec` |
| Reduction | `\|r\|/2^60` | `TrigReduce.remPio2_spec` |

The final steps use two criteria.  `F64RelativeStep.within_one_relative` accepts a word within `(11/8) u |y|` of `y`, which leaves `(3/8) u` beside the last rounding, and `F64UnitStep.unit_step` accepts a word within one and a half spacings of a number of magnitude from `1/2 + 2^-50` to 1, where the spacing below 1 is `u`.

| Inputs | Path | Bound | Allowance | Theorem |
|---|---|---|---|---|
| `sin`, `0 < \|x\| < 2^-26` | the result is `x` | `\|sin x - x\| ≤ \|x\|³/6 < 2^-54 \|x\|` | `2^-54` relative to the word | `F64SelfStep.self_step` |
| `sin`, `\|r\| ≤ 0.54` | kernel, direct or reduced | `0.31 u \|sin r\|` before the last rounding | `(3/8) u \|sin r\|` | `TrigStep.sin_final` |
| `sin`, `0.54 < \|r\| ≤ 0.78541` | kernel, direct or reduced | `1.44 u`, the last rounding included | `1.5 u` | `TrigStep.sin_final` through `unit_step` |
| `cos`, `\|x\| < 0x3E46A09E00000000` | the result is 1 | `1 - cos x ≤ x²/2 ≤ u` | `1.5 u` | `TrigSinCos.cos_within` through `unit_step` |
| `cos`, otherwise | kernel, direct or reduced | `(7/5) u` plus the reduction's `2^-59 \|r\|`, below `1.42 u` | `1.5 u` | `TrigStep.cos_final` |

The sine kernel's bound reaches `0.44 u` at `|r| = π/4`, above the `(3/8) u` of the relative criterion, so `sin_final` splits at `|r| = 0.54`, where `sin r` exceeds 1/2 and the binade criterion applies.  The margins are about 17 percent of the allowance below 0.54, 4 percent above it, and 5 percent for the cosine.  `TrigQuadrant.reduced_kernels` combines `Reduced` with the kernels, `quadrant` turns `sin r` and `cos r` into `sin |x|` and `cos |x|` by `N mod 4`, and `TrigSinCos.neg_within` negates the result of `sin` for a negative `x`.

### Shared modules

The proof uses ProofKit, including the arithmetic chain of `F64Add`, `F64Mul`, `F64Div`, `F32*`, and `F64Bits` that proves Lean's float operations equal to Talos's `IEEE64` functions.  The modules specific to the analysis are [the polynomial bound checked by the kernel](../../LeanExe/ProofKit/PolyBound.lean), [Taylor remainders of `sin`, `cos`, and other series](../../LeanExe/ProofKit/TaylorRemainder.lean), [error tracking of operations](../../LeanExe/ProofKit/F64ErrorTrack.lean), [the relative one-step criterion](../../LeanExe/ProofKit/F64RelativeStep.lean), [one step near 1](../../LeanExe/ProofKit/F64UnitStep.lean), [one step from a word to itself](../../LeanExe/ProofKit/F64SelfStep.lean), [exact sums and differences stated with values](../../LeanExe/ProofKit/F64ValueExact.lean), [the nearest property of rounded sums and fdlibm's compensated difference](../../LeanExe/ProofKit/F64SignedNearestSum.lean), [one step against the full reference](../../LeanExe/ProofKit/F64FullStep.lean), [the signed reference](../../LeanExe/ProofKit/F64SignedRounding.lean), [exact products by powers of two](../../LeanExe/ProofKit/F64ExactProduct.lean), [conversions between words and floats](../../LeanExe/ProofKit/F64Convert.lean), [grid exactness](../../LeanExe/ProofKit/F64GridExact.lean), [exponent, magnitude, and sign](../../LeanExe/ProofKit/F64Magnitude.lean), and [borrowed tables kept across calls](../../LeanExe/ProofKit/BorrowedKept.lean).  `TrigPi` takes Machin's formula from Mathlib's `Real.four_mul_arctan_inv_5_sub_arctan_inv_239` [15] and proves the alternating series bound of the arctangent.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| Machin's partial sums with 275 and 82 terms bound `π` within `2^-1270`, and the two tables against those bounds | `TrigPi.checked`, `tableNum_eq`, `halfNum_eq` |
| The 1,025 rational approximations and their count | `TrigDistance.certs_checked`, `certs_length` |
| The windows of `invPi` for exponent fields 1043 to 2046 | `TrigWindows.windows_eq` |
| `pio2_1 + pio2_1t` within `2^-86` of `π/2`, and the sums of the six pieces within `2^-121` and `2^-157` | `TrigSmall.pio2_checked`, `TrigMediumConst.pio2_sums_checked` |
| The fields of the six pieces of `π/2` | `TrigMediumConst.consts_checked` |
| The sine and cosine polynomials against their Taylor polynomials, by bisection to depth 14 | `TrigKernelPoly.sin_check`, `cos_check`, `TrigKernelWide.sin_check_wide`, `cos_check_wide` |
| Functions 15 and 16 are exported as `sin` and `cos` | `TrigTheorem.sin_export`, `cos_export` |
| The file's bytes equal the encoder's | `TrigFile.trig_file` |

### History

Recursion-depth failures in `omega`, `positivity`, `congr`, `generalize`, and `rw` came from powers such as `2^1088` in the context, and lemmas stated with a named variable and proved by `subst` avoid the unifier's comparison of large literals ([the reduction section](../../devnotes.md#2026-10-10-argument-reduction-of-sin-and-cos-track-trig-minideb1)).  A first `rfl` proof of `remLarge_eq` timed out, and the version with pattern-matching `let` and the stage definitions unfolded takes under a second.  `TrigKernelWide` exists because the reduction's one-step branches exceed `π/4`, beyond the range of `TrigKernelPoly` ([the kernel section](../../devnotes.md#2026-10-11-the-kernels-and-the-final-step-of-sin-and-cos-track-trig)).  `trig_file_decode` first took its bytes from `sin_bytes_accuracy` alone, so its axiom report did not cover `cos_bytes_accuracy`, and it now takes them from both ([the journal](../../devnotes.md#2026-10-11-integration-of-the-sine-cosine-and-log2-theorems)).

## Tests

[The accuracy check](TrigAccuracy.lean) compares `Trig.sin` and `Trig.cos` natively with the doubles nearest to `sin x` and `cos x` from [the integer reference](Reference.lean), which reduces with a 2,400-bit `π` from Machin's formula and sums the Taylor series at 300 bits, and it fails at the first result more than one step away.  It first compares the words of `invPi` and `halfPi` with `2/π` and `π/2` from the same `π`.  Its 180,031 arguments are 100,000 hashed values with exponents from `2^-30` to `2^1023` and both signs, 20,001 evenly spaced values from 0 to 100, the doubles at and next to the rounded `k · π/2` for `k` from 1 to 20,000, five hard arguments and their negatives (`6381956970095103 · 2^797`, `1647100`, `10^22`, `10^300`, and the largest finite double), and the 20 inputs of `WorstCases.sin` and `WorstCases.cos`.  Those 20 are the double-precision inputs that give the largest known errors of `sin` and `cos` in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [16], whose Table 3 lists 0.831 and 0.834 units for FreeBSD 15.1 and 0.516 for GNU libc 2.44.

In a run of `tests/verified/run.sh`, all 360,062 results, those of `sin` and `cos` at each argument, lie within one step of the reference, and 7,400 of them differ from it.  The largest measured distance therefore equals the proved bound.  The C library of the test run, glibc 2.41, lies within 8 steps, with 315 results unequal to the reference, and [the journal](../../devnotes.md#2026-10-11-zimmermanns-inputs-in-the-accuracy-checks) traces the 8 steps to its `cos` at `6381956970095103 · 2^797`, 7.95 units from a 1,200-digit computation.  The reference's docstrings state its truncation errors, below `2^-231` relative for every value the check compares, and no theorem proves them.

## Limits

The theorems are about Talos's semantics of WebAssembly.  The Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode` are trusted, as [the design notes](../../docs/design.md#scope-of-the-theorem) record, and the file theorem trusts the elaborator `binary_file%`, which reads `trig.wasm`.  Talos implements the deterministic profile, in which every NaN result is canonical [12], and an engine outside that profile, such as a browser, may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, and every NaN `Float` has the canonical bits (`F64Bits.toBits_canonical`), so the theorems cover only the canonical NaN among the NaN words a WebAssembly caller can pass.  For another NaN word the compiled code reaches `x - x`, which returns the canonical NaN in Talos, but no theorem states it.  The byte theorems cover sequences of calls to `sin` and `cos` only: the module also exports `alloc`, `release`, the reduction and kernel functions, `sinWith`, `cosWith`, its memory, and the allocation counters, and a host that calls another export or writes the tables between calls needs a theorem that the action preserves `Ready`.  `quadrant_distance` covers doubles from 1/2 on, which suffices because the reduction runs only above `π/4`.

## References

1. FreeBSD, msun, [`lib/msun/src/k_sin.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_sin.c).  Copyright (C) 1993 by Sun Microsystems, Inc., with the notice quoted above.  It states the polynomial's error relative to `x` as at most `2^-58`.
2. FreeBSD, msun, [`k_cos.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_cos.c), same commit and notice.
3. FreeBSD, msun, [`s_sin.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_sin.c) and [`s_cos.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_cos.c), same commit and notice: the quadrant table and "TRIG(x) returns trig(x) nearly rounded".
4. FreeBSD, msun, [`e_rem_pio2.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_rem_pio2.c), same commit and notice, optimized by Bruce D. Evans.
5. W. J. Cody, Jr. and W. Waite, *Software Manual for the Elementary Functions*, Prentice-Hall, 1980.  The book was not consulted.  Its identity is confirmed by the review in *SIAM Review* 24(1):91–93, 1982, [doi:10.1137/1024023](https://doi.org/10.1137/1024023), and the method by reference 6.
6. S. Boldo, M. Daumas, and R.-C. Li, "Formally Verified Argument Reduction with a Fused Multiply-Add", *IEEE Transactions on Computers* 58(8):1139–1145, 2009, [doi:10.1109/TC.2008.216](https://doi.org/10.1109/TC.2008.216); preprint [arXiv:0708.3722](https://arxiv.org/abs/0708.3722).  The paper describes Cody and Waite's technique as a first floating-point number `C1` approximating the constant, with `z · C1` exact, and a second `C2` holding the next bits.
7. M. H. Payne and R. N. Hanek, "Radian reduction for trigonometric functions", *ACM SIGNUM Newsletter* 18(1):19–24, January 1983, [doi:10.1145/1057600.1057602](https://doi.org/10.1145/1057600.1057602).  Crossref confirms the bibliographic data.  The publisher's site refused automated access, so the description above rests on reference 8, which credits the method to Payne and Hanek and to Bob Corbett.
8. K. C. Ng and the members of the FP group of SunPro, ["Argument Reduction for Huge Arguments: Good to the Last Bit"](https://userpages.cs.umbc.edu/phatak/645/supl/Ng-ArgReduction.pdf), works in progress, March 24, 1992, in the typeset version by Derek O'Connor (2006).  Sections 2.3 to 2.5 give the closest double to a multiple of `π/2`, the bound `f > 2^-62`, and the window of `2/π`.
9. The Go Authors, [`src/math/trig_reduce.go`](https://github.com/golang/go/blob/go1.23.0/src/math/trig_reduce.go), Go 1.23.0, BSD-style license: Payne–Hanek reduction by `π/4` in 64-bit integer arithmetic, citing reference 8.  The docstring of `Trig.remLarge` names this function but no Go version, and the port reduces by `π/2` with its own window.
10. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clause 9.2 with Table 9.1 (domains and exceptions) and clause 9.2.1 (special values).
11. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.1.5, and F.9.1.6, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
12. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
13. FreeBSD, msun, [`k_rem_pio2.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_rem_pio2.c), same commit and notice: the table `ipio2` of `2/π` in 24-bit pieces.
14. FreeBSD, msun, [`math_private.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/math_private.h), same commit: `rnint`.
15. The Mathlib Community, Mathlib, [`Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean), `Real.four_mul_arctan_inv_5_sub_arctan_inv_239`.
16. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
