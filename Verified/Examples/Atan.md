# The arctangent functions

[The implementation](Atan.lean) exports `atan` and `atan2`, ports of fdlibm's `s_atan.c` and `e_atan2.c` as FreeBSD's msun has them [1].  The decided bounds are one representable step from the nearest-even rounding of `arctan x` for `atan` and two steps from that of the argument of `x + iy` for `atan2`.  `atan2` has the larger bound because an exact model of the port lies two steps from the reference at an input of Zimmermann's report [9], as [the decisions after the review of the worst inputs](../../devnotes.md#2026-10-10-decisions-after-the-review-of-gamma-bessel-and-worst-inputs) record, and the accuracy check finds two steps at two input pairs of that report.  `transcendentals` proves both bounds for every finite input in the domain and the exceptional values as words, except `atan2 (y, ±0)`, which it proves within two steps, and NaN arguments of `atan2`, for which no theorem exists.  `AtanBytes.atan_module_accuracy` carries both functions to the decoded WebAssembly module, with `AtanFile.atan_file` connecting that module to `build/verified/atan.wasm`.  No accepted theorem depends on an axiom other than `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`atan` computes `Real.arctan a` for the value `a` of its argument, and every double is in its domain.  `atan2 y x` computes `Complex.arg (x + y i)` [8], the angle in `(-π, π]` of the point `(x, y)`, which IEEE 754-2019 defines as the result of `atan2` in clause 9.2.1 [5].  The bounds are `F64SignedRounding.WithinSteps 1 (Real.arctan a) w` and `WithinSteps 2 (Complex.arg (x + y i)) w`, with `WithinSteps` from [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean): `w` is not a NaN, and its position on the ordered line of doubles, with both zeros at 0, lies within `n` of the position of the nearest-even rounding.  The theorem for `atan2` requires finite `x`, finite `y`, and `y ≠ 0`.  `Complex.arg` gives `π` for `y = ±0` and `x < 0`, and the code returns `+π` for `y = +0` and `-π` for `y = -0`, as IEEE 754 and C99 require, so the signed zeros of `y` have their own theorems.

| Function and input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `atan (±0)` | `±0` | IEEE 754-2019 9.2.1 [5]; C99 F.9.1.3 [6] | `atan_zero`, `atan_neg_zero` |
| `atan (±∞)` | `±π/2` rounded: `0x3FF921FB54442D18` and `0xBFF921FB54442D18` | IEEE 754-2019 9.2.1; C99 F.9.1.3 | `atan_pos_inf`, `atan_neg_inf` |
| `atan` of NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [7] | `atan_nan` |
| `atan2 (±0, x)`, `x` not NaN | `±0` when the sign bit of `x` is clear, `±π` rounded when it is set, `x = -0` included | IEEE 754-2019 9.2.1; C99 F.9.1.4 | `atan2_zero` |
| `atan2 (±∞, x)`, finite `x` | `±π/2` rounded | IEEE 754-2019 9.2.1; C99 F.9.1.4 | `atan2_inf_y` |
| `atan2 (y, ±∞)`, finite nonzero `y` | `±0` for `+∞`, `±π` rounded for `-∞`, with the sign of `y` | IEEE 754-2019 9.2.1; C99 F.9.1.4 | `atan2_inf_x` |
| `atan2 (±∞, ±∞)` | `±π/4` and `±3π/4` rounded | IEEE 754-2019 9.2.1; C99 F.9.1.4 | `atan2_inf_both` |
| `atan2` with a NaN argument | the canonical NaN in Talos, from `x + y` | IEEE 754-2019 9.2; C99 F.9 paragraph 11 | `atan2_nan` |
| `atan2 (y, ±0)`, finite nonzero `y` | `±π/2` rounded | IEEE 754-2019 9.2.1; C99 F.9.1.4 | within two steps, `AtanTwoTheorem.xzero_case` |

The rounded constants are the words `0x400921FB54442D18` (`π`), `0x3FF921FB54442D18` (`π/2`), `0x3FE921FB54442D18` (`π/4`), and `0x4002D97C7F3321D2` (`3π/4`), with the sign bit set for the negative results, and each is the nearest double to its value.  IEEE 754-2019 recommends both operations in clause 9.2, where a conforming implementation rounds correctly [5].  fdlibm states no error bound for either function, and the theorems say nothing about floating-point exceptions, which the port does not compute.

## Algorithm

`atan` reduces `|x|` to an argument `t` with `|t| < 7/16` by the addition formula of DLMF 4.24.15 [4], `arctan u - arctan c = arctan ((u - c)/(1 + uc))`, which holds for the principal values here since `u` and `c` are positive.  `c` is one of `1/2`, `1`, `3/2`, and `∞`, and for `c = ∞` the formula reads `arctan u = π/2 + arctan (-1/u)` for `u > 0`.  The intervals come from the source's comment and code [1].

| `\|x\|` | Reduced argument `t` | Result |
|---|---|---|
| below `2^-27` | none | `x` |
| `[2^-27, 7/16)` | `x` | `t - t (s1 + s2)` |
| `[7/16, 11/16)` | `(2\|x\| - 1)/(2 + \|x\|)` | `arctan (1/2) + arctan t` |
| `[11/16, 19/16)` | `(\|x\| - 1)/(\|x\| + 1)` | `π/4 + arctan t` |
| `[19/16, 39/16)` | `(\|x\| - 1.5)/(1 + 1.5 \|x\|)` | `arctan (3/2) + arctan t` |
| `[39/16, 2^66)` | `-1/\|x\|` | `π/2 + arctan t` |
| from `2^66` | none | `±π/2` rounded |

The polynomial is `aT0 z + ⋯ + aT10 z^11` in `z = t²`, split into the parts `s1` and `s2` with the even- and odd-indexed coefficients, each a polynomial in `w = z²`, and the series it approximates is DLMF 4.24.3 [4].  Each constant `arctan c` is stored as a sum `atanhi + atanlo`, and the result `atanhi - ((t (s1 + s2) - atanlo) - t)` adds the large term last.  The doubling `2|x|` and the subtractions `2|x| - 1`, `|x| - 1`, and `|x| - 1.5` are exact, the subtractions by Sterbenz's lemma, and the other operations of the reduction round once each.

`atan2` returns `atan y` for `x = 1`, handles the zeros and infinities with constants, and otherwise compares the exponents of `y` and `x` through `k = (iy - ix) >> 20`, the shifted difference of their high words.  For `k > 60`, `|y/x| > 2^60` and the result is `±π/2`.  For `x < 0` and `k < -60` the result is `±π`.  Otherwise the code computes `z = atan |y/x|` and places it in the quadrant of `(x, y)`: `z` and `-z` for `x > 0`, and `π - (z - π_lo)` and `(z - π_lo) - π` for `x < 0`, with `π` in two parts.  The quotient `y/x` rounds before `atan` sees it, with a relative error up to `2^-53`, and the resulting change of `arctan` reaches 0.96 spacings of the result's binade in the cases of the table under `atan2` below.  That change, added to the error of `atan`, is why `atan2` has a bound of two steps where `atan` stays within one.

## Implementation

The sources are `lib/msun/src/s_atan.c` and `lib/msun/src/e_atan2.c` of FreeBSD at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1], each "Copyright (C) 1993 by Sun Microsystems, Inc." with the notice "Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved".  The module docstring of [the implementation](Atan.lean) names the two files and the commit and quotes their notices verbatim, as the notices require.  fdlibm is Sun's "Freely Distributable LIBM" [3].  The port follows the dialect of the Verified compiler as [the exponential document](Exp.md#implementation) describes: `verified_compile compiled := [atan, atan2]` generates a module whose functions are `alloc` (0), `release` (1), `atan` (2), and `atan2` (3), every named constant is `Float.ofBits` of its bit pattern, and the module reads no table.  The WebAssembly entry of `atan2` takes `y` and then `x`, as C's `atan2 (y, x)` does.

| C code | Port | Reason |
|---|---|---|
| `id = -1` for the direct polynomial, and the arrays `atanhi[id]`, `atanlo[id]` | `id = 4`, with the entries selected by comparisons | The comparisons select the same entries, and the module needs no table. |
| The volatile read of `atanlo[3]` in `s_atan.c`, and the volatile `tiny` and `pi_lo` of `e_atan2.c` | their values | The qualifier prevents constant folding, and the dialect has no such qualifier. |
| `huge + x > one`, `pi + tiny`, `pi_o_2 + tiny`, and the other sums with `tiny` | kept as computed | They serve only to raise inexact.  The test holds for every `\|x\| < 1` (`AtanTheorem.huge_gt`), and the sums equal the rounded constants (`AtanTwoBits.half_bits`, `half_neg_bits`, and the words of `AtanTwoSpecial`). |
| Signed `int32_t` high words | `UInt64` words with the sign bit tested apart | The dialect has no signed integers. |
| `k = (iy - ix) >> 20`, an arithmetic shift | the shift of the 64-bit two's complement difference, with the top 20 bits filled when it is negative | The same value as a two's complement word, and `k > 60` and `k < -60` test the sign bit first. |
| `nan_mix (x, y)`, a `long double` sum in `math_private.h` [2] | `x + y` | Both give a NaN, which is the canonical NaN in the deterministic profile. |
| `switch (m)` | comparisons on `m` | The dialect has no `switch`. |

| Constant | Bits | Constant | Bits |
|---|---|---|---|
| `atanhi[0]` | `0x3FDDAC670561BB4F` | `atanlo[0]` | `0x3C7A2B7F222F65E2` |
| `atanhi[1]`, `pi_o_4` | `0x3FE921FB54442D18` | `atanlo[1]` | `0x3C81A62633145C07` |
| `atanhi[2]` | `0x3FEF730BD281F69B` | `atanlo[2]` | `0x3C7007887AF0CBBD` |
| `atanhi[3]`, `pi_o_2` | `0x3FF921FB54442D18` | `atanlo[3]` | `0x3C91A62633145C07` |
| `pi` | `0x400921FB54442D18` | `pi_lo` | `0x3CA1A62633145C07` |
| `aT[0]` to `aT[3]` | `0x3FD555555555550D`, `0xBFC999999998EBC4`, `0x3FC24924920083FF`, `0xBFBC71C6FE231671` | `aT[4]` to `aT[7]` | `0x3FB745CDC54C206E`, `0xBFB3B0F2AF749A6D`, `0x3FB10D66A0D03D51`, `0xBFADDE2D52DEFD9A` |
| `aT[8]` to `aT[10]` | `0x3FA97B4B24760DEB`, `0xBFA2B4442C6A6C2F`, `0x3F90AD3AE322DA11` | `huge`, `tiny` | `0x7E37E43C8800759C` (`1.0e300`), `0x01A56E1FC2F8F359` (`1.0e-300`) |

`s_atan.c` prints 19 constants and `e_atan2.c` 4 beside their bits, and each decimal value rounds to its printed word, as [the ports' journal section](../../devnotes.md#2026-10-10-ports-of-log1p-atan-atan2-asin-acos-and-tan) records.  The 25 `Float.ofBits` words of `Atan.lean` agree with the pinned sources: the 23 words with printed bits match, and `huge` and `tiny` are the nearest doubles to `1.0e300` and `1.0e-300`, a comparison that [the journal](../../devnotes.md#2026-10-12-pause-of-the-proof-work) records for every port.  The kernel bound restates `aT[0]` to `aT[10]` as `PolyBound.ratOfWord` of the same words.

## Theorems

The theorems are in [the `atan` theorem](AtanTheorem.lean), [its exceptional values](AtanTheoremSpecial.lean), [the `atan2` theorem](AtanTwoTheorem.lean), [its exceptional values](AtanTwoSpecial.lean), [its NaN results](AtanTwoNaN.lean), [the byte theorems](AtanBytes.lean), and [the file theorem](AtanFile.lean).  `x` and `y` are Lean `Float`s, `a = value x.toBits`, and `b = value y.toBits`.  The byte theorems use `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `AtanTheorem.atan_within_one` | For finite `x`, `WithinSteps 1 (Real.arctan a) (Atan.atan x).toBits`. |
| `AtanTheoremSpecial.atan_zero`, `atan_neg_zero` | `±0` give `±0`. |
| `atan_pos_inf`, `atan_neg_inf` | `+∞` gives `0x3FF921FB54442D18` and `-∞` gives `0xBFF921FB54442D18`, each `WithinSteps 0` of `±π/2`. |
| `atan_nan` | A NaN gives `Wasm.IEEE64.canonicalNaN`. |
| `AtanTwoTheorem.atan2_within_two` | For finite `y` and `x` with `b ≠ 0`, `WithinSteps 2 (Complex.arg (a + b i)) (Atan.atan2 y x).toBits`. |
| `AtanTwoSpecial.atan2_zero`, `atan2_inf_y`, `atan2_inf_x`, `atan2_inf_both` | The words of the zero and infinite cases of the table above. |
| `AtanTwoNaN.atan2_nan` | When `y` or `x` is a NaN, `(Atan.atan2 y x).toBits` is `Wasm.IEEE64.canonicalNaN`. |
| `AtanBytes.ready_initial` | The initial store satisfies `Ready`: the allocator invariant and a memory cap of at most 65,535 pages. |
| `AtanBytes.atan_entry_call`, `atan2_entry_call` | A call of function 2 or 3 from a `Ready` store returns, without a trap, the bits of the Lean function, and leaves a `Ready` store in which every heap region keeps its bytes. |
| `AtanBytes.atan_bytes_accuracy`, `atan2_bytes_accuracy` | `Atan.compiled.module` encodes to bytes that decode to it, exports the function, starts in a `Ready` store, and every call from a `Ready` store returns the bits of the Lean function, within the decided bound on the domain of the accuracy theorem, and leaves a `Ready` store. |
| `AtanBytes.atan_module_accuracy` | The conjunction of the two byte theorems. |
| `AtanFile.atan_file`, `atan_file_decode` | `build/verified/atan.wasm` holds `encode Atan.compiled.module`, and the file decodes to the module of `atan_module_accuracy`. |

`atan_file_decode` takes its bytes from `atan_module_accuracy`, so its axiom report covers both byte theorems, which `tests/verified/run.sh` requires because it reads only the two reports of the file module.  The logs under `build/transcendentals/` of the worktree `lt-poly` on the build host record the first builds with the permitted axioms: `atan_within_one` in `arc-atan-main-5.log`, `atan2_within_two` and the byte theorems in `arc-mix-18.log`, the `atan2` exceptional values in `arc-mix-19.log`, and the file theorems in `arc-file-3.log` ([the track's journal](../../devnotes.md#2026-10-10-full-theorems-for-log1p-atan-atan2-asin-and-acos-track-arc)).  In the primary checkout on the build host, the integration build `opus-merge-arc-1.log` printed the three axioms for the accuracy, exceptional-value, and byte theorems, and the run `opus-verified-tests-12.log` first passed the file check ([the integration](../../devnotes.md#2026-10-12-integration-of-expm1-tanh-erf-log1p-atan-atan2-asin-and-acos-first-push)).

`tests/verified/run.sh` builds `Verified.Examples.AtanBytes` and checks `AtanFile.lean` against the `atan.wasm` that it writes earlier in the same run.  Its latest run in the primary checkout, `opus-verified-tests-14.log` of 2026-10-11, passed that check and printed `[propext, Classical.choice, Quot.sound]` for `atan_within_one`, `atan2_within_two`, the `atan` exceptional values, and every declaration of `AtanBytes`.  `AtanBytes` does not import `AtanTwoSpecial`, which [the root `Verified` import](../../Verified.lean) includes, so `lake build Verified` checks the `atan2` exceptional values, and the latest integration build, `opus-merge-sinh-1.log`, printed the same three axioms for them.

## Proof

### Modules

The table lists the proof modules in dependency order.  The `atan` chain ends in `AtanTheorem` and `AtanTheoremSpecial`, on which the `atan2` chain builds from `AtanTwoBranches` on.  `AtanTwoSpecial` imports `AtanTwoBits`, `AtanBytes` imports `AtanTheoremSpecial` and `AtanTwoTheorem`, and `AtanFile` imports `AtanBytes`.

| Module | Content |
|---|---|
| `AtanKernelPoly` | The kernel bound `atan_kernel_error`. |
| `AtanTheoremPoly` | The error chain of `t (s1 + s2)`: within `2.0 · 2^-53 s³` of `t · polyS t` for `\|t\| ≤ s ≤ 7/16`. |
| `AtanTheoremBranches` | The branches of `atan` as equations on the high word. |
| `AtanTheoremTail` | The errors of `x - x (s1 + s2)` and of `hi - ((t (s1 + s2) - lo) - t)` as functions of the case bounds. |
| `AtanTheoremReduce` | The reduced arguments: the exact doubling and subtractions and the rounded operations. |
| `AtanTheoremConst` | `atanhi + atanlo` within `2^-64` of `arctan (1/2)`, `π/4`, `arctan (3/2)`, and `π/2`, and `arctan` 1-Lipschitz. |
| `AtanTheoremCases` | The eight reduced cases within one step. |
| `AtanTheoremSmall` | `\|x\| < 7/16`: below `2^-27`, from `2^-27` to `1/4`, and two pieces up to `7/16`. |
| `AtanTheorem`, `AtanTheoremSpecial` | `atan_within_one` and the exceptional values. |
| `AtanTwoBranches`, `AtanTwoQuot`, `AtanTwoErr`, `AtanTwoAtan` | The branches of `atan2`, the rounded quotient `q` within `2^-53 Q + 2^-1075` of `Q = \|y/x\|`, the change of `arctan` between them, and `atan_good` for every branch of `atan` at `q`. |
| `AtanTwoArg`, `AtanTwoBits`, `AtanTwoTheorem` | `Complex.arg` through `arctan (y/x)`, the word tests of `atan2`, and `atan2_within_two`. |
| `AtanTwoSpecial`, `AtanTwoNaN`, `AtanBytes`, `AtanFile` | Exceptional values, the NaN results of `atan2`, byte theorems, and the file theorem. |

### Kernel bound

`AtanKernelPoly.atan_kernel_error` states `|arctan x - x (1 - aT0 z - ⋯ - aT10 z^11)| ≤ |x| · (5/8) · 2^-57` for `|x| ≤ 7/16` and `z = x²`, about `2^-57.68` relative to `x`.  The proof subtracts the kernel from the first 30 terms of the arctangent's series in `z` (`TaylorRemainder.atanCoeffs 30`), whose remainder `TaylorRemainder.atan_remainder` bounds by `|x|^61/(1 - x²)` from Mathlib's `Real.hasSum_arctan` [8], at most `|x| · (1/256) · 2^-57` here.  `PolyBound.check` bounds the difference by `(159/256) · 2^-57` on `[0, 49/256]`, the range of `z`, in 16 adjacent pieces, `atan_part_1` to `atan_part_16`, each proved by `decide +kernel` with bisection to depth 18 and combined through `atan_part_covers` by `PolyChecks.bounded_of_covers`.  Sampling found the largest error to be about `2^-57.71` at `x ≈ 0.188`, and `s_atan.c` states none ([the polynomial journal section](../../devnotes.md#2026-10-10-kernel-polynomials-of-stage-3-track-poly)).  A first attempt with a single `decide +kernel` over the whole interval ran for 4 minutes 40 seconds and reached 5.7 GB before it was stopped, and the split into pieces, which `PolyChecks.Covers` states, built in 40 seconds.

### Error budget of `atan`

Each reduced case bounds the error of the result against `arctan |x|` by the sum of the reduced argument's error, the kernel's error, the error of the constant, the roundings of the tail, and the Lipschitz bound of `arctan`, and `F64Approx.within_one_of_error` turns an error below one and a half spacings of a binade at or below the result into one step.  The small cases use `F64WithinSelf.rel_finish`, a relative criterion in the binade of `x`, and `abs_finish`, the same absolute criterion for either sign.  The constants of the eight reduced cases come from a script outside the repository, `cases.py`, which the docstring of `AtanTheoremCases` names, and the Lean statements carry them as rationals that the proofs check.

| `\|x\|` | Theorem | Binade of the result | Error in spacings | Allowance |
|---|---|---|---|---|
| below `2^-27` | `AtanTheoremSmall.atan_tiny` | that of `x` | `\|arctan x - x\| ≤ \|x\|³/(1 - x²)`, relative about `2^-54` | relative `2^-53` (`within_one_of_self`) |
| `[2^-27, 1/4]` | `atan_poly_small` | that of `x` | relative `1.2 · 2^-53` | relative, about `1.5 · 2^-53` (`rel_finish`) |
| `[1/4, 0.2556]` | `atan_poly_mid_a` | `[1/8, 1/4)` | 1.222 | 1.5 |
| `[0.2556, 7/16)` | `atan_poly_mid_b` | `[1/4, 1/2)` | 1.308 | 1.5 |
| `[7/16, 0.551]` | `AtanTheoremCases.case0_low` | `[1/4, 1/2)` | 1.3256 | 1.5 |
| `[0.551, 11/16)` | `case0_high` | `[1/2, 1)` | 1.0671 | 1.5 |
| `[11/16, 1]` | `case1_low` | `[1/2, 1)` | 1.4005 | 1.5 |
| `[1, 19/16)` | `case1_high` | `[1/2, 1)` | 1.1676 | 1.5 |
| `[19/16, 3/2]` | `case2_a` | `[1/2, 1)` | 1.4385 | 1.5 |
| `[3/2, 1.586]` | `case2_b` | `[1/2, 1)` | 1.1097 | 1.5 |
| `[1.586, 39/16)` | `case2_c` | `[1, 2)` | 1.2459 | 1.5 |
| `[39/16, 2^66)` | `case3` | `[1, 2)` | 1.2991 | 1.5 |
| from `2^66` | `AtanTheorem.atan_big` | `[1, 2)` | 0.28 | 1.5 |

The column of errors divides each case's bound, a rational in its `_err` theorem, by the spacing of its binade.  The smallest margin is that of `case2_a`, 0.06 spacings or 4 percent of the allowance.  A negative `x` gives the negated word, and `AtanTheorem.signed_result` carries the bound through the negation.

### `atan2`

`atan2_within_two` follows the branches of the code.  For `x = 1` the result is `atan y`, within one step.  For `x = ±0` and for `|y/x| > 2^60` the result is `±π/2` rounded and the argument lies within `2^-59` of `±π/2` (`within_half`), and for `x < 0` with `|y/x|` below about `2^-59` the result is `±π` rounded (`within_pi`).  `AtanTwoBits.k_cases` derives these ranges from the shifted difference of the high words.

The general branch rests on `AtanTwoAtan.atan_good`, which follows the branches of `atan` for the rounded quotient `q` and bounds the result against `arctan Q` for the exact quotient `Q`.  `AtanTwoQuot.quot_facts` gives `|q - Q| ≤ 2^-53 Q + 2^-1075`, and `AtanTwoErr.sens_range` bounds `|arctan q - arctan Q|` by `H/(1 + L H) · 2^-53 + 2^-1075` for `q ≥ L` and `Q ≤ H`.  For `q ≥ 1.586` that bound is too weak for the quadrants `x < 0`, and `sens_sharp` bounds the change by `c · 2^-53 + 2^-1075` for any `c` with `L + c · 2^-53 + 2^-1075 ≤ c (1 + L²)` and `2 c L ≥ 1`, which admits `c` just above `L/(1 + L²)`.  The predicate `AtanTwoErr.Good z Q` states that `z` is finite, within `1.49 · 2^-52` of `arctan Q`, and within two steps of it.

For `x > 0` the result is `±z`, and `F64TwoSteps.within_two_of_error` allows two and a half spacings of a binade at or below the result, from the same argument as one step from one and a half.  For `x < 0` the result is `π - (z - π_lo)` or its negation, and `AtanTwoErr.neg_finish` turns the first two parts of `Good` into two steps: the rounding of `z - π_lo` adds at most half a spacing (`F64HalfUlp`), and the last difference rounds to a nearest word of its exact value (`F64RoundNearest`).  Below `2^-27` the quotient itself is the result of `atan`, which meets the relative criterion down to `2^-1021` and `F64TwoSteps.within_two_low` below it.

| Case of `atan` at `q` | Binade | Error of `atan` | Change from `Q` | Total for `x > 0` |
|---|---|---|---|---|
| `case0_low` | `[1/4, 1/2)` | 1.326 | 0.888 | 2.214 |
| `case1_low` | `[1/2, 1)` | 1.401 | 0.593 | 1.993 |
| `case2_a` | `[1/2, 1)` | 1.438 | 0.539 | 1.978 |
| `atan_poly_mid_a` | `[1/8, 1/4)` | 1.222 | 0.961 | 2.183 |

The table, from [the track's journal](../../devnotes.md#2026-10-10-full-theorems-for-log1p-atan-atan2-asin-and-acos-track-arc), lists the largest totals in spacings of each case's binade against the allowance of 2.5, a margin of 11 percent at the worst.  For `x < 0` the largest totals against the `1.49 · 2^-52` of `Good` are 1.4716 (`case2_c`) and 1.4746 (`case3`), a margin of about 1 percent.  The accuracy check finds results two steps from its reference at two input pairs of the report's Table 6, so a bound of one step would fail for this algorithm unless the reference errs there.

### Shared modules

The analysis uses [error tracking for straight-line code](../../LeanExe/ProofKit/F64Approx.lean), [half-spacing sums](../../LeanExe/ProofKit/F64HalfUlp.lean), [nearest rounding of sums](../../LeanExe/ProofKit/F64RoundNearest.lean), [doubling a nearest word](../../LeanExe/ProofKit/F64RoundDouble.lean), [division bounds](../../LeanExe/ProofKit/F64DivBounds.lean), [functions that return their argument](../../LeanExe/ProofKit/F64WithinSelf.lean), [a word that is the reference](../../LeanExe/ProofKit/F64WithinZero.lean), [two steps from a total error](../../LeanExe/ProofKit/F64TwoSteps.lean), [exact operations and Sterbenz's lemma](../../LeanExe/ProofKit/F64Exact.lean), [fdlibm's high-word tests](../../LeanExe/ProofKit/F64UpperWord.lean), [the polynomial checker](../../LeanExe/ProofKit/PolyBound.lean), [its unions of intervals](../../LeanExe/ProofKit/PolyChecks.lean), and [Taylor remainders](../../LeanExe/ProofKit/TaylorRemainder.lean).  The proof modules import 11 ProofKit modules directly, which with their ProofKit dependencies number 78.  The whole import closure of `AtanFile`, with the implementation and the compiler, contains 134 ProofKit modules.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| The polynomial difference within `(159/256) · 2^-57` on 16 pieces of `[0, 49/256]`, and their union | `AtanKernelPoly.atan_part_1` to `atan_part_16`, `atan_part_covers` |
| `arctan (1/2)` and `arctan (2/3)` from 36 and 64 terms of their series, evaluated in `ℚ`, and `π` from Mathlib's twenty-digit bounds `Real.pi_gt_d20` and `Real.pi_lt_d20` [8] | `AtanTheoremConst.atan_half`, `atan_two_thirds`, `atan_one`, `atan_inf`, `atan_three_halves` |
| The thresholds of the high-word tests as rationals | `AtanTheorem.ix_66`, `ix_27`, `ix_a` to `ix_d` |
| The words of the rounded constants and of `pi_o_2 + 0.5 pi_lo` | `AtanTwoBits.half_bits`, `half_neg_bits`, `big_bits2`, `AtanTheorem.big_bits` |
| Functions 2 and 3 are exported as `atan` and `atan2` | `AtanBytes.atan_export`, `atan2_export` |
| The file's bytes equal the encoder's | `AtanFile.atan_file` |

## Tests

[The accuracy check](AtanAccuracy.lean) compares `Atan.atan` and `Atan.atan2` natively with the doubles nearest to their exact values, computed by `ArcReference.atanQuotient` with Lean's integers, and it fails at the first result of `atan` more than one step away or of `atan2` more than two.  The 200,084 arguments of `atan` are 100,001 evenly spaced values from -10 to 10, 100,000 hashed values over all finite exponents with both signs, the five doubles at and around each of the six thresholds of the high-word tests with both signs, 14 special values, and the 9 inputs of `WorstCases.atan`.  The 84,189 pairs of `atan2` are 60,000 hashed pairs over all finite exponents, 22,000 hashed pairs whose exponents differ by 55 to 65 in both directions and with all four signs, 2,000 hashed `y` with `x = 1`, the 10 pairs of `WorstCases.atan2` in both orders, and the 169 pairs of 13 special values.  The worst-case inputs are those of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [9], whose Table 3 lists 0.861 units for FreeBSD 15.1's `atan` and 1.55 for its `atan2`.

In `opus-verified-tests-14.log` all 200,084 results of `atan` lie within one step of the reference, 6,140 of them unequal to it, and all 84,189 results of `atan2` lie within two steps, 3,105 of them unequal.  The largest measured distances equal the proved bounds: the two-step results of `atan2` are at the pairs `(-0x1.ec2003fe89e36p-433, 0x1.ec173ed5fd8f5p-427)` and `(-0x1.358bb5eb25bdcp+813, 0x1.2f86b82481a0ap+815)` of the report's Table 6 ([the journal](../../devnotes.md#2026-10-11-zimmermanns-inputs-in-the-accuracy-checks)).  The C library on the build host lies within one step for both functions at the same arguments, with 94 and 1 results unequal to the reference.  The reference's docstrings bound its truncation errors below `2^-390` relative, a claim that is not proved.

## Limits

The limits of [the exponential theorem](Exp.md#limits) apply in the same way: the theorem is about Talos's semantics, the interpreter and the decoder are trusted, the file theorem trusts `binary_file%`, Talos implements the deterministic profile in which every NaN result is canonical [7], and the arguments are the bits of Lean `Float`s, whose only NaN is the canonical one (`F64Bits.toBits_canonical`), so the theorems cover only the canonical NaN among the NaN words a WebAssembly caller can pass.  The byte theorems cover sequences of calls to `atan` and `atan2`.  The module also exports `alloc`, `release`, its memory, and the counters `allocCount` and `freeCount`, and a host that calls `alloc` or `release` or writes the memory between calls needs a theorem that the action preserves `Ready`.  The module reads no table, so the store invariant has only the allocator invariant and the memory cap.

`atan2_within_two` and the bound in the byte theorem exclude NaN arguments through their finiteness hypotheses.  The code returns `x + y` there, which is the canonical NaN in Talos, and `AtanTwoNaN.atan2_nan` states that result for the Lean function.  For a NaN, `y = ±0`, and infinite arguments the byte theorem of `atan2` states only that the result is the word of `Atan.atan2 y x`, and `AtanTwoSpecial` and `AtanTwoNaN` give those words for the Lean function.

## References

1. FreeBSD, [`lib/msun/src/s_atan.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_atan.c) and [`lib/msun/src/e_atan2.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_atan2.c), commit `20381bce4b63975494a2f4bc84257f6932e6d379`.  Copyright (C) 1993 by Sun Microsystems, Inc., with the notice quoted above.
2. FreeBSD, [`lib/msun/src/math_private.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/math_private.h), the same commit: `nan_mix` and the word macros.
3. Sun Microsystems, [FDLIBM version 5.3 readme](https://www.netlib.org/fdlibm/readme), netlib: "FDLIBM (Freely Distributable LIBM) is a C math library for machines that support IEEE 754 floating-point arithmetic."
4. NIST, *Digital Library of Mathematical Functions*, [§4.24 Inverse Trigonometric Functions: Further Properties](https://dlmf.nist.gov/4.24), Eq. 4.24.3 (the series of `arctan`) and Eq. 4.24.15 (the addition formula).
5. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clause 9.2 with Table 9.1 (domains and exceptions) and clause 9.2.1, which defines `atan2` and its special values.
6. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.1.3, and F.9.1.4, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
7. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
8. The Mathlib Community, Mathlib at commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`: [`Mathlib/Analysis/SpecialFunctions/Complex/Arctan.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Complex/Arctan.lean) (`Real.hasSum_arctan`), [`Mathlib/Analysis/Real/Pi/Bounds.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/Real/Pi/Bounds.lean) (`Real.pi_gt_d20`, `Real.pi_lt_d20`), and [`Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean) (`Complex.arg`).
9. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
