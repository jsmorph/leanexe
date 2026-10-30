# The exponential minus one and the hyperbolic tangent

[The implementation](Program.lean) exports `expm1` and `tanh`, ports of fdlibm's `s_expm1.c` and `s_tanh.c` as FreeBSD's msun has them [1, 2].  `expm1` reduces its argument by multiples of `ln 2`, approximates `exp r - 1` by a rational function, and scales the result in one of five forms, and `tanh` computes `tanh |x|` from `expm1 (±2|x|)` with one quotient.  The decided bounds are one representable step for `expm1` and three steps for `tanh`.  Both bounds are proved for every finite input, and the exceptional values are proved as words.  `TanhBytes.tanh_module_accuracy` carries the bounds to the decoded WebAssembly module, and `TanhFile.tanh_file` connects that module to the file `build/verified/tanh.wasm`.  Every accepted theorem reports only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`expm1` computes `Real.exp a - 1` and `tanh` computes `Real.tanh a`, where `a` is the value of the argument.  Every finite double is in both domains.  The bound is `F64SignedRounding.WithinSteps n y w`, defined in [the signed rounding reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean): the word `w` is not a NaN, and its position in the ordered line of doubles, with both zeros at 0 and the infinities next to the largest finite values, lies within `n` of the position of the nearest-even rounding of `y`.  `expm1` overflows to `+∞` above fdlibm's `o_threshold`, about 709.78, and the nearest-even rounding of `exp a - 1` is `+∞` from the overflow threshold `2^1024 - 2^970` of IEEE 754-2019 clause 4.3.1 [5].  `tanh` is bounded by 1 in magnitude and never overflows.

| Input | `expm1` | `tanh` | Source of the rule | Theorems |
|---|---|---|---|---|
| `+0`, `-0` | same zero | same zero | IEEE 754-2019 9.2.1 [5]; C99 F.9.3.3 and F.9.2.6 [6] | `Expm1Special.expm1_zero`, `TanhSpecial.tanh_zero` |
| `+∞` | `+∞` | `1` | IEEE 754-2019 9.2.1; C99 F.9.3.3 and F.9.2.6 | `expm1_pos_infinity`, `tanh_pos_infinity` |
| `-∞` | `-1` (`0xBFF0000000000000`) | `-1` | IEEE 754-2019 9.2.1; C99 F.9.3.3 and F.9.2.6 | `expm1_neg_infinity`, `tanh_neg_infinity` |
| NaN | canonical NaN | canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [7] | `expm1_nan`, `tanh_nan` |
| finite, `exp a - 1 ≥ 2^1024 - 2^970` | `+∞` or the largest finite double within the one-step bound | | IEEE 754-2019 4.3.1 gives the reference `+∞` | `Expm1Theorem.expm1_within_one` |

IEEE 754-2019 lists `expm1` and `tanh` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [5].  fdlibm states an error below one unit in the last place for `expm1` and no bound for `tanh` [1, 2].  The theorems say nothing about floating-point exceptions or `errno`, which the port does not compute.

## Algorithm

`expm1` writes `x = k ln 2 + r` with `|r| ≤ 0.5 ln 2`, about 0.3466, and keeps the rounding error of `r` in a correction `c`, so that `r + c` approximates the exact residual [1].  For `|x|` below `0.5 ln 2` there is no reduction, `k = ±1` up to `1.5 ln 2`, and otherwise `k` is the truncation of `x/ln 2 ± 1/2`.  `ln 2` is split into `ln2_hi`, whose significand has 32 bits, and `ln2_lo`, so that `k · ln2_hi` and `x - k · ln2_hi` are exact for every `k` that the code forms, from -56 to 1024.  This is the splitting of Cody and Waite [3], as Boldo, Daumas, and Li describe it [4].

The approximation is a rational function.  fdlibm's comment defines `R1 (r²) = 6/r · ((exp r + 1)/(exp r - 1) - 2/r)`, which equals `1 - r²/60 + r⁴/2520 - ...`, and approximates it by a polynomial `1 + Q1 z + ... + Q5 z⁵` in `z = r²` with error below `2^-61` [1].  With `hxs = r²/2`, `t = 3 - R1 · r/2`, and `e = hxs · (R1 - t)/(6 - r t)`, the kernel returns `r - (r e - hxs)`, which equals `exp r - 1` when `R1` is exact.  The code stores the coefficients scaled by `2^n` and evaluates the polynomial in `hxs`, which the kernel needs for its other terms, so that `r²` is never formed.  With a correction, the kernel uses `expm1 (r + c) ≈ expm1 r + c + r c`.

The result is `2^k (expm1 r + 1) - 1`, formed in the order that loses least for each `k` [1].  In the table `E` is the remainder `e` after the correction, `(r (e - c) - c) - hxs`, so that `r - E` approximates `expm1 (r + c)`.  The multiplications by `2^k` are exact except where the result overflows.

| `k` | Result |
|---|---|
| 0 | `r - (r e - hxs)` |
| -1 | `0.5 (r - E) - 0.5`, with `E` the corrected remainder |
| 1 | `-2 (E - (r + 0.5))` for `r < -0.25`, else `1 + 2 (r - E)` |
| `≤ -2` or `> 56` | `2^k (1 - (E - r)) - 1`, with `2^1024` formed as `2 · 2^1023` |
| 2 to 19 | `2^k ((1 - 2^-k) - (E - r))` |
| 20 to 56 | `2^k ((r - (E + 2^-k)) + 1)` |

Below `2^-54` the result is `x`, and for `x ≤ -56 ln 2`, about -38.8, it is `-1`.  `tanh` reduces to `|x|` by oddness.  Below `2^-28` the result is `x`, from 22 on it is `1 - 10^-300`, which rounds to 1, and between them `tanh |x| = -t/(t + 2)` with `t = expm1 (-2|x|)` below 1 and `1 - 2/(t + 2)` with `t = expm1 (2|x|)` from 1 on [2].  Both forms are identities: `-t/(t + 2) = (1 - e^{-2a})/(1 + e^{-2a})` and `1 - 2/(t + 2) = (e^{2a} - 1)/(e^{2a} + 1)`.  The first keeps relative accuracy for small `a`, and the second subtracts a small quotient from 1.

## Implementation

The sources are FreeBSD's `lib/msun/src/s_expm1.c` and `s_tanh.c` [1, 2].  Both carry the notice "Copyright (C) 1993 by Sun Microsystems, Inc.  All rights reserved.  Developed at SunPro, a Sun Microsystems, Inc. business.  Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved."  The module docstring of [the implementation](Program.lean) quotes the notice verbatim, as the notice requires.

The port is written in the Verified dialect, which [the Verified compiler](../../../../Verified/README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [expm1Kernel, expm1, tanh]` generates the module, whose functions are `alloc` (0), `release` (1), `expm1Kernel` (2), `expm1` (3), and `tanh` (4).  The module reads no tables.  [The hyperbolic sine and cosine](../Sinh/Program.lean) call `Tanh.expm1`, so their module contains `expm1Kernel` and `expm1` as well.

| C code | Port | Reason |
|---|---|---|
| `int32_t k` from `(int32_t)(invln2*x ± 0.5)` | sign `neg` and magnitude `m : UInt64`, with `m` the truncation of `invln2 · x + 0.5` or of `-(invln2 · x - 0.5)` | The dialect converts only between floats and unsigned words.  The negation is exact, so the magnitude equals the C truncation's. |
| kernel and scaling inline in `expm1` | `expm1Kernel x c neg m` | One function per path shape. |
| `t = huge + x; return x - (t - (huge + x))` | `x - ((huge + x) - (huge + x))` | The expression raises the inexact flag in C, and its value is `x`. |
| `x + tiny < 0` and `tiny - one` | kept | The test holds for every `x ≤ -56 ln 2`, and the value is `-1`. |
| `volatile` `huge` and `tiny`, `STRICT_ASSIGN` | constants and `let` | The dialect evaluates each binary64 operation once, in order. |
| nested tests on the high word | one chain of `if` | `0x7ff00000 ≥ 0x40862E42 ≥ 0x4043687A`, so the order of the tests gives the same branches. |
| `if (ix < 0x3e300000) { if (huge + x > one) return x; }` in `tanh` | `ix < 0x3e300000 && huge + x > 1.0` | `huge + x > 1` holds for every such `x`. |
| `fabs` | `Float.abs`, compiled to `f64.abs` | |
| floating-point flags, `errno` | none | WebAssembly has no floating-point status flags. |

Each constant is written as `Float.ofBits` of its bit pattern with fdlibm's decimal beside it.  A script that compares the port with the C sources at the pinned commit finds that each decimal converts to the port's bits, that each pair of hexadecimal words in the C comments equals the port's word, and that every high-word threshold of the C code appears in the port.  `huge` and `tiny` carry no hexadecimal comment in the C source, and their decimals convert to the words in the table.

| Constant | Bits | Value |
|---|---|---|
| `o_threshold` | `0x40862E42FEFA39EF` | `7.09782712893383973096e+02` |
| `ln2_hi` | `0x3FE62E42FEE00000` | `6.93147180369123816490e-01`, 32 significant bits |
| `ln2_lo` | `0x3DEA39EF35793C76` | `1.90821492927058770002e-10` |
| `invln2` | `0x3FF71547652B82FE` | `1.44269504088896338700e+00` |
| `Q1` to `Q5` (scaled) | `0xBFA11111111110F4`, `0x3F5A01A019FE5585`, `0xBF14CE199EAADBB7`, `0x3ED0CFCA86E65239`, `0xBE8AFDB76E09C32D` | `-3.33333333333331316428e-02` to `-2.01099218183624371326e-07` |
| `huge`, `tiny` | `0x7E37E43C8800759C`, `0x01A56E1FC2F8F359` | `1.0e+300`, `1.0e-300` |
| `2^1023` | `0x7FE0000000000000` | factor for `k = 1024` |

| High word | Value | Test |
|---|---|---|
| `0x3fd62e42` | `0.5 ln 2` | `expm1` reduces above it |
| `0x3FF0A2B2` | `1.5 ln 2` | `k = ±1` below it |
| `0x4043687A` | `56 ln 2` | `-1` from it on for negative `x` |
| `0x40862E42` | 709.78 | overflow test |
| `0x3c900000` | `2^-54` | `expm1` returns `x` below it |
| `0x3e300000`, `0x3ff00000`, `0x40360000` | `2^-28`, 1, 22 | ranges of `tanh` |

## Theorems

The theorems are in [the expm1 theorem](Expm1Theorem.lean), [its exceptional values](Expm1Special.lean), [the tanh theorem](TanhMain.lean), [its exceptional values](TanhSpecial.lean), [the byte theorems](TanhBytes.lean), and [the file module](TanhFile.lean), each in the namespace `Library.Numerics.Float64.Tanh` followed by the module's name.  `x` is a Lean `Float`, `a = value x.toBits`, and a word is the `UInt64` bit pattern of a double.  The byte theorems use `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `Expm1Theorem.expm1_within_one` | For finite `x`, `WithinSteps 1 (Real.exp a - 1) (Tanh.expm1 x).toBits`. |
| `Expm1Special.expm1_zero`, `expm1_pos_infinity`, `expm1_neg_infinity`, `expm1_nan` | `±0` gives the same word, `+∞` gives `+∞`, `-∞` gives `-1`, and a NaN gives `Wasm.IEEE64.canonicalNaN`. |
| `TanhMain.tanh_within_three` | For finite `x`, `WithinSteps 3 (Real.tanh a) (Tanh.tanh x).toBits`. |
| `TanhSpecial.tanh_zero`, `tanh_pos_infinity`, `tanh_neg_infinity`, `tanh_nan` | `±0` gives the same word, `+∞` gives 1, `-∞` gives `-1`, and a NaN gives the canonical NaN. |
| `TanhBytes.ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant and a memory cap of at most 65,535 pages. |
| `TanhBytes.expm1_entry_call`, `tanh_entry_call` | A call of function 3 or 4 from a `Ready` store returns, without a trap, the bits of `Tanh.expm1 x` or `Tanh.tanh x`, and leaves a `Ready` store in which every heap region keeps its bytes. |
| `TanhBytes.expm1_bytes_accuracy`, `tanh_bytes_accuracy` | `Tanh.compiled.module` encodes to bytes that decode to it, exports function 3 as `expm1` or function 4 as `tanh`, starts in a `Ready` store, and every call from a `Ready` store returns the function's bits, within one step of `exp a - 1` or three steps of `tanh a` for finite `x`, and leaves a `Ready` store. |
| `TanhBytes.tanh_module_accuracy` | Conjunction of the two byte theorems. |
| `TanhFile.tanh_file` | `build/verified/tanh.wasm` holds `encode Tanh.compiled.module`. |
| `TanhFile.tanh_file_decode` | `build/verified/tanh.wasm` decodes to the module of `tanh_module_accuracy`. |

Each of these theorems has a `#print axioms` line.  In a run of `tests/verified/run.sh`, every theorem of the table except the two file theorems reports `[propext, Classical.choice, Quot.sound]`.  `tests/verified/run.sh` builds `Library.Numerics.Float64.Tanh.TanhBytes`, checks `TanhFile.lean` against the `tanh.wasm` it has written, and fails unless both file theorems report exactly the three permitted axioms.  That run passed this check for its entry `tanh:TanhBytes:TanhFile`, and since `tanh_file_decode` takes its bytes from `tanh_module_accuracy`, the axiom report of `tanh_file_decode` covers both byte theorems.

## Proof

### Modules

The proof has 31 modules in `Library/Numerics/Float64/Tanh/` above the implementation, and it uses `ExpReductionBounds` from the exponential's proof for an enclosure of `ln 2`.  The table lists them by stage, in dependency order within each stage.  [The library aggregate](../../../../Library.lean) includes `TanhBytes` and `Expm1Near`, so `lake build Verified Library` builds the chain.

| Stage | Modules | Content |
|---|---|---|
| Kernel | `Expm1Words`, `Expm1KernelPoly`, `Expm1KernelInner`, `Expm1KernelE0`, `Expm1KernelOuter` | Kernel on bit patterns, its approximation in exact arithmetic, and rounding of each of its operations. |
| Scaling forms | `Expm1FormWords`, `Expm1SubOne`, `Expm1FormBase`, `Expm1FormsOne`, `Expm1FormsTwo`, `Expm1FormsMid` | Words `2^k`, `2^-k`, and `1 - 2^-k`, and one step for each form. |
| Reduction | `Expm1ReduceConst`, `Expm1ReduceWords`, `Expm1ReduceOne`, `Expm1ReduceK` | `ln2_hi + ln2_lo` within `2^-86` of `ln 2`, `invln2 · ln 2` within `2^-55` of 1, exact products and differences, and `y + c` within `2^-70` of `x - k ln 2`. |
| `expm1` | `Expm1PathsReduced`, `Expm1PathsEdge`, `Expm1Branches`, `Expm1Theorem`, `Expm1Special` | Paths, branches of the code, theorem, and exceptional values. |
| `tanh` | `TanhBranches`, `Expm1NearForms`, `Expm1Near`, `TanhWords`, `TanhSmall`, `TanhLarge`, `TanhTheorem`, `TanhMain`, `TanhSpecial` | Errors of the `expm1` paths before their last rounding, four ranges of `tanh`, theorem, and exceptional values. |
| Bytes | `TanhBytes`, `TanhFile` | Byte and file theorems. |

### Error budget of expm1

Let `u = 2^-53` and `η = 2^-1075`, the underflow term of a product or quotient.  The lemmas bound each stage against the exact value, with `X` the value of the reduced argument and `C` that of the correction.  The bounds before the last rounding feed the step criteria below, and the same bounds feed the analysis of `tanh`.

| Stage | Bound | Lemma |
|---|---|---|
| Kernel in exact arithmetic against `exp r - 1`, `\|r\| ≤ 0.3466` | `2^-62 \|r\|³` | `Expm1KernelPoly.kernel_approx` |
| Computed `e` against its exact value | `2.7 u X²/2 + 4η` | `Expm1KernelE0.e0_spec` |
| `k = 0`: the value before the last rounding against `exp X - 1` | `0.56 u \|X\| + 16η` | `Expm1KernelOuter.m0_spec` |
| Reduction: `y + c` against `x - k ln 2` | `2^-70`, with `\|c\| ≤ 0.36 u` | `Expm1ReduceOne.reduce_one_pos`, `reduce_one_neg`, `Expm1ReduceK.reduce_k_pos`, `reduce_k_neg` |
| `k ≠ 0`: `y - e2` against `exp r - 1` | `0.2401 u` | `Expm1FormBase.common`, from `Expm1KernelOuter.e2_spec` (`0.24 u`) |

`kernel_approx` multiplies out the denominator `6 - r t`.  With the exponential replaced by its Taylor polynomial of degree 17, the numerator of the error is `r³` times a polynomial of degree 26, which `PolyBound.check` bounds by `2^-60` on `[-0.3466, 0.3466]` in the kernel, and whose largest value the module's docstring gives as about `2^-61.74`.  The forms then prove one step against `2^k exp r - 1`, and the path without reduction against `exp x - 1`, with two criteria for a word that is a nearest word of the value before the last rounding.  `Expm1FormBase.within_of_level`, which the forms use, gives one step when that value lies within one spacing of the exact result and the exact result lies at least two spacings into its binade, and `Expm1PathsEdge.within_rel`, which the path without reduction uses, gives one step for a relative distance of at most `(1 - 2^-50) u`.  The journal's budget, made before the proof, found the forms for `k = 1` with `r < -1/4` and for `2 ≤ k < 20` with `exp r - 2^-k` above 0.457 within ten percent of a spacing of failing, and it needed the kernel below `0.25 u`, which `e2_spec` meets with `0.01 u` to spare.  These margins required the nearest property of each rounding and its half-spacing bound, which [the nearest sums](../../../../LeanExe/ProofKit/F64NearestSum.lean) and [the one-step criteria](../../../../LeanExe/ProofKit/F64NearestSteps.lean) provide.

| Range of `a` | Path | Theorem |
|---|---|---|
| `\|a\| < 2^-54` | `x` | `Expm1PathsEdge.path_tiny` |
| `2^-54 ≤ \|a\| ≤ 0.3466` | kernel, `k = 0` | `Expm1PathsEdge.path_middle` |
| `0.3466 < a < 1.0397` and `-1.0397 < a < -0.3466` | `k = ±1` | `Expm1PathsReduced.path_one_pos`, `path_one_neg` |
| `1.0397 ≤ a` up to the overflow threshold | `1 ≤ k ≤ 1024` | `Expm1PathsReduced.path_k_pos` |
| `-38.817 ≤ a ≤ -1.0397` | `1 ≤ -k ≤ 56` | `Expm1PathsReduced.path_k_neg` |
| `a > o_threshold` | `huge · huge = +∞` | `Expm1PathsEdge.path_overflow` |
| `a ≤ -38`, high word at least that of `56 ln 2` | `-1` | `Expm1PathsEdge.path_saturated` |

For `k = 1024` the form needs `exp r ≤ 1 - 2^-46` (`Expm1FormsTwo.form_top`), and `Expm1PathsReduced.overflow_gap` supplies it: at or below the overflow threshold, `x - 1024 ln 2 ≤ -2 · 10^-14`.  The form first assumed `exp r ≤ 1 - 2^-40`, which the reduction cannot supply, since `x - 1024 ln 2` is only about `-2.37 · 10^-14` at the threshold.  At the other end, from `x ≤ -38` the exponential is at most `2^-54` (`Expm1PathsEdge.exp_saturated`), and `-1` lies within one step of `exp x - 1`.

### Error budget of tanh

`tanh` composes `expm1` with at most three more roundings.  `Expm1Near` exports the error of each `expm1` path before its last rounding, and [the nearest quotient](../../../../LeanExe/ProofKit/F64NearestDiv.lean) states that a rounded quotient is a nearest word of the exact quotient.  [The relative step criteria](../../../../LeanExe/ProofKit/F64NearestRelative.lean) turn a relative distance into a count of steps: `within_rel_of` gives `k` steps when `|s - y| ≤ (k - 1/16) u y`.

| Range of `\|a\|` | Code | Bound used | Steps | Theorem |
|---|---|---|---|---|
| below `2^-28` | `x` | `\|x - tanh x\| ≤ (4/3) \|x\|³` | 1 | `TanhTheorem.tiny_within` |
| `2^-28` to 1 | `-t/(t + 2)`, `t = expm1 (-2\|x\|)` | error `E` of `-t` against `P = 1 - exp (-2\|x\|)`: `0.56 u · 2\|x\| + 16η` for `2\|x\| ≤ 0.3466`, `0.2451 u` for `k = -1`, and `0.3726 u` from `2\|x\| ≥ 1.0397`, each plus the last rounding of `t` | 3 | `TanhSmall.small_a`, `small_b`, `small_c` |
| 1 to 22 | `1 - 2/(t + 2)`, `t = expm1 (2\|x\|)` | `t` within `0.85 u T` of `T = exp (2\|x\|) - 1` before its rounding, and the result within `7.704 u/D + η`, with `D ≥ 8.36` the value of `t + 2` | 1 | `TanhLarge.large_core` |
| 22 on | `1 - 10^-300`, which rounds to 1 | `exp (2a) ≥ 2^54`, so `1 - tanh a < 2^-53` | 1 | `TanhTheorem.huge_within` |

On the middle range the computed quotient differs from `tanh a = P/(2 - P)` by `(2 (W - P) - P (D - 2 + W))/(D (2 - P))`, with `W` the value of `-t` and `D` that of `t + 2`, so its relative error is at most `(2E + P u)/(D P)` before the quotient's own rounding, as the journal derives.  `TanhSmall.small_core` gives three steps when `2E + P u ≤ (47/16) u P (2 - P - 1/1000)`.  The journal records the margins: `4.51 u P` against `4.85 u P` on the path without reduction, and positive quadratics in `P` on `[0.29, 0.65]` (`k = -1`) and `[0.64, 0.87]` (`k ≤ -2`).

Sampling and the worst inputs of Zimmermann's report reach two steps, and the proof reaches three.  A floating-point sweep in the journal, over 300,000 random arguments and the arguments next to each binade boundary of `tanh`, composed every bound at its worst case at once: with `WithinSteps 1` of `expm1` alone the composition gives four steps, and with the errors before the last rounding it leaves a margin factor of 1.11 for three steps and 0.74 for two.  Both minima lie at `|a| = atanh (1/2) ≈ 0.5493`, where `P = 2/3` and `tanh a = 1/2`.  Below that point `tanh a` lies in the binade `[1/4, 1/2)`, whose spacing is half that of `[1/2, 1)`, so an absolute error there counts twice as many steps.  The decided bound is therefore three steps, with the gap recorded as one of the analysis ([the decision of 2026-10-11](../../../../devnotes.md#2026-10-11-decisions-on-tanh-the-reflector-and-the-bessel-bounds)).

### Shared modules

The proof imports the arithmetic chain of `F64Add`, `F64Mul`, `F64Div`, and `F64Bits` that proves Lean's `Float` operations equal to Talos's `IEEE64` functions.  This proof added six ProofKit modules: [the nearest sums](../../../../LeanExe/ProofKit/F64NearestSum.lean), [the one-step criteria](../../../../LeanExe/ProofKit/F64NearestSteps.lean), [the rounding stages of approximations](../../../../LeanExe/ProofKit/F64ApproxStages.lean), [the nearest scaling by a power of two](../../../../LeanExe/ProofKit/F64NearestScale.lean), [the nearest quotient](../../../../LeanExe/ProofKit/F64NearestDiv.lean), and [the relative step criteria](../../../../LeanExe/ProofKit/F64NearestRelative.lean).  The proof also uses [the polynomial bound checked by the kernel](../../../../LeanExe/ProofKit/PolyBound.lean) and [the Taylor remainders](../../../../LeanExe/ProofKit/TaylorRemainder.lean), whose exponential bound comes from Mathlib's `Real.exp_bound` [8], and [the relative one-step criterion](../../../../LeanExe/ProofKit/F64RelativeStep.lean).

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| The numerator of the kernel's error has no terms below `r³`, and the rest is at most `2^-60` on `[-0.3466, 0.3466]` | `Expm1KernelPoly.error_low`, `error_check` |
| The denominator `6 - r t` differs from 6 by at most `6/5` on the same interval | `Expm1KernelPoly.denominator_check` |
| Values of the constants 1, 1/2, 2, 3, 6, -2, and -1/4 as scaled words, and rational bounds on the magnitudes of `Q1` to `Q5` | `Expm1KernelInner.const_values`, `coefficient_rat` |
| `ln2_hi + ln2_lo` and `invln2 · ln 2` against the rational enclosure of `ln 2` | `Expm1ReduceConst.split_check` |
| Words `1 - 2^-k` for `2 ≤ k < 20` | `Expm1FormWords.oneMinus_scaled` |
| `x - 1024 ln 2 ≤ -2 · 10^-14` at the overflow threshold | `Expm1PathsReduced.overflow_gap` |
| Functions 3 and 4 are exported as `expm1` and `tanh` | `TanhBytes.expm1_export`, `tanh_export` |
| The file's bytes equal the encoder's | `TanhFile.tanh_file` |

### History

[The proof's journal section](../../../../devnotes.md#2026-10-10-exponential-minus-one-and-hyperbolic-tangent-track-expm1) records each module with its logs.  The plan of 2026-10-10 set two steps for `tanh` from sampling, and the composition above moved it to three.  `Expm1PathsEdge` first compiled for 40 and then 15 minutes without a diagnostic: `rfl` on an equation between the kernel's word function and its unfolded operations did not finish, while `simp [Expm1Words.kernel]` proved it at once, and the module now uses `simp`.  The arithmetic with `2^1075` in the context exceeded the recursion and heartbeat limits of `positivity`, `linarith`, and `nlinarith`, so each inequality of the kernel's budget sits in a lemma over plain reals (`m0_arith1` to `e2_arith3`).

## Tests

[The accuracy check](../../../../tests/TestSupport/Numerics/TanhAccuracy.lean) compares `Tanh.expm1` and `Tanh.tanh` natively with the doubles nearest to `exp x - 1` and `tanh x` computed by [the integer reference](../../../../tests/TestSupport/Numerics/Reference.lean), and it fails at the first `expm1` result more than one step away or `tanh` result more than two steps away.  Its 184,599 arguments of `expm1` are 120,001 evenly spaced values from -40 to 710, 60,000 hashed values with exponents from `2^-60` to `2^9` and both signs, the five doubles around each of 16 thresholds and their negations, 4,406 evenly spaced values from the high-word thresholds to `0.5 ln 2`, `1.5 ln 2`, and `o_threshold` with both signs, 14 tiny values, eight special values, and the ten inputs of `WorstCases.expm1`.  Its 160,082 arguments of `tanh` are 100,001 evenly spaced values from -25 to 25, 60,000 hashed values with exponents from `2^-60` to `2^5`, the doubles around five thresholds with both signs, the tiny and special values, and the nine inputs of `WorstCases.tanh`.  The worst inputs are those of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [9], whose Table 3 lists 0.909 units for `expm1` and 2.22 for `tanh` in FreeBSD 15.1, Musl, and OpenLibm.

In a run of `tests/verified/run.sh`, all 184,599 results of `expm1` lie within one step of the reference, 12,359 of them unequal to it, and all 160,082 results of `tanh` within two steps, 10,410 unequal.  The C library's `tanh` lies within two steps at the same arguments, with 15,125 results unequal.  The largest measured distance equals the proved bound for `expm1`, and for `tanh` it is two steps against the proved three.  The check of `tanh` enforces two steps, so a change that kept the theorem but reached three steps would fail the check.  The reference's truncation errors are stated in its docstrings and are not proved.

## Limits

The theorems are about Talos's semantics of WebAssembly.  The Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode` are trusted, as [the design notes](../../../../docs/design.md#scope-of-the-theorem) record, and the file theorem trusts the elaborator `binary_file%`, which reads `tanh.wasm`.  Talos implements the deterministic profile, in which every NaN result is canonical [7], and an engine outside that profile may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, so the theorems cover only the canonical NaN among the NaN words a caller can pass.  The byte theorems cover sequences of calls to `expm1` and `tanh`: the module also exports `alloc`, `release`, `expm1Kernel`, its memory, and the allocation counters, and a host that calls another export or writes the memory between calls needs a theorem that the action preserves `Ready`.  The `tanh` bound of three steps is one step weaker than the measured behavior, and the analysis above locates the loss at `|a| = atanh (1/2)`.

## References

1. FreeBSD, [`lib/msun/src/s_expm1.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_expm1.c).  Copyright (C) 1993 by Sun Microsystems, Inc.  The comment states the method, the polynomial's error below `2^-61`, and the error below one unit in the last place.
2. FreeBSD, `lib/msun/src/s_tanh.c`, [same commit](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_tanh.c).  Copyright (C) 1993 by Sun Microsystems, Inc.
3. W. J. Cody, Jr. and W. Waite, *Software Manual for the Elementary Functions*, Prentice-Hall, 1980.  Not consulted: the review in *SIAM Review* 24(1):91–93, 1982, [doi:10.1137/1024023](https://doi.org/10.1137/1024023), confirms its identity, and reference 4 the method.
4. S. Boldo, M. Daumas, and R.-C. Li, "Formally Verified Argument Reduction with a Fused Multiply-Add", *IEEE Transactions on Computers* 58(8):1139–1145, 2009, [doi:10.1109/TC.2008.216](https://doi.org/10.1109/TC.2008.216), with the preprint [arXiv:0708.3722](https://arxiv.org/abs/0708.3722).  The preprint describes Cody and Waite's constant `C1` with an exact product `z C1` and its continuation `C2`.
5. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clause 4.3.1 (the overflow threshold), clause 9.2 and Table 9.1 (the recommended operations `expm1` and `tanh`), and clause 9.2.1 (special values).
6. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.2.6, and F.9.3.3, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
7. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
8. The Mathlib Community, Mathlib, [`Mathlib/Analysis/Complex/Exponential.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/Complex/Exponential.lean), `Real.exp_bound`.
9. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
