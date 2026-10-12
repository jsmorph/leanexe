# The exponential function

[The implementation](Exp.lean) exports `exp`, a port of Arm's optimized-routines `exp` [1, 2] in its configuration without fused multiply-add: a reduction by `ln 2/128`, a table of 128 values of `2^(j/128)`, and a polynomial of degree 5.  The decided bound is one representable step from the nearest-even rounding of the real exponential, which the user approved on 2026-10-09 before any other bound.  The bound is proved for every finite binary64 input, the exceptional values are proved exactly, and `ExpTheorem.exp_bytes_accuracy` carries both to the decoded WebAssembly module, with `ExpFile.exp_file` connecting that module to the file `build/verified/exp.wasm`.  Every accepted theorem reports only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`exp` computes `Real.exp` of the value of its argument.  Every finite double is in the domain.  The result is positive infinity from the overflow threshold `2^1024 - 2^970` on, the rule of clause 4.3.1 of IEEE 754-2019 for rounding to nearest [9], which `F64PositiveRounding.overflow_threshold_midpoint` proves to be the midpoint between the largest finite double and `2^1024`.  Results of at most half the smallest subnormal round to `+0`.

The bound is stated in `ExpTheorem.exp_one_step`: for finite `x`, with `r` the word of [the nonnegative nearest-even reference](../../LeanExe/ProofKit/F64PositiveRounding.lean) `F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))` and `w` the word of `Exp.exp x`, `w.toNat ≤ 0x7FF0000000000000`, `w.toNat ≤ r.toNat + 1`, and `r.toNat ≤ w.toNat + 1`.  Nonnegative encodings order zero, the subnormals, the normal doubles, and positive infinity consecutively, so these inequalities state one representable step, overflow included.  The theorem predates [the signed reference](../../LeanExe/ProofKit/F64SignedRounding.lean) and its `WithinSteps n y w`, which the later functions use.  `F64SignedRounding.within_of_nonneg` derives `WithinSteps 1 (Real.exp a) w` from these three inequalities, but no declaration in the repository states that corollary for `exp`.

| Input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `+0`, `-0` | `1` (`0x3FF0000000000000`) | IEEE 754-2019 9.2.1 [9]; C99 F.9.3.1 [10] | `exp_pos_zero`, `exp_neg_zero` |
| `+∞` | `+∞` | IEEE 754-2019 9.2.1; C99 F.9.3.1 | `exp_pos_infinity` |
| `-∞` | `+0` | IEEE 754-2019 9.2.1; C99 F.9.3.1 | `exp_neg_infinity` |
| NaN | the canonical NaN `0x7FF8000000000000` | IEEE 754-2019 9.2 (a quiet NaN for a NaN operand); C99 F.9 paragraph 11; the deterministic profile of WebAssembly [11] | `exp_nan` |
| finite, `exp a ≥ 2^1024 - 2^970` | `+∞` | IEEE 754-2019 4.3.1 | `exp_one_step` |
| finite, `exp a ≤ 2^-1075` | `+0`, or the smallest subnormal within the one-step bound | IEEE 754-2019 4.3.1 | `exp_one_step` |

IEEE 754-2019 lists the exponential among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [9].  The one-step bound is weaker than correct rounding, and the port is not correctly rounded: Arm states a worst error of 0.511 units in the last place for this configuration [2].  The theorem says nothing about floating-point exceptions or `errno`, which the port does not compute.

## Algorithm

The method is the table-driven exponential that Tang published in 1989 [5], as Harrison, Kubaska, Story, and Tang summarize it [6]: write `x = k ln 2/N + r` with an integer `k` and a small residual `r`, so that `exp x = 2^(k/N) · exp r`, take `2^(k/N)` from a table, and approximate `exp r` by a polynomial.  A larger `N` shortens the polynomial at the cost of a table of `N` entries.  Arm's code uses `N = 128` and splits `k = 128 q + j` with `0 ≤ j < 128`, so that `2^(k/N) = 2^q · 2^(j/128)`.

The reduction computes `z = x · N/ln 2` with the constant `InvLn2N`, rounds `z` to an integer by adding and subtracting `0x1.8p52`, and forms `r = x - k · C1 - k · C2`, where `C1 + C2` approximates `ln 2/128`.  `C1 = 0x1.62e42fefa0000p-8` has 36 significant bits, so `k · C1` is exact for `|k|` up to 189,096, and `x - k · C1` is exact as well, since `x` and `k · C1` lie on a common grid.  This splitting of the constant into a head whose products are exact and a tail is Cody and Waite's reduction [7], as Boldo, Daumas, and Li describe it [8].  The computed `r` satisfies `|r| ≤ 1/256`, and it differs from the ideal residual `x - k ln 2/128` by at most `2^-60`.

The table holds, for each `j`, a head `H_j` with `1 ≤ H_j < 2` and a tail `T_j` with `|T_j| ≤ 2^-53`, such that `H_j (1 + T_j)` approximates `2^(j/128)`.  The stored head word is the bits of `H_j` less `j · 2^52/N`, so adding `k << 45` to it gives the bits of the scale `s = 2^q H_j` in one integer addition, with no separate exponent field arithmetic.  The polynomial `p(r) = r + r² (C2 + r C3) + r⁴ (C4 + r C5)` approximates `exp r - 1`, and the code evaluates `tmp = T_j + p(r)` and returns `s + s · tmp`, which approximates `s (1 + T_j) exp r`.

Four paths handle the rest of the domain.  Below `2^-54` in magnitude the result is `1 + x`, which differs from `exp x` by less than `x²`.  From 512 on, `specialcase` avoids an exponent that leaves the range of `s`: for positive `k` it scales `s` down by `2^1009` and multiplies the result by `2^1009`, and for negative `k` it scales `s` up by `2^1022` and multiplies by `2^-1022`.  When the scaled result `y` is below 1, the subnormal result would suffer two roundings, so the code first rounds `1 + y` with a compensated sum and subtracts 1, an exact operation, before the final product.  Arm's comment states that this compensation helps only for a goal better than one unit in the last place [1].  From 1024 on, `-∞` gives `+0`, other infinities and NaN give `1 + x`, and finite inputs give the products `2^-767 · 2^-767` and `2^769 · 2^769` of Arm's `__math_uflow` and `__math_oflow` [3], which round to `+0` and `+∞`.

## Implementation

The source is Arm's `math/exp.c` with the data of `math/exp_data.c` and the error products of `math/math_err.c`, at commit `503fafe311c177de0e571c458c7c337b1ca5f522` [1, 2, 3].  The files carry `Copyright (c) 2018-2025, Arm Limited` (`exp.c`), `2018-2023` (`exp_data.c`), and `2018` (`math_err.c`), all under `SPDX-License-Identifier: MIT OR Apache-2.0 WITH LLVM-exception` [4], and the module docstring of [the implementation](Exp.lean) repeats the notice.  The configuration is the one that `math/math_config.h` selects without rounding intrinsics or fast fused multiply-add: `EXP_TABLE_BITS` 7, `EXP_POLY_ORDER` 5, `EXP_POLY_WIDE` 0, and `EXP_USE_TOINT_NARROW` 0 [3].  For this configuration `exp_data.c` gives an absolute polynomial error of `1.555 · 2^-66` and a worst error of 0.511 units without fused multiply-add [2].

The port is written in the Verified dialect, the subset of Lean that [the Verified compiler](../README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [specialCase, expCore, expWith, exp]` generates the module, whose functions are `alloc` (0), `release` (1), `specialCase` (2), `expCore` (3), `expWith` (4), and `exp` (5).  Each constant is written as `Float.ofBits` of its bit pattern, and the table is an `Array UInt64` placed in a data segment and borrowed at address 4096.  `expWith` takes the table as a parameter, so that [the base-2 and base-10 exponentials](Exp2.lean), [the power function](Pow.lean), [the hyperbolic sine and cosine](Sinh.lean), and [the error function](Erf.lean) can call it or read the table.

| C code | Port | Reason |
|---|---|---|
| `exp_inline (x, xtail)` with `hastail` | `expCore tab x special`, without `xtail` | `exp` passes `xtail = 0`, and the tail code is dead for it. |
| `abstop = 0` marks the special path | the Boolean `special` | The dialect has no mutable locals. |
| 32-bit comparisons of `abstop - top12 (0x1p-54)` | 64-bit comparisons | The unsigned difference wraps for `abstop < 0x3c9` in both widths, and the wrapped value is at least `2^32 - 0x3c9` either way, so every comparison gives the same result; the docstring of `expWith` records this. |
| `WANT_ROUNDING` | assumed 1: `1.0 + x` for tiny `x`, and the test `y == 0.0` kept | Rounding is always to nearest. |
| `force_eval_double`, `check_oflow`, `check_uflow`, `errno` | omitted | WebAssembly has no floating-point status flags, and the dialect has no `errno`. |
| `__math_uflow (0)`, `__math_oflow (0)` | the products `0x1p-767 · 0x1p-767` and `0x1p769 · 0x1p769` | These are the calls' results with sign 0 [3]. |
| `__exp_data` global | the parameter `tab`, read with `tab[i]!` | The table is a borrowed array of the module. |

| Constant | Bits | Value |
|---|---|---|
| `InvLn2N` | `0x40671547652B82FE` | `0x1.71547652b82fep0 · 128`, exact |
| `Shift` | `0x4338000000000000` | `0x1.8p52` |
| `-C1` (`NegLn2hiN`) | `0xBF762E42FEFA0000` | `-0x1.62e42fefa0000p-8` |
| `-C2` (`NegLn2loN`) | `0xBD0CF79ABC9E3B3A` | `-0x1.cf79abc9e3b3ap-47` |
| `C2` to `C5` | `0x3FDFFFFFFFFFFDBD`, `0x3FC555555555543C`, `0x3FA55555CF172B91`, `0x3F81111167A4D017` | `0x1.ffffffffffdbdp-2`, `0x1.555555555543cp-3`, `0x1.55555cf172b91p-5`, `0x1.1111167a4d017p-7` |
| `2^1009`, `2^-1022` | `0x7F00000000000000`, `0x0010000000000000` | factors of `specialcase` |
| `2^-767`, `2^769` | `0x1000000000000000`, `0x7000000000000000` | factors of `math_err.c` |

The table `expTable` is Arm's `__exp_data.tab` for `N = 128`: 256 words, `T_j` at index `2j` and the adjusted head at `2j + 1`.  Three checks cover it.  `ExpTableBounds.checked_table_bounds` proves in the kernel, by `decide +kernel` on rationals, that `(H_j (1 + T_j) (1 - 2^-100))^128 ≤ 2^j ≤ (H_j (1 + T_j) (1 + 2^-100))^128` for every `j`, which gives `|H_j (1 + T_j) - 2^(j/128)| ≤ 2^-100 H_j (1 + T_j)`.  `ExpAccuracy.tableEntryOk` checks the same relation natively against a 400-bit reference.  For this document the 256 words and every constant above were compared with `exp_data.c` at the pinned commit by a script, and all agree.

## Theorems

The theorems are in [the exponential theorem module](ExpTheorem.lean) and [the file module](ExpFile.lean), in the namespaces `Verified.Examples.ExpTheorem` and `Verified.Examples.ExpFile`.  `x` is a Lean `Float`, `a = value x.toBits` its real value, and a word is the `UInt64` bit pattern of a double.  The byte theorem uses `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `exp_one_step` | For finite `x`, the word of `Exp.exp x` is at most `0x7FF0000000000000` and within one encoding step of the nonnegative nearest-even rounding of `Real.exp (value x.toBits)`. |
| `exp_pos_zero`, `exp_neg_zero` | `exp (±0)` has the bits `0x3FF0000000000000`. |
| `exp_pos_infinity`, `exp_neg_infinity` | `exp (+∞) = +∞` and `exp (-∞) = +0`, as bits. |
| `exp_nan` | For a NaN `x`, the result has the bits `Wasm.IEEE64.canonicalNaN`. |
| `saturated_bits` | From exponent field 1033 on (`|a| ≥ 1024`), the result is `+0` for negative and `+∞` for positive finite inputs. |
| `ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant, the table borrowed at 4096, and a memory cap of at most 65,535 pages. |
| `exp_entry_call` | A call of function 5 from a store satisfying `Ready` returns, without a trap, the bits of `Exp.exp x`, and leaves a store satisfying `Ready` in which every heap region keeps its bytes. |
| `exp_bytes_accuracy` | `Exp.compiled.module` encodes to bytes that decode to it, exports function 5 as `exp`, starts in a `Ready` store, and every call from a `Ready` store returns the bits of `Exp.exp x`, within one step for finite `x`, and leaves a `Ready` store.  The statement therefore covers every call in a sequence of calls to `exp`. |
| `exp_file` | `build/verified/exp.wasm` holds `encode Exp.compiled.module`. |
| `exp_file_decode` | `build/verified/exp.wasm` decodes to the module of `exp_bytes_accuracy`. |

Each declaration of `ExpTheorem.lean` has a `#print axioms` line, and the journal records that each reports `[propext, Classical.choice, Quot.sound]`.  The accepted builds are `opus-theorem-4.log` and `opus-calls-1.log` on the build host, the rebuild from source is `opus-fresh-1.log` on the build host, and the file theorems were first checked in `opus-exp-file-1.log`.  The logs are under `build/transcendentals/` in the primary checkout of each machine.  `tests/verified/run.sh` builds `Verified.Examples.ExpTheorem`, checks `ExpFile.lean` against the `exp.wasm` it has just written, and fails unless both file theorems report exactly the three permitted axioms.  The latest run in the primary checkout, `opus-verified-tests-13.log` of 2026-10-11, passed that check and printed the same report for `exp_one_step` and `exp_bytes_accuracy`.

## Proof

### Modules

The proof modules form one chain of 35 modules in `Verified/Examples/` above the implementation.  The table lists them by stage, in dependency order within each stage.  [The root `Verified` import](../../Verified.lean) reaches `ExpRelative` and the modules below it through the error function's proof, but not `ExpNegativeFinal`, `ExpFarRange`, or `ExpTheorem`, so `tests/verified/run.sh` builds `Verified.Examples.ExpTheorem` itself.

| Stage | Modules | Content |
|---|---|---|
| Table and constants | `ExpTableBounds`, `ExpReductionBounds`, `ExpApproximation` | The table enclosure, `C1 + C2` within `2^-99` of `ln 2/128`, and the polynomial within `2^-56` of `exp r - 1` for `|r| ≤ 1/256`. |
| Reduction | `ExpReductionExact`, `ExpIntegerSelection`, `ExpReductionSelection`, `ExpShiftedBits`, `ExpScaleFacts`, `ExpScaleEncoding`, `ExpScaleBits`, `ExpCoreState`, `ExpHighSubtraction`, `ExpHighPartBounds`, `ExpHighResidual`, `ExpResidualBounds`, `ExpResidualFloat` | The shift selects the nearest integer `k` for `|z| ≤ 2^18`; `k · C1` and `x - k · C1` are exact; the scale word is `2^q H_j`; the computed residual is within `2^-60` of the ideal one. |
| Evaluation and reconstruction | `ExpEvaluationBounds`, `ExpEvaluationFloat`, `ExpReconstructionBounds`, `ExpReducedReconstruction`, `ExpTableReconstruction`, `ExpCoreBounds` | The error budget below, ending in `ExpCoreBounds.core_error`. |
| Main path | `ExpCoreRange`, `ExpCoreInterval`, `ExpCoreOneStep`, `ExpBranches` | The position of `exp a` in its binade, one step for `2^-54 ≤ |a| ≤ 512`, and the tiny path. |
| Special paths | `ExpSpecialScale`, `ExpSpecialReconstruction`, `ExpSpecialPositiveCore`, `ExpOneStep`, `ExpSpecialPositive`, `ExpSpecialNegative`, `ExpNegativeFinal` | `512 ≤ |a| ≤ 768`, with the compensated subnormal path. |
| Far range and assembly | `ExpFarRange`, `ExpTheorem` | `768 < |a| < 1024`, saturation, exceptional values, and the byte theorem. |

`ExpRelative.expWith_relative`, outside this chain, bounds the relative error of `expWith` by `1.405 · 2^-53` for `|a| < 512`.  [The error function's proof](ErfPositive.lean) uses it for the factors `exp (-z² - 0.5625)` and `exp ((z - x)(z + x) + R/S)`.  [The base-2 and base-10 proofs](Exp2Core.lean) use `ExpTableBounds` and the saturating products of `ExpTheorem`.

### Error budget of the main path

Let `u = 2^-53`, `s = 2^q H_j` the scale, and `E = exp a`.  The lemmas bound each stage of `s + s · tmp` against `E`, for `|a| ≤ 512` on the main path and up to 768 on the special paths, where the bound applies to the scaled value.  From the third line on, each bound includes the ones above it.

| Stage | Bound | Lemma |
|---|---|---|
| Polynomial against `exp r - 1`, from Taylor's remainder `7 · 2^-60` and the coefficients' distance `5 · 2^-60` from `1/n!` | `2^-56` | `ExpApproximation.polynomial_error` |
| Evaluation of `T_j + p(r)` in floating point | `2^-56` | `ExpEvaluationBounds.evaluation_error` |
| Both, against `T_j + exp r - 1` | `2^-55` | `evaluation_exp_error` |
| `s + s · tmp` before the last rounding, against `s (1 + T_j) exp r` | `(37/128) u s` | `ExpReconstructionBounds.presum_error` |
| After the last rounding | `(4/3) u s` | `reconstruction_error` |
| Computed residual against the ideal residual, `s · 2^-58` | `(11/8) u s` | `ExpReducedReconstruction.reconstruction_ideal_error` |
| Table against `2^(j/128)`, `s · 2^-98` | `(7/5) u s` | `ExpTableReconstruction.table_reconstruction_error` |

A word within one and a half spacings of `E` lies within one step of the nearest-even rounding of `E`: rounding moves `E` by at most half a spacing, and a word two steps away from the rounded value lies at least one and a half spacings from `E`.  `F64FullStep.one_step_binades` states this, binade boundaries and the step to positive infinity included, and `ExpOneStep.one_step_of_error` applies it.  For `j ≠ 0`, `E` lies in `[2^q (1 + 1/4096), 2^q (2 - 1/65536)]`, whose spacing is `2u · 2^q`, and `H_j ≤ 255/128` (`ExpCoreRange.checked_head_bounds`), so the error is at most `2.79 u · 2^q` against the `3u · 2^q` allowed.  For `j = 0`, `E` lies in `[2^q · 319/320, 2^q · 257/256]` and may fall below `2^q`, so the allowance is one and a half spacings of the lower binade, `1.5 u · 2^q`, against an error of `1.4 u · 2^q`.  The margin is about 7 percent of the allowance in both cases.

| Range of `a` | Path | Bound before the final step | Theorem |
|---|---|---|---|
| `|a| < 2^-54` | `1 + x` | below `1.5 u` (`ExpTinyError.tiny_bounds`) | `ExpBranches.exp_small_one_step` |
| `2^-54 ≤ |a| < 512` | main path | `(7/5) u s` | `ExpBranches.exp_small_one_step` |
| `512 ≤ a ≤ 768` | `specialcase`, product with `2^1009` | `(7/5) u s` on the scaled value; the product is exact or `+∞` | `ExpSpecialPositive.positive_one_step` |
| `-768 ≤ a ≤ -512`, `y ≥ 1` | product with `2^-1022` | `(7/5) u s`; the product is exact | `ExpSpecialNegative.negative_one_step` |
| `-768 ≤ a ≤ -512`, `y < 1` | compensated sum, then `2^-1022 (z - 1)` | `((47/16) u + 3u²) · 2^-1022`, against `3u · 2^-1022` | `ExpNegativeFinal.compensated_one_step` |
| `768 < |a| < 1024` | `specialcase` with coarse bounds | scale above `2^98` gives `+∞`; scale below `2^-85` gives `+0` or the smallest subnormal, and `exp a ≤ 2^-1100` | `ExpFarRange.far_positive`, `far_negative` |
| `|a| ≥ 1024` | the saturating products | exact words `0` and `0x7FF0000000000000` | `ExpTheorem.saturated_bits` |

On the compensated path, `ExpSpecialNegative.comp_sum_bounds` shows that `hi + lo` rounds onto the grid of `2^-52` in `[1, 2]` within `2u + 3u² + u s/8` of `1 + s + p`, with `s < 2`, and `ExpNegativeFinal.comp_final` shows that `z - 1` and its product with `2^-1022` are exact.  The hypothesis of `compensated_one_step` allows `(11/16) u` for `s + p` against `2^1022 E`, and with `u s/8 ≤ u/4` the error of `z - 1` against `2^1022 E` is at most `(47/16) u + 3u²`.  The subnormal spacing is `2u · 2^-1022`, so the total stays below one and a half spacings by about 2 percent of the allowance.  Only relative rounding bounds and two exact subtractions enter, as Arm's comment anticipates.

### Shared modules

The proof imports 64 ProofKit modules, most of them the arithmetic chain of `F64Add`, `F64Mul`, and `F64Bits` that proves Lean's `Float` operations equal to Talos's `IEEE64` functions.  The modules specific to the error analysis are [the nonnegative rounding reference](../../LeanExe/ProofKit/F64PositiveRounding.lean), [one step against the full reference](../../LeanExe/ProofKit/F64FullStep.lean), [multiplication by a power of two](../../LeanExe/ProofKit/F64PowerScale.lean), [grid exactness](../../LeanExe/ProofKit/F64GridExact.lean), [exponent, magnitude, and sign](../../LeanExe/ProofKit/F64Magnitude.lean), [rounding stages](../../LeanExe/ProofKit/F64StageBounds.lean), [errors of rounded sums and products](../../LeanExe/ProofKit/RealRoundedError.lean), [the real exponential's Taylor bounds](../../LeanExe/ProofKit/RealExpError.lean), which specialize Mathlib's `Real.exp_bound` [13], and [the tiny path](../../LeanExe/ProofKit/ExpTinyError.lean).  [The transcendental plan](../../transcendentals.md#library-results-added-for-the-theorem) lists the library results added for this theorem.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| The table's 128 rational enclosures of `2^(j/128)` within `2^-100` | `ExpTableBounds.checked_table_bounds` |
| `1 ≤ H_j ≤ 2`, `|T_j| ≤ 2^-53`, and `H_j ≤ 255/128`, with `H_j ≥ 257/256` for `j ≠ 0` | `ExpTableBounds.checked_entry_magnitudes`, `ExpCoreRange.checked_head_bounds` |
| The sign and exponent fields of the heads, and the head word plus `j · 2^45` | `ExpScaleFacts.checked_head_fields` |
| The Taylor sums of `exp` with 40 terms and their remainder at `128 (C1 + C2) ∓ 2^-92` bracket 2, so `ln 2` lies within `2^-92` of `128 (C1 + C2)`; `InvLn2N · ln 2/128` lies within `2^-53` of 1 | `ExpReductionBounds.checked_log_brackets`, `checked_inverse_bounds` |
| The saturating products give `0` and `0x7FF0000000000000` | `ExpTheorem.underflow_product`, `overflow_product` |
| Function 5 is exported as `exp` | `ExpTheorem.exp_export` |
| The file's bytes equal the encoder's | `ExpFile.exp_file` |

### History

GPT's proof covered `|a| < 512` and stopped before the final scaling of the special paths, as [its failure account](../../devnotes.md#2026-10-09-failure-account-and-stopped-gpt-work) records.  Opus reviewed GPT's statements, widened hypotheses that the proofs already allowed, and finished the theorem on 2026-10-09 ([the journal section](../../devnotes.md#2026-10-09-full-exponential-theorem-opus)).  The split at 768 is GPT's and stays so that its lemmas remain usable, although any split between the finite range of `exp` and 1024 would do.  The far range needs coarse bounds because `k · C1` is exact only for `|k| ≤ 189,096`, and inputs just below 1024 select `|k| = 189,097`.  `borrowed_kept` states the table frame for an arbitrary array, because the concrete table made elaboration reduce the size of a literal array of 256 words and stop at the recursion limit ([the review](../../devnotes.md#2026-10-10-review-of-the-exponential-theorem)).

## Tests

[The accuracy check](ExpAccuracy.lean) compares `Exp.exp` natively with the double nearest to `exp x` computed by [the integer reference](Reference.lean) with at least 400 bits after the binary point, and it fails at the first result more than one step away.  It first checks every table entry against `2^(j/128)` within `2^-100`.  Its 180,095 arguments are 120,001 evenly spaced values from -745.5 to 710, 60,000 hashed values with exponents from `2^-60` to `2^10` and both signs, the five doubles at and around each of 15 thresholds of the code and of overflow and underflow, nine special values, and the ten inputs of `WorstCases.exp`.  Those ten are the double-precision inputs that give the largest known `exp` errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [12], whose Table 3 lists 0.511 units for GNU libc 2.44, Musl, and the Arm Performance Library and 0.949 for FreeBSD 15.1.

In `opus-verified-tests-13.log` all 180,095 results lie within one step of the reference, and 150 of them differ from it.  The largest measured distance therefore equals the proved bound.  The C library on the build host lies within one step at the same arguments, with 118 results unequal to the reference.  The reference's truncation errors are stated in its docstrings and are below `2^-230` relative.  They are not proved, and a reference rounded the wrong way could only move a one-step check between passing results.

## Limits

The theorem is about Talos's semantics of WebAssembly.  The Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode` are trusted, as [the design notes](../../docs/design.md#scope-of-the-theorem) record.  The WebAssembly testsuite run of 2026-10-10 passed 64,751 commands with no failure, and the decoder test decoded 712 valid modules and rejected 676 malformed ones.  The file theorem trusts the elaborator `binary_file%`, which reads `exp.wasm`.  Talos implements the deterministic profile, in which every NaN result is canonical [11], and an engine outside that profile, such as a browser, may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, and every NaN `Float` has the canonical bits, so the theorem covers only the canonical NaN among the `2^53 - 2` NaN words a WebAssembly caller can pass.  For another NaN word the compiled code reaches `1.0 + x`, which returns the canonical NaN in Talos, but no theorem states it.  `exp_bytes_accuracy` covers sequences of calls to `exp` only: the module also exports `alloc`, `release`, `specialCase`, `expCore`, `expWith`, its memory, and the globals `allocCount` and `freeCount`, and a host that calls another export or writes the table between calls needs a theorem that the action preserves `Ready`. 

## References

1. Arm Limited, optimized-routines, [`math/exp.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/exp.c), commit `503fafe311c177de0e571c458c7c337b1ca5f522`.  Copyright (c) 2018-2025, Arm Limited, MIT OR Apache-2.0 WITH LLVM-exception.
2. Arm Limited, optimized-routines, [`math/exp_data.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/exp_data.c), same commit: the table, the reduction constants, and the polynomial with its stated errors.
3. Arm Limited, optimized-routines, [`math/math_err.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/math_err.c) and [`math/math_config.h`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/math_config.h), same commit.
4. Arm Limited, optimized-routines, [`LICENSE`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/LICENSE), same commit.
5. P. T. P. Tang, "Table-driven implementation of the exponential function in IEEE floating-point arithmetic", *ACM Transactions on Mathematical Software* 15(2):144–157, June 1989, [doi:10.1145/63522.214389](https://doi.org/10.1145/63522.214389).  The bibliographic data were confirmed in Crossref.  The publisher's site refused automated access, so the paper's text was not read, and the description above rests on reference 6.
6. J. Harrison, T. Kubaska, S. Story, and P. T. P. Tang, ["The Computation of Transcendental Functions on the IA-64 Architecture"](https://www.cl.cam.ac.uk/~jrh13/papers/itj.pdf), *Intel Technology Journal*, Q4 1999.  Its introduction describes the reduction `x = N ln 2/2^K + r`, the table of `2^(d/32)`, and the reconstruction of the table-driven framework, citing reference 5.
7. W. J. Cody, Jr. and W. Waite, *Software Manual for the Elementary Functions*, Prentice-Hall, 1980.  The book was not consulted.  Its identity was confirmed through the review in *SIAM Review* 24(1):91–93, 1982, [doi:10.1137/1024023](https://doi.org/10.1137/1024023), and the method through reference 8.
8. S. Boldo, M. Daumas, and R.-C. Li, "Formally Verified Argument Reduction with a Fused Multiply-Add", *IEEE Transactions on Computers* 58(8):1139–1145, 2009, [doi:10.1109/TC.2008.216](https://doi.org/10.1109/TC.2008.216); preprint [arXiv:0708.3722](https://arxiv.org/abs/0708.3722).  The abstract describes Cody and Waite's reduction and its loss of accuracy for large arguments.
9. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229).  Clause 4.3.1 (the overflow threshold `b^emax (b - ½ b^(1-p))`), clause 9.2 (recommended operations, correct rounding, NaN operands), and clause 9.2.1 (special values) were read.
10. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.3.1, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
11. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
12. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
13. The Mathlib Community, Mathlib at commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`, [`Mathlib/Analysis/Complex/Exponential.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/Complex/Exponential.lean), `Real.exp_bound`.
