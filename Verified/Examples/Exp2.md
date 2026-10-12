# The base-2 and base-10 exponentials

[The implementation](Exp2.lean) exports `exp2` and `exp10`, ports of Arm's optimized-routines `exp2` and `exp10` [1, 2] in their configuration without fused multiply-add, which share the table of 128 values of `2^(j/128)` with [the exponential](Exp.lean).  The decided bound, which [the plan's table of functions](../../transcendentals.md#functions) records, is one representable step from the nearest-even rounding of `2^a` and of `10^a`.  `Exp2Theorem.exp2_within` and `Exp10Theorem.exp10_within` prove the bounds for every finite binary64 input, ten theorems give the exceptional values exactly, and `Exp2Bytes.exp2_bytes_accuracy` and `exp10_bytes_accuracy` carry them to the decoded WebAssembly module, with `Exp2File.exp2_file` connecting that module to the file `build/verified/exp2.wasm`.  Every theorem below reports no axioms other than `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`exp2` computes `(2 : ℝ) ^ a` and `exp10` computes `(10 : ℝ) ^ a`, where `a` is the value of the argument and `^` is Mathlib's real power `Real.rpow`, which `Real.rpow_def_of_pos` equates with `exp (log b · a)` for a positive base `b` [14].  Every finite double is in the domain of both.  The results overflow to `+∞` from the threshold `2^1024 - 2^970` of clause 4.3.1 of IEEE 754-2019 [10], which `exp2` reaches from `a = 1024` on and `exp10` from `a = 0x1.34413509f79ffp8` on, and they round to `+0` at or below `2^-1075`, which `exp2` reaches at `a = -1075` and `exp10` near `a = -323.6`.

The bound is `F64SignedRounding.WithinSteps 1`, defined in [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean).  `WithinSteps n y w` states that the word `w` is not a NaN and that its position differs by at most `n` from the position of the nearest-even reference of `y`, where `position` places both zeros at 0 and the infinities next to the largest finite doubles.  `F64SignedRounding.within_of_nonneg` derives it, for a nonnegative `y`, from the three encoding inequalities in which `ExpTheorem.exp_one_step` states `exp`'s bound.

| Input | `exp2` | `exp10` | Source of the rule | Theorems |
|---|---|---|---|---|
| `+0`, `-0` | `1` | `1` | IEEE 754-2019 9.2.1 [10]; C99 F.9.3.2 for `exp2` [11]; C23 F.10.3.2 for `exp10` [12] | `exp2_pos_zero`, `exp2_neg_zero`, `exp10_pos_zero`, `exp10_neg_zero` |
| `+∞` | `+∞` | `+∞` | the same clauses | `exp2_pos_infinity`, `exp10_pos_infinity` |
| `-∞` | `+0` | `+0` | the same clauses | `exp2_neg_infinity`, `exp10_neg_infinity` |
| NaN | the canonical NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [13] | `exp2_nan`, `exp10_nan` |
| finite, result at least `2^1024 - 2^970` | `+∞` | `+∞` | IEEE 754-2019 4.3.1 | `exp2_within`, `exp10_within` |
| finite, result at most `2^-1075` | `+0`, or the smallest subnormal within the bound | the same | IEEE 754-2019 4.3.1 | `exp2_within`, `exp10_within` |

C99 has `exp2` but no `exp10`.  C23 adds `exp10` in clause 7.12.6.2, with its special values in F.10.3.2, as the WG14 working draft N3220 gives them [12].  IEEE 754-2019 lists both among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [10], and Arm states worst errors of 0.511 units for `exp2` and about 0.513 units for `exp10`, so neither port is correctly rounded [3, 2].

## Algorithm

Both functions use the table-driven method of the exponential [6, 7]: write the argument as `k/128 + r` in base 2, so that the result is `2^(k/128) · 2^r`, take `2^(k/128) = 2^q · 2^(j/128)` with `k = 128 q + j` from the table, and approximate `2^r` or `10^r` by a polynomial.  The table, its head and tail words, and the scale `s = 2^q H_j` formed by one integer addition are those that [the exponential's documentation](Exp.md#algorithm) describes.  The functions differ in their reductions and polynomials.

`exp2` needs no constant in its reduction.  Adding `0x1.8p52/128 = 3 · 2^44` to `x` rounds `x` to the nearest multiple of `1/128`, since for `|x| ≤ 2^12` the sum lies in `[2^45, 2^46)`, whose spacing is `2^-7`.  Subtracting the shift gives `k/128` exactly, and `r = x - k/128` is exact with `|r| ≤ 1/256`.  The polynomial `C1 r + r² (C2 + r C3) + r⁴ (C4 + r C5)` approximates `2^r - 1 = exp (r log 2) - 1`, with `C1` near `log 2`.

`exp10` computes `z = x · 128/log10 2`, rounds it to the integer `k` with the shift `0x1.8p52` as `exp` does, and forms `r = x - k · log10 2/128` with the constant split into a 32-bit head and a tail, so that `k` times the head is exact and adding `x` is exact.  This is Cody and Waite's reduction [8], as Boldo, Daumas, and Li describe it [9].  The computed `r` lies within `2^-61` of `x - k · log10 2/128`, and both are at most `1/850` in magnitude.  The polynomial `r (C0 + r C1 + r² ((C2 + r C3) + r² C4))` approximates `10^r - 1`, with `C0` near `log 10`, and the result is `s · tmp + s` in place of `exp`'s `s + s · tmp`.

The special paths follow `exp`'s, with one change.  Below `2^-54` (`exp2`) or `2^-57` (`exp10`) in magnitude the result is `1 + x` or `x + 1`.  Near overflow and underflow, for `|x| > 928` in `exp2` and `|x| ≥ 256` in `exp10`, both functions call `exp2SpecialCase`, which is `exp2.c`'s `specialcase` and `exp10.c`'s `special_case`, the same code [1, 2].  For a positive `k` it lowers the scale by one binade and doubles the rounded sum, where `exp.c` lowers it by 1009 binades and multiplies by `2^1009`.  For a negative `k` it raises the scale by `2^1022`, compensates a sum below 1 as `exp` does, and multiplies by `2^-1022`.  Beyond the finite range the functions return the products `2^769 · 2^769` and `2^-767 · 2^-767` of `__math_oflow` and `__math_uflow` [4].

## Implementation

The sources are Arm's `math/exp2.c` (`Copyright (c) 2018-2025, Arm Limited`), `math/exp10.c` (`2023-2025`), and the data of `math/exp_data.c` (`2018-2023`), at commit `503fafe311c177de0e571c458c7c337b1ca5f522`, under `SPDX-License-Identifier: MIT OR Apache-2.0 WITH LLVM-exception` [1, 2, 3, 5].  The module docstring of [the implementation](Exp2.lean) repeats the notice.  The configuration is `Exp.lean`'s: `EXP_TABLE_BITS` 7, `EXP2_POLY_ORDER` 5, `EXP2_POLY_WIDE` 0, `EXP10_POLY_WIDE` 0, and no rounding intrinsics or fused multiply-add [4].  For it `exp_data.c` states an absolute polynomial error of `1.2195 · 2^-65` for `exp2` on `|r| < 1/256` and 0.511 units without fused multiply-add, and `exp10.c` states a largest observed error of about 0.513 units [3, 2].

`verified_compile compiled := [exp2SpecialCase, exp2Core, exp2With, exp10Core, exp10With, exp2, exp10]` generates the module, whose functions are `alloc` (0), `release` (1), and the seven functions of the list (2 to 8), so that `exp2` is function 7 and `exp10` function 8.  `wasm-tools print` of `exp2.wasm` shows every function exported, with the memory and the globals `allocCount` and `freeCount`.  `exp2` and `exp10` pass `Exp.expTable` to `exp2With` and `exp10With`, and the module holds that table in a data segment borrowed at address 4096.  `exp_data.c`'s `__exp_data.tab` for `N = 128` equals `Exp.expTable` word for word, as [the journal section on the ports](../../devnotes.md#2026-10-10-ports-of-exp2-exp10-log2-log10-and-pow) records.  The port calls no function of `Exp`.

| C code | Port | Reason |
|---|---|---|
| `abstop = 0` marks the special path | the Boolean `special` of `exp2Core` and `exp10Core` | The dialect has no mutable locals. |
| `exp2`'s nested tests from `abstop ≥ top12 (1024)` on, which fall through to the test `2 · asuint64 (x) > 2 · asuint64 (928)` for `-1075 < x ≤ -1024` | one chain of tests joined by `&&`, ending in `exp2Core` with the flag `2 · x.toBits > 2 · 0x408D000000000000` | The dialect has no fall-through.  Every input selects the same branch as in C. |
| 32-bit comparisons of `abstop` | 64-bit comparisons | As in `Exp.lean`, the wrapped difference exceeds the thresholds in both widths. |
| `WANT_ROUNDING` | assumed 1 | WebAssembly arithmetic rounds to nearest, ties to even. |
| `force_eval_double`, `check_oflow`, `check_uflow` | omitted | WebAssembly has no floating-point status flags. |
| `__math_oflow (0)`, `__math_uflow (0)` | the products `0x1p769 · 0x1p769` and `0x1p-767 · 0x1p-767` | These are the calls' results with sign 0 [4]. |
| `__exp_data` fields | constants written as bit patterns, products and quotients by `N` included | The dialect has no global data other than borrowed tables. |

| Constant | Bits | Value in Arm's source |
|---|---|---|
| `exp2` shift | `0x42C8000000000000` | `0x1.8p52 / N` |
| `exp2` `C1` to `C5` | `0x3FE62E42FEFA39EF`, `0x3FCEBFBDFF82C424`, `0x3FAC6B08D70CF4B5`, `0x3F83B2ABD24650CC`, `0x3F55D7E09B4E3A84` | `0x1.62e42fefa39efp-1`, `0x1.ebfbdff82c424p-3`, `0x1.c6b08d70cf4b5p-5`, `0x1.3b2abd24650ccp-7`, `0x1.5d7e09b4e3a84p-10` |
| `exp10` shift | `0x4338000000000000` | `0x1.8p52` |
| `invlog10_2N` | `0x407A934F0979A371` | `0x1.a934f0979a371p1 · N`, exact |
| `neglog10_2hiN`, `neglog10_2loN` | `0xBF63441350A00000`, `0x3D10C0219DC1DA99` | `-0x1.3441350ap-2 / N`, `0x1.0c0219dc1da99p-39 / N` |
| `exp10` `C0` to `C4` | `0x40026BB1BBB55516`, `0x40053524C73CE9FE`, `0x4000470591CE4B26`, `0x3FF2BD76577FE684`, `0x3FE1446EECCD0EFB` | `0x1.26bb1bbb55516p1`, `0x1.53524c73ce9fep1`, `0x1.0470591ce4b26p1`, `0x1.2bd76577fe684p0`, `0x1.1446eeccd0efbp-1` |
| `OFlowBound`, `UFlowBound` | `0x40734413509F79FF`, `0xC075E00000000000` | `0x1.34413509f79ffp8`, `-0x1.5ep+8 = -350` |
| `exp2` thresholds | `0xC090CC0000000000`, `0x408D000000000000` | `-1075.0`, `928.0` |
| factors | `0x0010000000000000`, `0x7000000000000000`, `0x1000000000000000` | `2^-1022`, `2^769`, `2^-767` |

These 22 bit patterns are the binary64 values of their expressions in `exp_data.c`, `exp2.c`, `exp10.c`, and `math_err.c` at the pinned commit, with the products and quotients by `N` evaluated in binary64.  The kernel checks the coefficients' distance from `(log 2)^n/n!` and `(log 10)^n/n!`, the two-part constant's distance from `log10 2/128`, and the overflow and underflow bounds, as the next sections list.  The table carries `exp`'s kernel checks, `ExpTableBounds.checked_table_bounds` among them, since its words are `exp`'s.

## Theorems

The theorems are in [the base-2 theorem module](Exp2Theorem.lean), [the base-10 theorem module](Exp10Theorem.lean), [the byte theorem module](Exp2Bytes.lean), and [the file module](Exp2File.lean).  `x` is a Lean `Float`, `a = value x.toBits` its real value, and a word is the `UInt64` bit pattern of a double.  The byte theorems use `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `Exp2Theorem.exp2_within` | For finite `x`, `WithinSteps 1 ((2 : ℝ) ^ a) (Exp2.exp2 x).toBits`. |
| `Exp10Theorem.exp10_within` | For finite `x`, `WithinSteps 1 ((10 : ℝ) ^ a) (Exp2.exp10 x).toBits`. |
| `exp2_pos_zero`, `exp2_neg_zero`, `exp10_pos_zero`, `exp10_neg_zero` | The result for `±0` has the bits `0x3FF0000000000000`. |
| `exp2_pos_infinity`, `exp10_pos_infinity` | The result for `+∞` has the bits `0x7FF0000000000000`. |
| `exp2_neg_infinity`, `exp10_neg_infinity` | The result for `-∞` has the bits `0`. |
| `exp2_nan`, `exp10_nan` | For a NaN `x`, the result has the bits `Wasm.IEEE64.canonicalNaN`. |
| `Exp2Bytes.ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant, `Exp.expTable` borrowed at 4096, and a memory cap of at most 65,535 pages. |
| `exp2_entry_call`, `exp10_entry_call` | A call of function 7 or 8 from a store satisfying `Ready` returns, without a trap, the bits of `Exp2.exp2 x` or `Exp2.exp10 x`, and leaves a store satisfying `Ready` in which every heap region keeps its bytes. |
| `exp2_bytes_accuracy`, `exp10_bytes_accuracy` | `Exp2.compiled.module` encodes to bytes that decode to it, exports function 7 as `exp2` (8 as `exp10`), starts in a `Ready` store, and every call from a `Ready` store returns the bits of the Lean function, within one step for finite `x`, and leaves a `Ready` store.  Each statement therefore covers every call in a sequence of calls to its entry. |
| `exp2_module_accuracy` | The conjunction of the two byte theorems. |
| `Exp2File.exp2_file` | `build/verified/exp2.wasm` holds `encode Exp2.compiled.module`. |
| `Exp2File.exp2_file_decode` | `build/verified/exp2.wasm` decodes to the module of `exp2_module_accuracy`. |

Every theorem in the table has a `#print axioms` line.  The journal records only `propext`, `Classical.choice`, and `Quot.sound` for every theorem of the `exp2` modules in `exp2-theorem-3.log`, for the `exp10` modules in `exp10-theorem-1.log`, and for the byte theorems in `exp2-bytes-2.log`, logs on debtop1.  `opus-merge-exp2-1.log`, the build that merged both theorems into `transcendentals`, reports the same for both byte theorems and `exp2_module_accuracy`, under `build/transcendentals/` in `/home/somebody/src/leanexe-transcendentals` on minideb1.  `tests/verified/run.sh` builds `Verified.Examples.Exp2Bytes`, checks `Exp2File.lean` against the `exp2.wasm` that it writes earlier in the same run, and fails unless both file theorems report exactly the three permitted axioms.  `exp2_file_decode` depends on both byte theorems through `exp2_module_accuracy`, so its report covers both.  Its run of 2026-10-11 on minideb1, `opus-verified-tests-14.log`, passed that check and printed the permitted report for every theorem in the table.

## Proof

### Modules

The proof adds 18 modules in `Verified/Examples/` to the chain of `ExpTheorem`, whose table, scale, one-step, and compensated-subnormal lemmas it reuses.  The table lists them by stage, in dependency order within each stage.  [The root `Verified` import](../../Verified.lean) does not reach them, so `tests/verified/run.sh` builds `Verified.Examples.Exp2Bytes` as a separate target.

| Stage | Modules | Content |
|---|---|---|
| Polynomials | `Exp2Approximation`, `Exp10Constants`, `Exp2Evaluation`, `Exp10Evaluation` | The coefficients against `(log 2)^n/n!` and `(log 10)^n/n!`, the polynomials within `2^-58` of `2^r - 1` on `\|r\| ≤ 1/256` and within `2^-57` of `10^r - 1` on `\|r\| ≤ 1/850`, and their rounded evaluations. |
| Reductions | `Exp2Selection`, `Exp10Reduction` | `exp2`'s exact `k/128` and residual, and `exp10`'s `k` within `1/2 + 2^-31` of `x · 128/log10 2` and its residual within `2^-61` of the ideal one. |
| Shared reconstruction | `ArmReconstruction`, `ArmSpecial`, `ArmScale` | `s + s · w` and the two special paths for any polynomial word `w` within `2^-56` of `T_j + ρ - 1`. |
| Paths | `Exp2Core`, `Exp2Paths`, `Exp10Core`, `Exp10Paths` | The state of each core and one step on its three paths. |
| Assembly | `Exp2Branches`, `Exp2Theorem`, `Exp10Theorem` | The branches of `exp2With` and `exp10With`, the tiny, overflow, and underflow cases, and the exceptional values. |
| Bytes | `Exp2Bytes`, `Exp2File` | `Ready`, the entry calls, the byte theorems, and the file theorems. |

`exp`'s reconstruction lemmas concern `exp`'s residual and evaluation words.  `ArmReconstruction` generalizes them over a polynomial word `w` and a real factor `ρ`, which is `2^r` for `exp2` and `10^r` for `exp10`, and the proof reuses `ExpOneStep.one_step_of_error`, `ExpScaleBits`, `ExpSpecialScale`, and `ExpSpecialNegative.compensated_one_step` of `ExpNegativeFinal.lean` unchanged ([the journal section](../../devnotes.md#2026-10-11-the-exp2-theorem-track-exp2-debtop1)).  `exp2`'s key `0x42C8000000000000 + k`, raised by `7 · 2^52`, has the form `0x4338000000000000 + k` of `exp`'s key with the same low 19 bits (`Exp2Core.key_scale`), and `exp10`'s key has that form, so the scale and tail words are `exp`'s for `k = 128 q + j`.

### Error budget

Let `u = 2^-53`, `s = 2^q H_j` the scale, `ρ` the factor the polynomial approximates, and `E = 2^q · exp (j log 2/128) · ρ` the exact result.  The bounds hold on the ordinary paths, `|a| ≤ 928` for `exp2` and `|a| < 256` for `exp10`, and for the scaled sums of the special paths.  From the third line on, each bound includes the ones above it.

| Stage | `exp2` | `exp10` | Lemmas |
|---|---|---|---|
| Polynomial against `ρ - 1` | `2^-58` | `2^-57` | `Exp2Approximation.polynomial_error`, `Exp10Evaluation.polynomial_error` |
| Evaluation in floating point | `2^-57` | `2^-58` | `Exp2Evaluation.evaluation_error`, `Exp10Evaluation.evaluation_error` |
| Polynomial word against `T_j + ρ - 1`, with `exp10`'s residual error of `2^-61` carried into `ρ` | `2^-56` | `2^-56` | `Exp2Evaluation.evaluation_exp_error`, `Exp10Core.core_state` |
| `s + s · w` before the last rounding, against `s (1 + T_j) ρ` | `(21/128) u s` | `(21/128) u s` | `ArmReconstruction.presum_general` |
| After the last rounding | `(6/5) u s` | `(6/5) u s` | `ArmReconstruction.reconstruction_general` |
| Table against `2^(j/128)` | `s · 2^-98` more | `s · 2^-98` more | `ArmReconstruction.table_general` |

`ExpOneStep.one_step_of_error` accepts `(7/5) u s`, which lies 7 percent below one and a half spacings of `E`, as [the exponential's error budget](Exp.md#error-budget-of-the-main-path) explains.  Against that allowance the ordinary path's `(6/5) u s + 2^-98 s` leaves about 14 percent, and against one and a half spacings about 20 percent.

| Range of `a` | Path | Theorem |
|---|---|---|
| `exp2`: `\|a\| < 2^-54` | `1 + x`, within `11/8` units of roundoff of `2^a` (`F64RelativeStep`) | `Exp2Theorem.tiny_within` |
| `exp2`: `2^-54 ≤ \|a\| ≤ 928` | ordinary reconstruction | `Exp2Paths.ordinary_within` |
| `exp2`: `928 < a ≤ 1024 - 2^-43` | scale lowered by one binade, sum doubled exactly since `2^a ≤ 2^1024 - 2^980` keeps it below `2^1023` | `Exp2Paths.positive_within` |
| `exp2`: `-1075 < a < -928` | scale raised by `2^1022`, compensated below 1, product with `2^-1022` | `Exp2Paths.negative_within` |
| `exp2`: `a ≥ 1024` | overflow product, `+∞` | `Exp2Theorem.overflow_within` |
| `exp2`: `a ≤ -1075` | underflow product, `+0`, against `2^a ≤ 2^-1075` | `Exp2Theorem.zero_within` |
| `exp10`: `\|a\| < 2^-57` | `x + 1` | `Exp10Theorem.tiny_within` |
| `exp10`: `2^-57 ≤ \|a\| < 256` | ordinary reconstruction `s · w + s` | `Exp10Paths.ordinary_within` |
| `exp10`: `256 ≤ a ≤ 0x1.34413509f79fep8` | scale lowered and sum doubled, with `10^a ≤ 2^1024 - 2^980` | `Exp10Paths.positive_within` |
| `exp10`: `-350 ≤ a ≤ -256` | scale raised, compensated below 1 | `Exp10Paths.negative_within` |
| `exp10`: `a ≥ 0x1.34413509f79ffp8` | overflow product, with `10^a ≥ 2^1024` | `Exp10Theorem.exp10_within` |
| `exp10`: `a < -350` | underflow product, with `10^a ≤ 10^-350 ≤ 2^-1075` | `Exp10Theorem.exp10_within` |

On the negative special path `ArmSpecial.negative_within` applies `ExpSpecialNegative.compensated_one_step`, whose hypothesis allows `(11/16) u` for `s + p` against `2^1022 E`.  The presum bound `(21/128) u s` with `s < 2` gives at most `(21/64) u`, `(23/64) u` inside that allowance, and the lemma's conclusion carries the margin of about 2 percent that the exponential's documentation computes.  The overflow test of `exp10` agrees with the reference: `Exp10Constants.checked_reduction` shows that `10^a ≥ 2^1024` at `0x1.34413509f79ffp8`, and that the double below it gives `10^a ≤ 2^1024 - 2^980`, which the doubled path handles without overflow.

### Shared modules

The proof imports 71 ProofKit modules.  Beyond those of the exponential's proof, it uses [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean), [error tracking through chains of rounded operations](../../LeanExe/ProofKit/F64ErrorTrack.lean), [exact products of words](../../LeanExe/ProofKit/F64ExactProduct.lean), [the bits of a word from its scaled value](../../LeanExe/ProofKit/F64BinadeWord.lean), [one step from a relative bound of 11/8 units of roundoff](../../LeanExe/ProofKit/F64RelativeStep.lean), [the borrowed-table frame](../../LeanExe/ProofKit/BorrowedKept.lean), and `ratOfWord` from [the kernel-checked polynomial bound](../../LeanExe/ProofKit/PolyBound.lean).  This proof added `F64BinadeWord` to ProofKit.  `F64ErrorTrack.Approx` carries the evaluation's rounding errors through `exp2`'s polynomial.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| `exp2`'s coefficients within `2^-55`, `2^-46`, `2^-37`, `2^-28`, and `2^-22` of `(log 2)^n/n!` on the rational enclosure of `log 2` | `Exp2Approximation.checked_coefficients` |
| `log 10 = 3 log 2 + log (5/4)` enclosed within `2^-88` by `exp`'s enclosure of `log 2` and 45 terms of the series of `log (5/4)` | `Exp10Constants.checked_log_ten` |
| `exp10`'s coefficients within `2^-51` to `2^-12` of `(log 10)^n/n!` | `Exp10Constants.checked_coefficients` |
| The two-part constant within `2^-85` of `log10 2/128`, `invlog10_2N` within `2^-40` of `128/log10 2`, the overflow and underflow bounds, and `1075 log 2 ≤ 350 log 10` | `Exp10Constants.checked_reduction` |
| The residual bounds `1/850` and `1/512` | `Exp10Reduction.checked_margins` |
| The high part's scaled magnitude `2585827973 · 2^1034`, a 32-bit significand | `Exp10Reduction.high_magnitude` |
| Functions 7 and 8 are exported as `exp2` and `exp10` | `Exp2Bytes.exp2_export`, `exp10_export` |
| The file's bytes equal the encoder's | `Exp2File.exp2_file` |

### History

The journal sections on [the `exp2` theorem](../../devnotes.md#2026-10-11-the-exp2-theorem-track-exp2-debtop1) and [the `exp10` theorem](../../devnotes.md#2026-10-11-the-exp10-theorem-and-the-byte-theorems-track-exp2-debtop1) record the failed runs.  One failure shaped the modules: Lean panicked with `Nat.pow exponent is too big` because `linarith` preprocesses every hypothesis with `norm_num`, whose `rpow` extension tried to evaluate `(2 : ℝ) ^ ((1024 : ℝ) - 1 / 2 ^ 43)` exactly.  The proof states the exponential bound in its own lemma, `Exp2Paths.top_bound`, so that no such hypothesis is in context, and keeps `linarith` away from real powers with numeral exponents.  The first `positive_within` assumed `E ≤ 2^1024 - 2^984`, which fails for the double below 1024, and the accepted one assumes `E ≤ 2^1024 - 2^980`.

## Tests

[The accuracy check](Exp2Accuracy.lean) compares `exp2` and `exp10` natively with the doubles nearest to `2^x` and `10^x` from [the power references](PowerReference.lean), which compute `2^x` from the series of `exp` at `(x - k) log 2` for the integer `k` nearest `x` and `10^x` from `Reference.exp` at `x log 10`, within a relative `2^-390` and `2^-386`.  It fails at the first result more than one step away.  The 204,309 arguments of `exp2` are 100,001 evenly spaced values from -1100 to 1100, 100,000 hashed values with magnitudes from `2^-60` to `2^10` and both signs, the 2,111 integers from -1080 to 1030 with the half above each, 4,222 values, the five doubles at and around twelve thresholds (`±2^-54`, `±512`, `±928`, `±1024`, -1022, -1074, -1075, and -1076), 15 special values, and the 11 inputs of `WorstCases.exp2`.  The 200,717 arguments of `exp10` are 100,001 evenly spaced values from -400 to 400, 100,000 hashed values, the integers from -330 to 310, the doubles around `±2^-57`, `±256`, `±0x1.34413509f79ffp8`, `±350`, and `±307.65`, the 15 special values, and the 10 inputs of `WorstCases.exp10`.

The worst-case inputs are those that give the largest known errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [15].  Its Table 3 lists for `exp2` 0.511 units for GNU libc 2.44 and Musl, 0.509 for the Arm Performance Library, and 0.751 for FreeBSD 15.1, and for `exp10` 0.513 units for GNU libc 2.44 and 0.510 for the Arm Performance Library, with no entry for FreeBSD.  In `opus-verified-tests-14.log` all 204,309 results of `exp2` lie within one step of the reference, 311 of them unequal to it, and all 200,717 results of `exp10` lie within one step, 115 of them unequal, so the largest measured distance equals the proved bound for both functions.  The C library's `exp2` on minideb1 also has 311 results unequal to the reference, which fits glibc's use of Arm's routine, and Lean has no binding of `exp10` for a comparison.  The references' docstrings state their truncation errors, and no theorem proves them.  Such an error can change a reference only for an exact value within that distance of a midpoint between two doubles.

## Limits

The theorems are about Talos's semantics of WebAssembly.  They trust the Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode`, as [the design notes](../../docs/design.md#scope-of-the-theorem) record, and the file theorem trusts the elaborator `binary_file%`, which reads `exp2.wasm`.  Talos implements the deterministic profile, in which every NaN result is canonical [13], and an engine outside that profile may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, and every NaN `Float` has the canonical bits, so the theorems cover only the canonical NaN among the `2^53 - 2` NaN words a WebAssembly caller can pass.  For another NaN word the compiled code reaches `1 + x` (`exp2`) or `x + 1` (`exp10`), which returns the canonical NaN in Talos, but no theorem states it.  The byte theorems cover sequences of calls to `exp2` or to `exp10` from a `Ready` store.  The module also exports `alloc`, `release`, `exp2SpecialCase`, `exp2Core`, `exp2With`, `exp10Core`, `exp10With`, its memory, and the globals `allocCount` and `freeCount`, and a host that calls another export or writes the table between calls needs a theorem that the action preserves `Ready`.

## References

1. Arm Limited, optimized-routines, [`math/exp2.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/exp2.c), commit `503fafe311c177de0e571c458c7c337b1ca5f522`.  Copyright (c) 2018-2025, Arm Limited, MIT OR Apache-2.0 WITH LLVM-exception.
2. Arm Limited, optimized-routines, [`math/exp10.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/exp10.c), same commit.  Copyright (c) 2023-2025, Arm Limited.
3. Arm Limited, optimized-routines, [`math/exp_data.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/exp_data.c), same commit: the table, `exp2`'s shift and polynomial with its stated errors, and `exp10`'s constants and polynomial.
4. Arm Limited, optimized-routines, [`math/math_err.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/math_err.c) and [`math/math_config.h`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/math_config.h), same commit.
5. Arm Limited, optimized-routines, [`LICENSE`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/LICENSE), same commit.
6. P. T. P. Tang, "Table-driven implementation of the exponential function in IEEE floating-point arithmetic", *ACM Transactions on Mathematical Software* 15(2):144–157, June 1989, [doi:10.1145/63522.214389](https://doi.org/10.1145/63522.214389).  Crossref's record gives these bibliographic data.  The paper's text is not checked here, and the description above follows reference 7, which cites it.
7. J. Harrison, T. Kubaska, S. Story, and P. T. P. Tang, ["The Computation of Transcendental Functions on the IA-64 Architecture"](https://www.cl.cam.ac.uk/~jrh13/papers/itj.pdf), *Intel Technology Journal*, Q4 1999.  Its introduction describes the reduction `x = N ln 2/2^K + r`, the table of `2^(d/32)`, and the reconstruction of the table-driven framework, citing reference 6.
8. W. J. Cody, Jr. and W. Waite, *Software Manual for the Elementary Functions*, Prentice-Hall, 1980.  The book's text is not checked here.  H. C. Thacher, Jr.'s review in *SIAM Review* 24(1):91–93, 1982, [doi:10.1137/1024023](https://doi.org/10.1137/1024023), identifies the book, and reference 9 describes the method.
9. S. Boldo, M. Daumas, and R.-C. Li, "Formally Verified Argument Reduction with a Fused Multiply-Add", *IEEE Transactions on Computers* 58(8):1139–1145, 2009, [doi:10.1109/TC.2008.216](https://doi.org/10.1109/TC.2008.216); preprint [arXiv:0708.3722](https://arxiv.org/abs/0708.3722).  The paper describes Cody and Waite's reduction, a constant `C1` whose product with the integer is exact and a second constant `C2` holding the next bits.
10. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229).  This document cites clauses 4.3.1, 9.2, and 9.2.1.
11. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.3.2, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
12. ISO/IEC 9899:2024, *Information technology — Programming languages — C*, clause 7.12.6.2 and Annex F clause F.10.3.2, in WG14 working draft [N3220](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3220.pdf) (February 2024).
13. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
14. The Mathlib Community, Mathlib at commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`, [`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean), `Real.rpow_def_of_pos`.
15. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
