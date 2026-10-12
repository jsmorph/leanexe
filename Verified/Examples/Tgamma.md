# The gamma function

[The implementation](Tgamma.lean) exports `tgamma`, a port of CORE-MATH's correctly rounded `cr_tgamma` [1, 2] that calls [the software fused multiply-add](Fma.lean) wherever the C code calls `__builtin_fma`.  The decided bound is one representable step, `F64SignedRounding.WithinSteps 1`, from the nearest-even rounding of `Γ`, which is weaker than the correct rounding that CORE-MATH claims for its code.  `tests/verified/run.sh` checks the port natively against an integer reference at 74,373 arguments, and every result equals the reference.  `transcendentals` contains no theorem about `tgamma`, and no branch holds one.  The module's `verified_compile` call is commented out until the compiler change that [the plan's section "Resuming the work"](../../transcendentals.md#resuming-the-work) describes, the theorem of the fused multiply-add is assigned to track `expm1` and not started, and branch `w/erf` holds, not yet merged, the accepted mathematical foundations of the proof at commit `0efc1d87`: identities of `Γ`, the overflow and underflow thresholds, Stirling's series with a proved remainder, and kernel-checked Taylor models of `Γ` and `lgamma`.  The branch also holds bounds on three of CORE-MATH's polynomials, the fast path's below `1/4` and on `[3, 4]` and the accurate path's below `1/4`, in the forms that the floating-point proof takes as hypotheses.  The bounds on the other polynomials and tables are open.

## Specification

`tgamma` computes `Γ` of the value of its argument.  [Mathlib's `Real.Gamma`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean) is Euler's integral (DLMF 5.2.1) [4] for positive arguments, extended to the other reals by the recurrence `Γ (s + 1) = s Γ (s)`, and it takes the value 0 at zero and the negative integers by convention (`Real.Gamma_neg_nat_eq_zero`) [5].  The poles are therefore outside the domain of the accuracy statement, and their results are exceptional values.  The domain of the bound is every finite double other than zero and the negative integers.

The decided statement for such an `x` is `F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits)) (Tgamma.tgamma x).toBits`, with `WithinSteps` from [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean) as for the other functions: the word is not a NaN, and its position on the ordered line of doubles lies within one step of the position of the signed nearest-even reference.  The reference is `±∞` beyond the overflow threshold `2^1024 - 2^970` of IEEE 754-2019 clause 4.3.1 [6], which `Γ` crosses at about 171.62, and `±0` at or below half the smallest subnormal, which holds for every non-integer `x ≤ -184`.  The bound is the decision of 2026-10-10 recorded in [the journal](../../devnotes.md#2026-10-10-decisions-after-the-review-of-gamma-bessel-and-worst-inputs) and in [the plan](../../transcendentals.md#decisions), and the review of the same day recommended the special values in the table.

| Input | Result of the port | Source of the rule |
|---|---|---|
| `+0`, `-0` | `+∞`, `-∞` | C99 F.9.5.4 [7]; POSIX [8] |
| a negative integer | the canonical NaN | C99 F.9.5.4; POSIX on IEC 60559 systems |
| `-∞` | the canonical NaN | C99 F.9.5.4; POSIX |
| `+∞` | `+∞` | C99 F.9.5.4; POSIX |
| NaN | the canonical NaN | C99 F.9 paragraph 11; the deterministic profile of WebAssembly [9] |
| `x ≥ 0x1.573fae561f648p+7` | `+∞`, as `0x1.fp1023 + 0x1.fp1023` | overflow, POSIX |
| non-integer `x ≤ -184` | `±0` with the sign of `Γ x`, as `2^-1022 · (±2^-1022)` | underflow, POSIX |
| `x = 2^-1024` | `+∞`, as `0x1.fffffffffffffp+1023 + 0x1p+970` | overflow: `Γ x` exceeds the threshold |

IEEE 754-2019 lists no gamma function among its recommended operations [6], so C99's Annex F and POSIX fix the special values.  The port's NaN results are the canonical NaN, as every NaN result of the dialect is.  CORE-MATH sets `errno` when built with `CORE_MATH_SUPPORT_ERRNO` and raises the floating-point exceptions of these paths, and the port does neither.

## Algorithm

CORE-MATH's method evaluates `Γ` in double-double arithmetic, a pair `h + l` of doubles, with an explicit error bound `eps` for each path.  The project's paper describes the method: a fast path computes an approximation `y` with an error bound `ε`, a rounding test checks whether `[y - ε, y + ε]` crosses a rounding boundary, and otherwise an accurate path returns the correctly rounded value [3].  In `cr_tgamma`, when `h + (l + eps)` and `h + (l - eps)` round to the same double, the fast path returns that double, and otherwise `as_tgamma_accurate` evaluates `Γ` to about 100 bits, with a table of 57 hard cases for the inputs whose rounding test that path fails.  The structure below comes from the source [1].

| Range | Fast path |
|---|---|
| `\|x\| < 2^-112` | `1/x`, the leading term of `Γ x = 1/x - γ + ⋯`, and the correction for an exact `1/x` changes only the inexact flag and the directed roundings |
| `2^-112 ≤ \|x\| < 1/4` | `1/x` plus a polynomial of degree 20 in `x`, whose constant term is `-γ` |
| `-3 ≤ x ≤ 4`, not an integer | a polynomial of degree 17 in `d = x - (i + 3.5)` that approximates `Γ` on `[3, 4]`, divided by the product `x (x + 1) ⋯ (x + m - 1)` of the shifts that carry `x` there, the recurrence of DLMF 5.5.1 [4] |
| positive integers | `(x - 1)!` as a product in double-double, rounded once |
| `4 < x < 0x1.573fae561f648p+7` | `exp (lgamma x)`, with `lgamma` from Stirling's series (DLMF 5.11.1) by `as_lgamma_asym` and the exponential by `as_expd`, both in double-double |
| `-184 < x < -3`, not an integer | the reflection `Γ x = π/(sin (π x) Γ (1 - x))` (DLMF 5.5.3), with `Γ (1 - x)` from Stirling's series and `sin (π x)` from `as_sinpid`.  Below -170 the code tests whether the result is subnormal and then rounds it at the subnormal position. |

The accurate path `as_tgamma_accurate` uses polynomials in triple or double-double arithmetic, a series of 28 double-double terms below `1/4` and polynomials on nine ranges above it, and rounds once.  The fast path's error bounds, such as `1e-21` relative on `[-3, 4]` and `2e-21 + 1.84e-22 x` relative above 4, are constants of the source, and no Lean proof establishes them.  The decided one-step bound needs a proof that every path's error stays below one and a half spacings of the result, at least `1.5 · 2^-53 ≈ 1.7e-16` relative, about five orders of magnitude weaker than the bound `1e-21` that the rounding test on `[-3, 4]` assumes.

## Implementation

The source is `src/binary64/tgamma/tgamma.c` of CORE-MATH at commit `ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8` [1], `Copyright (c) 2024 Alexei Sibidanov`, under the MIT license [2].  The module docstring of [the implementation](Tgamma.lean) gives the copyright line and names the MIT license, and it omits the license's permission notice, which the license requires in all copies or substantial portions.  The port follows the C code operation for operation in the Verified dialect, the subset of Lean that [the Verified compiler](../README.md) translates to WebAssembly.  The commented `verified_compile` call lists 40 functions: the 14 of `Fma` and 26 of this module, among them the double-double operations `fastTwoSum`, `twoSum`, `fastSum`, `sumDD`, `mulDD`, `mulDD3`, `mulDDD`, and `polyDDD`, the helpers `asLogd`, `asExpd`, `asSinpid`, and `asLgammaAsym` for the logarithm, the exponential, `sin (π x)`, and Stirling's series, `database`, `accurate`, `tgammaWith`, and `tgamma`.

| C code | Port | Reason |
|---|---|---|
| a second result through a pointer | a pair result | The dialect has no pointers. |
| global `static const` tables | eight `Array UInt64` tables passed by `tgamma` to `tgammaWith` | The tables become borrowed arrays of the module. |
| integers `i`, `jm`, `ip`, `k` that count or select | integer-valued doubles | The dialect's words are unsigned 64-bit integers. |
| `int` exponents `e`, `eoff` and the index of `as_expd` | two's complement words, with `sar` for the arithmetic shift | The same reason. |
| `__builtin_fma` | `Fma.fma`, at all 15 calls | WebAssembly has no scalar fused multiply-add, and in the deterministic profile its relaxed SIMD multiply-add returns the unfused result [9]. |
| `roundeven_finite`, `floor` | adding and subtracting `2^52`, and `floorF` from it | The dialect has no operation that rounds to an integer. |
| the binary search of `as_tgamma_database` | a scan of all 57 rows | The scan finds the same row. |
| `errno`, `raise_underflow`, `feraiseexcept` | omitted, with the expressions evaluated for their flags kept | WebAssembly has no floating-point status flags. |
| `verified_compile` | commented out | With it, the build exceeds the runner's memory limit, as the Proof section describes. |

The eight tables hold 1,551 words: `dbTable` (the 57 hard cases as rows `x`, `f`, `δ`), `accurateTable` (718 words of the accurate path), `smallTable`, `mainTable`, `logdTable` (`as_logd`'s `B`, `r1`, `r2`, `l1`, and `l2`), `sinpidTable`, `expdTable`, and `asymTable`.  Each word carries the C literal in a comment.  A comparison of the port with `tgamma.c` at the pinned commit, run outside the repository, gives the results in the table.

| Check | Result |
|---|---|
| Floating-point literals of the C file | All 1,562 occurrences occur in the port as words or decimal literals, some with the opposite sign where the port writes a negation differently. |
| `double` arrays | 38 of the 39 occur in order as contiguous runs of the port's tables, and the port writes the two-element `sgn` inline. |
| `as_logd`'s integer pairs `B` | The 32 pairs equal the first 64 words of `logdTable`. |
| Comments | All 1,506 words with a hexadecimal literal in their comment equal the bits of that literal. |

No run compared the port with compiled CORE-MATH directly.  The journal records that the reference's Python model agreed with compiled CORE-MATH at 3,500 arguments.  The accuracy check below finds the port equal to the reference at every one of its arguments.

## Theorems

`transcendentals` contains no theorem about `Tgamma.tgamma`, and there is no axiom report to give.  The Lean module defines no `compiled` WebAssembly module, so there is no byte theorem and no file theorem, and `tests/verified/run.sh` writes no `tgamma.wasm` and runs [the accuracy check](TgammaAccuracy.lean) natively.  The intended results follow the other functions: `WithinSteps 1` against `Real.Gamma` on the domain above, exact words for the exceptional values in the table, a byte theorem of the form of `ExpTheorem.exp_bytes_accuracy` with the eight tables borrowed, and a file theorem.  [The software fused multiply-add](Fma.lean) compiles and is checked natively, and no theorem yet states that it returns the nearest-even rounding of `a · b + c`, a result that every path of the port depends on.  Branch `w/erf` holds accepted mathematical facts toward the accuracy theorem, from commit `0efc1d87` on, which the Proof section lists.

## Proof

No proof module for `tgamma` itself exists in `transcendentals` or on a branch, and the proof has four parts.  The first is a theorem for `Fma.fma`, which the review of 2026-10-10 proposed to prove once with ProofKit's rounding of scaled rationals ([the review](../../devnotes.md#2026-10-10-review-of-the-options-for-stages-7-and-8)), and which the plan assigns to track `expm1`.  The second is the set of mathematical facts that the algorithm uses and Mathlib lacks: Mathlib has `Real.Gamma` with the recurrence `Real.Gamma_add_one` and Euler's reflection formula `Real.Gamma_mul_Gamma_one_sub` [5] and no Stirling series with a remainder for `log Γ` at real arguments, so the proof needs a remainder bound, such as those of DLMF 5.11(ii) [4].  The decision of 2026-10-12 is to prove these facts only to the precision that a one-step bound needs ([the integration notes](../../devnotes.md#2026-10-12-integration-of-expm1-tanh-erf-log1p-atan-atan2-asin-and-acos-first-push)), and track `erf` proved the foundations in six ProofKit modules on branch `w/erf` at commit `0efc1d87`, in `/home/somebody/src/lt-erf` on debtop1, not yet merged.  The third is an error analysis of each fast path, the accurate path, and the 57 hard cases against one and a half spacings of the result, with the subnormal results below -170 and the overflow and underflow boundaries.  The fourth is the byte and file theorems, once `verified_compile` runs.

The six modules are `GammaBasic`, `GammaStirling`, `RatExpLog`, `GammaThresholds`, `TaylorModel`, and `GammaModels` in `LeanExe/ProofKit`.  Their 42 axiom reports list only `propext`, `Classical.choice`, and `Quot.sound` (`erf-gamma-12.log` in `build/transcendentals` on debtop1), and [the journal](../../devnotes.md#2026-10-11-foundations-for-core-maths-tgamma-and-lgamma-track-erf-debtop1) lists the facts with the C source lines that use them.  The table gives the results that `tgamma`'s proof uses.

| Theorem | Module | Statement |
|---|---|---|
| `gamma_add_nat`, `gamma_eq_div` | `GammaBasic` | `Γ (x + n) = Γ x · x (x + 1) ⋯ (x + n - 1)` for `x` other than 0 and the negative integers, the shifts of the paths on `[-3, 4]` and of the accurate path |
| `gamma_nat_prod` | `GammaBasic` | `Γ (k + 1) = 1 · 2 ⋯ k`, the path for positive integers |
| `gamma_reflect` | `GammaBasic` | `Γ x = π / (sin (π x) Γ (1 - x))` for non-integer `x`, the path below -3 |
| `gamma_pos_of_even`, `gamma_neg_of_odd` | `GammaBasic` | the sign of `Γ x` is `(-1) ^ ⌊x⌋` for non-integer `x < 1` |
| `gamma_underflow` | `GammaBasic` | `\|Γ x\| < 2 ^ -1078` for `x ≤ -184` at distance at least `2 ^ -45` from the integers, which holds for every non-integer double below -128 |
| `gamma_sub_inv_bounds` | `GammaBasic` | `-8/5 ≤ Γ x - 1/x ≤ 0` for nonzero `x` in `[-1/2, 1]`, so `1/x` is within a relative `2 ^ -111` of `Γ x` for `\|x\| < 2 ^ -112` |
| `gamma_overflow` | `GammaThresholds` | `Γ x ≥ 2 ^ 1024` from `0x1.573fae561f648p+7` on, with `t0_word` identifying the threshold's word |
| `stirling_twelve` | `GammaStirling` | `\|ln Γ x - ((x - 1/2) ln x - x + ln (2π)/2) - Σ B (2 k)/(2 k (2 k - 1) x ^ (2 k - 1))\| ≤ 104001 / (25 (x - 1) ^ 25)` for `x ≥ 16`, with twelve terms, below `2 ^ -85` at 16 |
| `gamma_model`, `gammaPieceOk_sound` | `GammaModels` | a Taylor model that `TaylorModel.tm` computes for Stirling's series after `n` shifts bounds `Γ (a + t)` on `[-r, r]`, and a kernel check of a polynomial against it bounds `\|Γ (a + t) - P (t)\|` |

Stirling's remainder comes from Mathlib's limit `Real.BohrMollerup.tendsto_log_gamma` and Stirling's formula for `n!`: the remainder `R` satisfies `R y - R (y + 1) = ρ y` with an elementary `ρ`, the kernel bounds `ρ` by a polynomial certificate in `1/y`, and the bound telescopes.  Each fact about a CORE-MATH polynomial then becomes a kernel check of Taylor models on pieces of its interval.  The one-step bound needs about `2 ^ -60` relative error per approximation, so each fact is proved to that precision, which is weaker than the `1e-21` of CORE-MATH's rounding test.

The floating-point proof, assigned to track `arc`, takes eight approximation statements as hypotheses, which `Verified/Examples/TgammaApprox.lean` defines on branch `w/poly` at commit `02c72fa9` (`SmallFact`, `MainFact`, `AccSmallFact`, `AccRangeFact`, `StirlingFact`, `LogFact`, `ExpFact`, and `SinFact`).  Track `erf` proves them on branch `w/erf`.  `TgammaFactsBase` reads the coefficient lists from the port's tables with the same definitions as `TgammaApprox`, so each theorem below has the type of the corresponding statement up to unfolding.  The models use Mathlib's 20-digit bounds on `π` where `π` enters only through `ln (2π)/2`, and `GammaPi` gives `π` within `2 ^ -128` from `TrigPi` for the kernels and tables of the sine.  The table gives the accepted results, whose axiom reports list only `propext`, `Classical.choice`, and `Quot.sound` (`erf-gamma-14.log`, `erf-gamma-17.log`, and `erf-gamma-19.log` in `build/transcendentals` on debtop1).

| Theorem | Module | Statement |
|---|---|---|
| `gamma_small_fast` | `TgammaPolySmall` | `\|Γ (1 + x) - (1 + x P (x))\| ≤ 2 ^ -60` for `\|x\| ≤ 1/4`, with `P` the five double-double and 16 double coefficients of the fast path below `1/4`: `SmallFact` |
| `gamma_sub_inv_fast` | `TgammaPolySmall` | `\|Γ x - (1/x + P (x))\| ≤ 5/3 · 2 ^ -60 \|Γ x\|` for `0 < \|x\| ≤ 1/4` |
| `gamma_main` | `TgammaPolyMain` | `\|Γ (7/2 + d) - P (d)\| ≤ 2 ^ -62` for `\|d\| ≤ 1/2`, with `P` the ten double-double and eight double coefficients of the path on `[-3, 4]`: `MainFact` |
| `gamma_main_ge` | `TgammaPolyMain` | `Γ (7/2 + d) ≥ 2` for `\|d\| ≤ 1/2` |
| `gamma_small_acc`, `gamma_sub_inv_acc` | `TgammaPolySmallAcc` | the same forms with `2 ^ -62` for the accurate path's 28 double-double and eight double coefficients below `1/4`: `AccSmallFact` |
| `fit_piece`, `fit_large` | `GammaFits` | a kernel check bounds `\|lgamma x - F (x)\|` for a Stirling fit `F (x) = (x - 1/2) (ln x - 1) + C0 + P (1/x²)/x` on a piece, and from 16 on by comparison with Stirling's series |
| `pi_bounds128` | `GammaPi` | `π` lies in an interval of width `2 ^ -128` |
| `exprOk_sound` | `TaylorCheck` | a kernel check of the Taylor model of an expression `E` gives `\|E (t)\| ≤ ε` on `[-r, r]` |

The other five statements are in progress on debtop1: the Stirling fits (`TgammaAsymFit`, `TgammaAsymFitB`, `TgammaAsymFitC`), the nine ranges of the accurate path (`TgammaAccRangeA` to `TgammaAccRangeC`), and the kernels and tables of `as_logd`, `as_expd`, and `as_sinpid` (`TgammaKernels`).  Track `arc`'s journal on branch `w/poly` (commit `3521ad41`) records that the 57 hard cases need no separate statement, since `AccRangeFact` and an exact evaluation at those arguments bound `Γ` there.

The compilation failure sets the order of the work.  With its `verified_compile` call, the module's build ran 25 minutes of CPU time at the runner's limits of 4.2 GB of memory and 1 GB of swap before `tools/leanrun` stopped it.  Probes that chain `let (h, l) := mulDD …` bindings showed the objects of the generated program growing from 5,093 at 10 bindings to 15,413 at 20, while the distinct subterms grew from 491 to 851, and a probe of 40 bindings exhausted the memory ([the journal](../../devnotes.md#2026-10-11-a-software-fused-multiply-add-core-maths-gamma-functions-and-fdlibms-bessel-functions)).  `Ctx.ctx` in `Verified/Reflect/Command.lean` rebuilds the expression of the whole context at each of its 23 uses, and a first change that shares it, uncommitted in `/home/somebody/src/lt-reflect` on debtop1, made the program term linear, while the kernel's checking still grows faster than linearly.  The plan records the measured cause: the kernel's evaluation of the code generator in the `decide +kernel` proof that `encode p.module` succeeds, where `Expr.code` in `Verified/Compile.lean` keeps the live variables as a chain of closures, at least cubic in the nesting depth of lets.  The decided change computes liveness as data, and the ported functions are not to be split ([the plan](../../transcendentals.md#decisions-taken-and-not-yet-acted-on)).

## Tests

[The accuracy check](TgammaAccuracy.lean) compares `Tgamma.tgamma` natively with the double nearest to `Γ x` from [the gamma reference](GammaReference.lean), and it fails at the first result more than one step away.  Its 74,373 arguments are 30,001 evenly spaced values from -185 to 172 and 20,001 from -4 to 5, 20,000 hashed values over the exponents from `2^-1074` to `2^7` with both signs, the integers from -200 to 172, the five doubles at and around each integer from -190 to 172 and each half-integer from -189.5 to 172.5, the doubles around the thresholds `2^-112`, `1/4`, 3, 4, `0x1.573fae561f648p+7`, and -184 and their negations, the 57 hard cases and their neighbors, the ten inputs of `WorstCases.tgamma`, and 13 special values.  The ten worst-case inputs give the largest known `tgamma` errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [10], whose Table 3 lists 0.500 units for GNU libc 2.44 and 1.03e3 for FreeBSD 15.1.  The fast paths rarely reach the accurate path, so the check also calls `Tgamma.accurate` directly at every eighth argument from -184 to 171 above `2^-112` in magnitude, other than the integers, and at the 57 hard cases, 7,002 arguments.

The reference computes `lgamma y` for `y > 0` as `lgamma (y + N) - ln (y (y + 1) ⋯ (y + N - 1))` with `y + N ≥ 300`, Stirling's series with 60 terms and a remainder below `2^-650`, and one logarithm of the exact product, and for `x < 0` the reflection with `Reference.sinCosTurns`.  `Γ` is the exponential of `lgamma` with the sign of `sin (π x)`.  The Bernoulli numbers come in exact fractions from the algorithm that the module attributes to Akiyama and Tanigawa, and a Python model of the reference at 600 bits gave the same doubles as compiled CORE-MATH at 3,500 arguments.  The truncation errors are stated in docstrings and are not proved.

In `opus-verified-tests-14.log`, the run of `tests/verified/run.sh` in `build/transcendentals` on minideb1 after the `sinh` merge, all 74,373 results equal the reference, so the largest measured distance is 0 steps against the decided bound of 1, and the 7,002 results of the accurate path also equal the reference.  The first run, `ports-TgammaAccuracy-1.log` in `/home/somebody/src/lt-ports/build/transcendentals` on minideb2, gave the same results.  The runs use the module built without its `verified_compile` call, so they test the Lean function that the compiler will translate, and no compiled WebAssembly.

## Limits

Every result for `tgamma` is a test of the Lean function, and the decided theorems are open.  Until the compiler change is merged and `verified_compile` runs, no WebAssembly module exists.  After that, the limits of the compiled functions apply as for [the exponential](Exp.md#limits): Talos and the decoder are trusted, the file theorem trusts `binary_file%`, the theorems cover the canonical NaN argument only, and host actions between calls need their own theorem.  The port depends on `Fma.fma` at every path, and that function has only a native check, `FmaAccuracy.lean`, which found 763,816 operand triples equal to the exact value rounded to nearest and which `tests/verified/run.sh` does not run.

The decided bound allows one step where CORE-MATH's code is designed to be correctly rounded, so a proof of the bound will not establish CORE-MATH's claim.  A theorem of correct rounding would need CORE-MATH's search for hard cases as a verified input, which the review did not recommend.  The port drops `errno` and the floating-point exceptions, which C99 and POSIX specify for the poles, the overflow, and the underflow.

## References

1. CORE-MATH, [`src/binary64/tgamma/tgamma.c`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/src/binary64/tgamma/tgamma.c), commit `ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8`.  Copyright (c) 2024 Alexei Sibidanov, MIT license.
2. CORE-MATH, [`LICENSE`](https://gitlab.inria.fr/core-math/core-math/-/blob/ff2f71f635e95d395a6646b7e7b2c72e7b03a5d8/LICENSE), same commit.
3. A. Sibidanov, P. Zimmermann, and S. Glondu, "The CORE-MATH Project", *2022 IEEE 29th Symposium on Computer Arithmetic (ARITH)*, pp. 26–34, 2022, [doi:10.1109/ARITH54963.2022.00014](https://doi.org/10.1109/ARITH54963.2022.00014).  Crossref confirms the bibliographic data, and the text was read in [HAL hal-03721525v3](https://inria.hal.science/hal-03721525): the abstract states the project's aim of open-source correctly rounded functions, and Section I.B describes the fast path, the rounding test, and the accurate path.
4. F. W. J. Olver, A. B. Olde Daalhuis, D. W. Lozier, B. I. Schneider, R. F. Boisvert, C. W. Clark, B. R. Miller, B. V. Saunders, H. S. Cohl, and M. A. McClain, eds., *NIST Digital Library of Mathematical Functions*, Release 1.2.8 of 2026-09-15: [§5.2](https://dlmf.nist.gov/5.2) (5.2.1, Euler's integral), [§5.5](https://dlmf.nist.gov/5.5) (5.5.1, the recurrence, and 5.5.3, the reflection), and [§5.11](https://dlmf.nist.gov/5.11) (5.11.1, Stirling's series, and 5.11(ii), its error bounds for real positive arguments).
5. The Mathlib Community, Mathlib at commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`: [`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean) (`Real.Gamma`, `Real.Gamma_add_one`, `Real.Gamma_neg_nat_eq_zero`) and [`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean) (`Real.Gamma_mul_Gamma_one_sub`).
6. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clause 4.3.1 (the overflow threshold) and clause 9.2 (the recommended operations, which include no gamma function).
7. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.5.4, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
8. The Open Group, *The Open Group Base Specifications Issue 8*, IEEE Std 1003.1-2024, [`tgamma`](https://pubs.opengroup.org/onlinepubs/9799919799/functions/tgamma.html).
9. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0: appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html), in whose deterministic profile "All NaN values generated by floating-point instructions are canonical and positive", and [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html), where for the relaxed multiply-add "In the deterministic profile, the unfused behaviour is used."
10. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 and Tables 4 to 11.
