# The function log1p

[The implementation](Log1p.lean) exports `log1p`, which computes `log (1 + x)`, a port of fdlibm's `s_log1p.c` as FreeBSD's msun has it [1, 2].  The decided bound is one representable step from the nearest-even rounding of `log (1 + x)`, which [the ports track](../../devnotes.md#2026-10-10-ports-of-log1p-atan-atan2-asin-acos-and-tan) recommended and [the review of the worst inputs](../../devnotes.md#2026-10-10-decisions-after-the-review-of-gamma-bessel-and-worst-inputs) left unchanged.  The bound is proved for every finite `x > -1`, the exceptional values are proved as words, and `Log1pBytes.log1p_bytes_accuracy` carries both to the decoded WebAssembly module, with `Log1pFile.log1p_file` connecting that module to `build/verified/log1p.wasm`.  Every accepted theorem reports only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`log1p` computes `Real.log (1 + a)` for the value `a` of its argument.  The domain is every finite double above -1, together with -1 itself, `+∞`, and the signed zeros, which have exact results.  The bound is `F64SignedRounding.WithinSteps 1 (Real.log (1 + a)) w` for the result word `w`, with `WithinSteps` from [the signed rounding reference](../../LeanExe/ProofKit/F64SignedRounding.lean): `w` is not a NaN, and its position on the ordered line of doubles, with both zeros at 0, lies within one of the position of the nearest-even rounding of `log (1 + a)`.  The result is never near overflow, since `log (1 + a) < 710` for every double.

| Input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `+0`, `-0` | `+0`, `-0` | IEEE 754-2019 9.2.1 (`logp1 (±0) = ±0`) [5]; C99 F.9.3.9 [6] | `log1p_zero`, `log1p_neg_zero` |
| `-1` | `-∞` | IEEE 754-2019 9.2.1 (divideByZero); C99 F.9.3.9 | `log1p_neg_one` |
| `+∞` | `+∞` | IEEE 754-2019 9.2.1; C99 F.9.3.9 | `log1p_pos_inf` |
| finite `x < -1` | the canonical NaN | IEEE 754-2019 Table 9.1 (domain `[-1, +∞]`, invalid below); C99 F.9.3.9 | `log1p_below` |
| `-∞` | the canonical NaN | C99 F.9.3.9 (`x < -1`) | `log1p_neg_inf` |
| NaN | the canonical NaN `0x7FF8000000000000` | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [7] | `log1p_nan` |

IEEE 754-2019 names this operation `logp1` and recommends it in clause 9.2, where a conforming implementation rounds correctly [5].  fdlibm states that "the error is always less than 1 ulp" [1].  An error below one unit implies the one-step bound, but one step allows errors up to one and a half units, so the theorem proves a weaker statement than fdlibm's.  The theorems say nothing about floating-point exceptions, which the port does not compute.

## Algorithm

The reduction writes `1 + x = 2^k (1 + f)` with `√2/2 < 1 + f < √2`.  When `k = 0`, `f = x` with no rounding.  When `k ≠ 0`, the code forms `u = 1 + x` rounded, normalizes `u` by replacing its exponent field, and carries the rounding error of `u` as the correction `c/u`, with `c = 1 - (u - x)` for `k > 0` and `c = x - (u - 1)` for `k < 0`, since `log (1 + x) - log u ≈ c/u`.  From `2^53` on, `u = x` and the correction is 0.  The result is `k ln 2 + log (1 + f)`, with `ln 2` split as `ln2_hi + ln2_lo`, where `ln2_hi` has 32 significant bits so that `k · ln2_hi` is exact for every `k` that occurs.

The approximation uses `s = f/(2 + f)`, for which `log (1 + f) = log (1 + s) - log (1 - s) = 2s + 2s³/3 + 2s⁵/5 + ⋯`, the series of DLMF 4.6.4 [4] with `z = 1 + f`.  fdlibm writes `log (1 + f) = 2s + s R(s²)` and approximates `R` on `|s| ≤ 0.1716` by a polynomial of degree 7 in `z = s²` with coefficients `Lp1` to `Lp7`, whose error it bounds by `2^-58.45` [1].  Since `2s = f - s f = f - f²/2 + s f²/2`, the code evaluates `log (1 + f)` as `f - (f²/2 - s (f²/2 + R))`, so that the leading term `f` is added last, without rounding.

Three paths shorten the work.  Below `2^-54` in magnitude the result is `x`, and below `2^-29` it is `x - x²/2`.  When the code's word `hu` is zero, which happens for `1 + f` within `3 · 2^-21` of 1, the code replaces `R` by the cubic term, using `log (1 + f) ≈ f - f²/2 (1 - 2f/3)`.  When `f = 0` the result is `k ln2_hi + (c + k ln2_lo)`.

## Implementation

The source is `lib/msun/src/s_log1p.c` of FreeBSD at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1], `Copyright (C) 1993 by Sun Microsystems, Inc.`, with the notice "Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved", which the module docstring of [the implementation](Log1p.lean) cites.  fdlibm is Sun's "Freely Distributable LIBM" [3].  The port follows the dialect of the Verified compiler as [the exponential document](Exp.md#implementation) describes: `verified_compile compiled := [log1pTail, log1p]` generates a module whose functions are `alloc` (0), `release` (1), `log1pTail` (2), and `log1p` (3), every constant is `Float.ofBits` of its bit pattern, and the module reads no table.

| C code | Port | Reason |
|---|---|---|
| The end of the function after the reduction | `log1pTail f c k hu` | One function serves both the `k = 0` path and the normalized paths. |
| Signed `int32_t` high words `hx`, `hu` | `UInt64` words, with the sign bit tested apart | A signed comparison with a positive bound becomes a sign test and an unsigned comparison: `hx < 0x3FDA827A` is `neg ∨ hx < 0x3FDA827A`. |
| Signed `k`, converted with `(double) k` | a two's complement word, converted as `Log.logCore` converts its `k` | The dialect has no signed integers. |
| `-two54/vzero` | `-two54 / 0.0` | The volatile zero serves only to raise divideByZero, and the value is `-∞` either way. |
| `two54 + x > zero` | kept as a test | It serves only to raise inexact, and it holds for every `\|x\| < 2^-29`, so it changes no result. |
| `c` unset on the `k = 0` path | `c = 0.0` | C never reads `c` there. |
| `0.66666666666666666` | `0x3FE5555555555555`, the nearest double | The literal has no bit pattern in the source. |
| `STRICT_ASSIGN (double, u, 1.0 + x)` | `1.0 + x` | `STRICT_ASSIGN` is a plain assignment for `double`. |

| Constant | Bits | Constant | Bits |
|---|---|---|---|
| `ln2_hi` | `0x3FE62E42FEE00000` | `Lp3` | `0x3FD2492494229359` |
| `ln2_lo` | `0x3DEA39EF35793C76` | `Lp4` | `0x3FCC71C51D8E78AF` |
| `two54` | `0x4350000000000000` | `Lp5` | `0x3FC7466496CB03DE` |
| `Lp1` | `0x3FE5555555555593` | `Lp6` | `0x3FC39A09D078C69F` |
| `Lp2` | `0x3FD999999997FA04` | `Lp7` | `0x3FC2F112DF3E5244` |

The ports track converted each decimal constant of the source to binary64 and compared it with the bits that the source prints beside it, and found all to agree ([its journal section](../../devnotes.md#2026-10-10-ports-of-log1p-atan-atan2-asin-acos-and-tan)).  For this document a script repeated the comparison against the pinned `s_log1p.c` and the port's `Float.ofBits` words: all ten constants agree, and `0x3FE5555555555555` is the nearest double to `0.66666666666666666`.  The proofs restate the polynomial's coefficients as `PolyBound.ratOfWord` of the same words, so the kernel-checked bounds apply to the port's constants.

## Theorems

The theorems are in [the accuracy theorem](Log1pTheorem.lean), [the exceptional values](Log1pTheoremSpecial.lean), [the byte theorem](Log1pBytes.lean), and [the file theorem](Log1pFile.lean).  `x` is a Lean `Float` and `a = value x.toBits` its real value.  The byte theorem uses `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `Log1pTheorem.log1p_within_one` | For finite `x` with `-1 < a`, `WithinSteps 1 (Real.log (1 + a)) (Log1p.log1p x).toBits`. |
| `Log1pTheoremSpecial.log1p_zero`, `log1p_neg_zero` | `±0` give the words `0` and `0x8000000000000000`. |
| `log1p_neg_one` | `-1` gives `0xFFF0000000000000`. |
| `log1p_pos_inf` | `+∞` gives `0x7FF0000000000000`. |
| `log1p_below`, `log1p_neg_inf`, `log1p_nan` | A finite `x < -1`, `-∞`, and every NaN give `Wasm.IEEE64.canonicalNaN`. |
| `Log1pBytes.ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant and a memory cap of at most 65,535 pages. |
| `Log1pBytes.log1p_entry_call` | A call of function 3 from a `Ready` store returns, without a trap, the bits of `Log1p.log1p x`, and leaves a `Ready` store in which every heap region keeps its bytes. |
| `Log1pBytes.log1p_bytes_accuracy` | `Log1p.compiled.module` encodes to bytes that decode to it, exports function 3 as `log1p`, starts in a `Ready` store, and every call from a `Ready` store returns the bits of `Log1p.log1p x`, within one step of `log (1 + a)` for finite `x > -1`, and leaves a `Ready` store. |
| `Log1pFile.log1p_file`, `log1p_file_decode` | `build/verified/log1p.wasm` holds `encode Log1p.compiled.module` and decodes to the module of `log1p_bytes_accuracy`. |

The arc track accepted `log1p_within_one`, the exceptional values, and the byte theorem in `arc-mix-13.log` and `arc-mix-14.log`, and the file theorem in `arc-file-2.log`, all under `build/transcendentals/` of the worktree `lt-poly` on minideb2 ([the track's journal](../../devnotes.md#2026-10-10-full-theorems-for-atan-and-log1p-track-arc-minideb2)).  After the merge into `transcendentals`, `opus-merge-arc-1.log` on minideb1 built the theorems with the permitted axioms.  `tests/verified/run.sh` builds `Verified.Examples.Log1pBytes`, checks `Log1pFile.lean` against the `log1p.wasm` that it writes earlier in the same run, and fails unless both file theorems report exactly the three permitted axioms.  The latest run in the primary checkout, `opus-verified-tests-13.log` of 2026-10-11, passed that check and printed `[propext, Classical.choice, Quot.sound]` for `log1p_within_one`, every exceptional value, and `log1p_bytes_accuracy`.

## Proof

### Modules

The chain has 12 modules of its own, listed in dependency order below.  It reuses `LogCoreBits.kd_value` of [the logarithm's proof](LogCoreBits.lean) for the conversion of `k`, and `AtanTheoremConst` and `AtanTheoremReduce` of [the arctangent's proof](Atan.md), with the modules below them, for rational evaluation and word facts.  `tests/verified/run.sh` builds the chain through `Verified.Examples.Log1pBytes`.

| Module | Content |
|---|---|
| `Log1pTheoremBranches` | The branches of `log1p` and `log1pTail` as equations on the high words. |
| `Log1pKernelPoly` | The kernel bound `log1p_kernel_error`. |
| `Log1pTheoremCore` | Error chains for `f²/2` and `P = s (f²/2 + R)` at the scale `σ = \|f\|`, for four ranges of `f`, and `log_kernel`, the exact identity `f - (f²/2 - P*) = 2s + sR(s)`. |
| `Log1pTheoremConst` | `log (1 + q)` between rationals for rational `q`, and `ln2_hi + ln2_lo` within `2^-81` of `log 2`. |
| `Log1pTheoremK0` | The path `k = 0`: `k0_neg`, `k0_pos_low`, and `k0_pos_high`. |
| `Log1pTheoremTail` | `log1pTail` for `k ≠ 0` against `K log 2 + log (1 + f) + log (1 + t)`: `tail_main` and `tail_big`. |
| `Log1pTheoremReduce` | The normalization: `1 + f` is `u/2^K` exactly, `f` is exact by Sterbenz's lemma, and `kd · ln2_hi` is exact (`main_reduce`). |
| `Log1pTheoremCorr` | The correction `c/u` within `2^-60` of `t = (1 + x - u)/u`, with `\|t\| ≤ 2^-52`, in each range of `x` (`corr_low`, `corr_mid`, `corr_hi`, `corr_big`). |
| `Log1pTheorem` | The case split on the high word and `log1p_within_one`. |
| `Log1pTheoremSpecial`, `Log1pBytes`, `Log1pFile` | Exceptional values, the byte theorem, and the file theorem. |

### Kernel bound

`Log1pKernelPoly.log1p_kernel_error` states `|log (1 + s) - log (1 - s) - s (2 + Lp1 z + ⋯ + Lp7 z⁷)| ≤ |s| · (93/128) · 2^-58` for `|s| ≤ 0.1716` and `z = s²`, about `2^-58.46` relative to `s`.  The proof subtracts the kernel from the series' first 20 terms in `z` (`LogRatioRemainder.logRatioCoeffs 20`), whose remainder `LogRatioRemainder.log_ratio_remainder` bounds by `2 |s|^41/(1 - s²)`, below `(1/256) · 2^-58 |s|`, from Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one` [8].  The difference of the two polynomials is checked by `PolyBound.check` on `[0, 15439/2^19]`, which contains `0.1716²`, in eight adjacent pieces, `log1p_part_1` to `log1p_part_8`, each proved by `decide +kernel` and combined by `PolyChecks.bounded_of_covers`, with the bound `(185/256) · 2^-58`.  The checker shifts the rational coefficients to the center of an interval and accepts when the sum of their magnitudes times powers of the half-width is below the bound, bisecting otherwise, and `PolyBound.check_sound` turns acceptance into a bound for every real point.  Sampling found the largest error to be about `2^-58.47` at `s ≈ 0.168`, inside fdlibm's stated `2^-58.45` ([the polynomial track's journal](../../devnotes.md#2026-10-10-kernel-polynomials-of-stage-3-track-poly-minideb2)).

### Error budget

The proof finishes each path with one of three criteria, all in ProofKit.  `F64RoundNearest.within_one_of_rounded` and its relative form `within_one_of_rounded_rel` charge nothing for the last rounding: a rounded sum is a nearest word of its exact value, and nearest words of two numbers closer than one spacing are at most one step apart, so the exact value of the last sum may differ from `log (1 + x)` by up to one spacing, or by the fraction `1/(2^53 + 1)` of it.  `F64Approx.within_one_of_error` allows one and a half spacings for a result word whose exact distance is bounded.  The arc track added the first criterion because the second failed by a few percent near the binade boundary at `1/2`.

| Inputs | Path | Proved bound | Allowance | Theorem |
|---|---|---|---|---|
| `\|x\| < 2^-54` | `x` | `\|log (1 + x) - x\| ≤ 2x² ≤ 2^-53 \|x\|` | relative `2^-53` (`F64WithinSelf.within_one_of_self`) | `Log1pTheorem.tiny_within` |
| `2^-54 ≤ \|x\| < 2^-29` | `x - x²/2` | relative `2^-56` | relative `1/(2^53 + 1)` | `small_within` |
| `-0.2929 ≤ x ≤ -2^-30` | `k = 0` | relative `0.63 · 2^-53` | relative `1/(2^53 + 1)` | `Log1pTheoremK0.k0_neg` |
| `2^-30 ≤ x ≤ 0.285` | `k = 0` | relative `0.66 · 2^-53` | relative `1/(2^53 + 1)` | `k0_pos_low` |
| `0.285 ≤ x < 0.4142` | `k = 0` | `0.65 · 2^-54` in `[1/4, 1/2)` | one spacing, `2^-54` | `k0_pos_high` |
| `k ≠ 0`: `\|K\| ≥ 2`, `K = 1` with `f ≥ -0.175`, or `K = -1` with `f ≤ 0.2125` | general | `1.5 · 2^-54`, at or above `1/2` | one spacing of `[1/2, 1)`, `2 · 2^-54` | `Log1pTheoremTail.tail_main` |
| `K = 1`, `f < -0.175` | general | `0.95 · 2^-54`, at or above `1/4` | one spacing, `2^-54` | `tail_main` |
| `K = -1`, `0.2125 < f < 0.285` | general | `0.90 · 2^-54`, at or above `1/4` | one spacing, `2^-54` | `tail_main` |
| `K = -1`, `f ≥ 0.285` | general, last difference exact | `1.2 · 2^-54` | one and a half spacings, `1.5 · 2^-54` | `finish_d` |
| `k ≠ 0`, `hu = 0` or `f = 0` | cubic term or `k ln 2` | `1.5 · 2^-54`, at or above `1/2` | `2 · 2^-54` | `finish_q`, `finish_z` |
| `x ≥ 2^53` | `u = x`, `c = 0` | `6 · 2^-54`, above 32 | one spacing, `2^-47` | `tail_big` |

The constants of the third column are the bounds that the Lean statements carry.  The journal reports the largest errors that a Python model of the same formulas computed: 0.62 and 0.65 times `2^-53` for the relative `k = 0` cases, `0.64 · 2^-54` above 0.285, and 1.33, 0.93, 0.87, and 1.10 in units of `2^-54` for the four general cases ([the track's journal](../../devnotes.md#2026-10-10-full-theorems-for-atan-and-log1p-track-arc-minideb2)).  The smallest margins are those of `K = 1` with `f < -0.175`, 5 percent of the allowance in the Lean constant and 7 percent in the model, and of the relative `k = 0` cases, about 34 percent.

The general path for `k ≠ 0` computes `A - G` with the exact `A = kd · ln2_hi` and `G = (f²/2 - (P + (kd · ln2_lo + c))) - f`.  The exact value of `A - G` is `K (ln2_hi + ln2_lo) + t + 2s + sR(s)`, which differs from `K log 2 + log (1 + f) + log (1 + t)` by `|K| · 2^-81` from `Log1pTheoremConst.ln2_close`, the kernel's error, and `2t²` from `Log1pTheoremTail.log_near_t`.  The sums inside `G` round within half a spacing of their binades, `F64HalfUlp.add_half`, which halves the charge of the relative bound at the top of a binade.  `Log1pTheoremCorr` shows that the correction `c/u` is within `2^-60` of `t`, and exact for `x ≤ -1/2`, where `u = 1 + x` is exact.  The one input `x = 1 - 2^-53` defeats the correction: `1 + x` rounds to 2, `u - x` rounds to 1, and `c = 0` misses `t = -2^-54`, but there `f = 0` and the error `2^-54` is below one spacing of `[1/2, 1)` (`Log1pTheorem.special_two`).

### Shared modules

The analysis uses these ProofKit modules beyond the arithmetic chain: [error tracking for straight-line code](../../LeanExe/ProofKit/F64Approx.lean), [error tracking through rounded chains](../../LeanExe/ProofKit/F64ErrorTrack.lean), [half-spacing sums](../../LeanExe/ProofKit/F64HalfUlp.lean), [nearest rounding of sums](../../LeanExe/ProofKit/F64RoundNearest.lean), [functions that return their argument](../../LeanExe/ProofKit/F64WithinSelf.lean), [exact operations and Sterbenz's lemma](../../LeanExe/ProofKit/F64Exact.lean), [exact products](../../LeanExe/ProofKit/F64ExactProduct.lean), [fdlibm's high-word tests](../../LeanExe/ProofKit/F64UpperWord.lean), [the polynomial checker](../../LeanExe/ProofKit/PolyBound.lean), [its unions of intervals](../../LeanExe/ProofKit/PolyChecks.lean), [Taylor remainders](../../LeanExe/ProofKit/TaylorRemainder.lean), and [the series of `log (1 + x) - log (1 - x)`](../../LeanExe/ProofKit/LogRatioRemainder.lean).  The file module depends on 108 ProofKit modules in all.  The arc track wrote `F64RoundNearest` and `F64HalfUlp` for these proofs, and the arctangent and arcsine proofs use them as well.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| The polynomial difference within `(185/256) · 2^-58` on eight pieces of `[0, 15439/2^19]` | `Log1pKernelPoly.log1p_part_1` to `log1p_part_8` |
| `log (1 + q)` between rational sums of the series at `s = q/(2 + q)`, at the case boundaries `0.285`, `-0.175`, `0.2125`, `-0.2929`, and `0.41422` | `Log1pTheoremConst.log_ge`, `log_le`, applied with `decide +kernel` |
| `ln2_hi + ln2_lo` within `2^-81` of `log 2`, from 30 terms of the series at `1/3` | `Log1pTheoremConst.ln2_close` |
| The thresholds of the high-word tests as rationals | `Log1pTheorem.ax_lt`, applied with `decide +kernel` |
| The words of the exceptional results | `Log1pTheoremSpecial` |
| Function 3 is exported as `log1p` | `Log1pBytes.log1p_export` |
| The file's bytes equal the encoder's | `Log1pFile.log1p_file` |

### History

The eighth run of the main theorem exposed an error in the first statement of `corr_mid`: the main path takes negative `x` down to `-1228485/2^22`, where `u = 1 + x` rounds to at most `0.70710659`, above the bound `0.7071065` that `corr_mid` claimed and `main_reduce` assumed.  `main_reduce` now takes the code's own threshold `hu < 0x6a09e` as the hypothesis `u < 1482910/2^21`, and `corr_mid` proves it.  `linarith` failed on goals in `Log1pTheoremConst` and `F64RoundNearest` whose hypotheses held the same term in two normal forms, because its preprocessing normalizes a hypothesis with a division through `norm_num`, and the proofs now name such terms with `set` or `generalize` before calling it ([the journal](../../devnotes.md#2026-10-10-full-theorems-for-atan-and-log1p-track-arc-minideb2)).

## Tests

[The accuracy check](Log1pAccuracy.lean) compares `Log1p.log1p` natively with the double nearest to `log (1 + x)`, computed from `2 atanh (x/(2 + x))` with `Reference.atanhFixed` for `|x| ≤ 1/4` and from `Reference.log` of the exact `1 + x` elsewhere, and it fails at the first result more than one step away.  Its 350,144 arguments are 100,001 evenly spaced values from -1 to 10, 100,001 from -0.3 to 0.42, 100,000 hashed positive values over all exponents, 50,000 hashed values from -1 to 0, the five doubles around each of 13 thresholds of the code and of the `√2` crossings, the 53 doubles `-1 + 2^-k`, 13 special values, and the 11 inputs of `WorstCases.log1p`.  Those 11 are the inputs of the largest known `log1p` errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [9], whose Table 3 lists 0.896 units for FreeBSD 15.1.

In `opus-verified-tests-13.log` all 350,144 results lie within one step of the reference, and 12,128 of them differ from it, so the largest measured distance equals the proved bound.  Lean has no binding of the C library's `log1p`, so the check reports no comparison with it.  The reference's docstring bounds its truncation error below `2^-380` relative, a claim that is not proved, and a reference rounded the wrong way could only move a one-step check between passing results.

## Limits

The limits of [the exponential theorem](Exp.md#limits) apply in the same way: the theorem is about Talos's semantics, the interpreter and the decoder are trusted, the file theorem trusts `binary_file%`, Talos implements the deterministic profile in which every NaN result is canonical [7], and the argument is the bits of a Lean `Float`, so the theorem covers only the canonical NaN among the NaN words a WebAssembly caller can pass.  `log1p_bytes_accuracy` covers sequences of calls to `log1p`, and a host that calls `alloc`, `release`, or `log1pTail` or writes the memory between calls needs a theorem that the action preserves `Ready`.  The module reads no table, so the store invariant has only the allocator invariant and the memory cap.

The docstring of `Log1p.lean`, following fdlibm's comment, says that the cubic path serves `|f| < 2^-20`.  The code's test `hu = 0` also selects it in the halved branch for `1 + f` within `3 · 2^-21` below 1, and the proof uses the bound `|f| ≤ 2^-19` (`Log1pTheoremReduce.main_reduce`).  The theorem therefore covers the path, and only the docstring's description is too narrow.

## References

1. FreeBSD, [`lib/msun/src/s_log1p.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_log1p.c), commit `20381bce4b63975494a2f4bc84257f6932e6d379`.  Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with the notice.
2. FreeBSD, [`lib/msun/src`](https://github.com/freebsd/freebsd-src/tree/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src), the same commit.
3. Sun Microsystems, [FDLIBM version 5.3 readme](https://www.netlib.org/fdlibm/readme), netlib: "FDLIBM (Freely Distributable LIBM) is a C math library for machines that support IEEE 754 floating-point arithmetic."
4. NIST, *Digital Library of Mathematical Functions*, [§4.6 Power Series](https://dlmf.nist.gov/4.6), Eq. 4.6.4, the series of `ln z` in `(z - 1)/(z + 1)`.
5. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229).  Clause 9.2 with Table 9.1 and clause 9.2.1 were read.
6. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.3.9, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
7. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
8. The Mathlib Community, Mathlib at commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`, [`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean), `Real.hasSum_log_sub_log_of_abs_lt_one` and `Real.abs_log_sub_add_sum_range_le`.
9. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
