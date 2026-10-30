# The arcsine and arccosine

[The implementation](Program.lean) exports `asin` and `acos`, ports of fdlibm's `e_asin.c` and `e_acos.c` as FreeBSD's msun has them [1].  The decided bound is one representable step from the nearest-even rounding of `arcsin x` and of `arccos x`, unchanged by the review of the worst inputs of Zimmermann's report ([the journal](../../../../devnotes.md#2026-10-11-zimmermanns-inputs-in-the-accuracy-checks)).  The theorems prove the bound for every finite `x` with `|x| ≤ 1` and the exceptional values as words, and `AsinBytes.asin_module_accuracy` carries both functions to the decoded WebAssembly module, with `AsinFile.asin_file` connecting that module to `build/verified/asin.wasm`.  No accepted theorem depends on an axiom other than `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`asin` computes `Real.arcsin a` and `acos` computes `Real.arccos a` for the value `a` of the argument, on the domain `[-1, 1]`.  The bounds are `F64SignedRounding.WithinSteps 1 (Real.arcsin a) w` and `WithinSteps 1 (Real.arccos a) w`, with `WithinSteps` from [the signed rounding reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean): `w` is not a NaN, and its position on the ordered line of doubles, with both zeros at 0, lies within one of the position of the nearest-even rounding.  Mathlib's `Real.arcsin` and `Real.arccos` take values in `[-π/2, π/2]` and `[0, π]`, the principal values.

| Function and input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `asin (±0)` | `±0` | IEEE 754-2019 9.2.1 [4]; C99 F.9.1.2 [5] | `asin_zero`, `asin_neg_zero` |
| `asin (±1)` | `±π/2` rounded | bound | `asin_within_one` |
| `acos 1` | `+0` | IEEE 754-2019 9.2.1 (`acos (1)` is `+0`); C99 F.9.1.1 | `acos_one` |
| `acos (-1)` | `π` rounded | bound | `acos_within_one` |
| `\|x\| > 1`, `±∞` | canonical NaN | IEEE 754-2019 Table 9.1 (domain `[-1, +1]`, invalid outside); C99 F.9.1.1 and F.9.1.2; the deterministic profile of WebAssembly [6] | `asin_nan`, `acos_nan` |
| NaN | canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly | `asin_nan`, `acos_nan` |

IEEE 754-2019 recommends both operations in clause 9.2, where a conforming implementation rounds correctly [4].  fdlibm states no error bound for either function.  It bounds the Remez error of its rational approximation by `2^-58.75`, a bound that the stored coefficients exceed, as the section on the kernel bound explains.  The theorems say nothing about floating-point exceptions, which the port does not compute.

## Algorithm

Both functions use one rational function, `R(t) = p(t)/q(t)` with `p(t) = t (pS0 + pS1 t + ⋯ + pS5 t⁵)` and `q(t) = 1 + qS1 t + ⋯ + qS4 t⁴`, which approximates `(arcsin √t - √t)/√t` on `0 ≤ t ≤ 1/4`.  Below `1/2` in magnitude, `asin x = x + x R(x²)` and `acos x = π/2 - (x + x R(x²))`, the latter computed as `pio2_hi - (x - (pio2_lo - x R(x²)))` so that `π/2` enters in two parts.  The series that `R` approximates is DLMF 4.24.1 [3].  Below `2^-26` `asin` returns `x`, and for `|x| < (1 + 2^-20) · 2^-57`, where the high word is at most `0x3c600000` (`AcosTheorem.ix_tiny`), `acos` returns `pio2_hi + pio2_lo`.

From `1/2` on, the half-angle identities `arcsin |x| = π/2 - 2 arcsin √z` and `arccos x = 2 arcsin √z`, with `z = (1 - |x|)/2 ≤ 1/4`, and `arccos x = π - 2 arcsin √z` with `z = (1 + x)/2` for negative `x`, bring the argument of `R` back into its range.  The argument `z` is exact: `1 - |x|` by Sterbenz's lemma, and the halving because `1 - |x|` lies on the grid of `2^-53`.  With `s = √z`, `arcsin √z ≈ s + s R(z)`.

| Function and range | Result |
|---|---|
| `asin`, `0.975 ≤ \|x\| < 1` | `pio2_hi - (2 (s + s r) - pio2_lo)` |
| `asin`, `1/2 ≤ \|x\| < 0.975` | `pio4_hi - (p - q)` with `w` the high 32 bits of `s`, `c = (z - w²)/(s + w)`, `p = 2 s r - (pio2_lo - 2c)`, and `q = pio4_hi - 2w` |
| `acos`, `-1 < x ≤ -1/2` | `π - 2 (s + (r s - pio2_lo))` |
| `acos`, `1/2 ≤ x < 1` | `2 (w + (r s + c))` with `w` and `c` as for `asin` |

The split `s = w + c` in the middle range of `asin` and the positive range of `acos` carries the bits of `√z` below the last place of `s`, which the subtraction from `π/4` in `asin` and the small results of `acos` near 1 would otherwise lose.  `w` has at most 21 significant bits, so `w²` is exact (`AsinTheoremSupport.trunc_facts`), and `w + c` lies within `2^-70` of `√z`, as the docstrings of `AsinTheoremMid` and `AcosTheoremPos` state.  `r = R(z)` is the same computation in every branch.

## Implementation

The sources are `lib/msun/src/e_asin.c` and `lib/msun/src/e_acos.c` of FreeBSD [1], each `Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.` with the notice "Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved."  fdlibm is Sun's "Freely Distributable LIBM" [2].  The module docstring of [the implementation](Program.lean) quotes the notice verbatim, as the notice requires.

The port follows the dialect of the Verified compiler as [the exponential document](../Exp/README.md#implementation) describes.  `verified_compile compiled := [asinRatio, asin, acos]` generates a module whose functions are `alloc` (0), `release` (1), `asinRatio` (2), `asin` (3), and `acos` (4).  Every named constant of the C code is `Float.ofBits` of its bit pattern, and the module reads no table.

| C code | Port | Reason |
|---|---|---|
| `p`, `q`, and `p/q` written out in each branch | `asinRatio t`, with the same operations in the same order | One function serves every branch. |
| `SET_LOW_WORD (w, 0)` | `Float.ofBits (s.toBits &&& 0xFFFFFFFF00000000)` | The dialect has word operations and no word macros. |
| `huge + x > one` | kept as a test | It serves only to raise inexact, and it holds for every finite `x` with `\|x\| < 1` (`AtanTheorem.huge_gt`), so it changes no result. |
| Signed `int32_t` high word `hx`, tested with `hx > 0` | `UInt64` word, its sign the top bit | The dialect has no signed integers, and `hx = 0` cannot occur on the paths that test it. |
| `pio2_lo` volatile in `e_acos.c` | its value | The volatile access serves only to prevent constant folding. |

| Constant | Bits | Constant | Bits |
|---|---|---|---|
| `pS0` | `0x3FC5555555555555` | `qS1` | `0xC0033A271C8A2D4B` |
| `pS1` | `0xBFD4D61203EB6F7D` | `qS2` | `0x40002AE59C598AC8` |
| `pS2` | `0x3FC9C1550E884455` | `qS3` | `0xBFE6066C1B8D0159` |
| `pS3` | `0xBFA48228B5688F3B` | `qS4` | `0x3FB3B8C5B12E9282` |
| `pS4` | `0x3F49EFE07501B288` | `pio2_hi` | `0x3FF921FB54442D18` |
| `pS5` | `0x3F023DE10DFDF709` | `pio2_lo` | `0x3C91A62633145C07` |
| `pio4_hi` | `0x3FE921FB54442D18` | `pi` | `0x400921FB54442D18` |
| `huge` | `0x7E37E43C8800759C` (`1.0e300`) | | |

Each file prints the bits of 14 constants beside their decimal values, and each decimal value rounds to its printed word ([the journal's audit of the ports](../../../../devnotes.md#2026-10-10-ports-of-log1p-atan-atan2-asin-acos-and-tan)).  Each `Float.ofBits` word of `Asin.lean` equals the word that the pinned `e_asin.c` or `e_acos.c` prints for the same constant, and `huge`, which the source gives without bits, is the nearest double to `1.0e300`.  The kernel bound restates `pS0` to `qS4` as `PolyBound.ratOfWord` of the same words.

## Theorems

The theorems are in [the `asin` theorem](AsinTheorem.lean), [the `acos` theorem](AcosTheorem.lean), [the exceptional values](AsinTheoremSpecial.lean), [the byte theorems](AsinBytes.lean), and [the file theorem](AsinFile.lean).  `x` is a Lean `Float` and `a = value x.toBits` its real value.  The byte theorems use `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `AsinTheorem.asin_within_one` | For finite `x` with `\|a\| ≤ 1`, `WithinSteps 1 (Real.arcsin a) (Asin.asin x).toBits`. |
| `AcosTheorem.acos_within_one` | For finite `x` with `\|a\| ≤ 1`, `WithinSteps 1 (Real.arccos a) (Asin.acos x).toBits`. |
| `AsinTheoremSpecial.asin_zero`, `asin_neg_zero` | `±0` give `±0`. |
| `acos_one` | `1` gives `+0`. |
| `asin_nan`, `acos_nan` | Every `x` other than a finite `x` with `\|a\| ≤ 1` gives `Wasm.IEEE64.canonicalNaN`. |
| `AsinBytes.ready_initial` | The initial store satisfies `Ready`: the allocator invariant and a memory cap of at most 65,535 pages. |
| `AsinBytes.asin_entry_call`, `acos_entry_call` | A call of function 3 or 4 from a `Ready` store returns, without a trap, the bits of the Lean function, and leaves a `Ready` store in which every heap region keeps its bytes. |
| `AsinBytes.asin_bytes_accuracy`, `acos_bytes_accuracy` | `Asin.compiled.module` encodes to bytes that decode to it, exports the function, starts in a `Ready` store, and every call from a `Ready` store returns the bits of the Lean function, within one step for finite `x` with `\|a\| ≤ 1`, and leaves a `Ready` store. |
| `AsinBytes.asin_module_accuracy` | Conjunction of the two byte theorems. |
| `AsinFile.asin_file`, `asin_file_decode` | `build/verified/asin.wasm` holds `encode Asin.compiled.module`, and the file decodes to the module of `asin_module_accuracy`. |

`asin_file_decode` takes its bytes from `asin_module_accuracy`, so its axiom report covers both byte theorems, which `tests/verified/run.sh` requires because it reads only the two axiom reports of the file module.  `tests/verified/run.sh` builds `Library.Numerics.Float64.Asin.AsinBytes`, checks `AsinFile.lean` against the `asin.wasm` that it writes earlier in the same run, and fails unless both file theorems report exactly the three permitted axioms.  The recorded run of 2026-10-11 passed that check and printed `[propext, Classical.choice, Quot.sound]` for both accuracy theorems, every exceptional value, and the three byte theorems.  Another build printed the same report, and [the journal](../../../../devnotes.md#2026-10-10-full-theorems-for-log1p-atan-atan2-asin-and-acos-track-arc) records the builds that first accepted `asin_within_one`, `acos_within_one`, the exceptional values, the byte theorems, and the file theorems.

## Proof

### Modules

The chain reuses word and exactness lemmas of [the `log1p` proof](../Log1p/README.md) (`Log1pTheoremReduce`, `Log1pTheoremCorr`, `Log1pTheoremTail`, `Log1pTheoremSpecial`) and of [the arctangent proof](../Atan/README.md) (`AtanTheorem`, `AtanTheoremReduce`, `AtanTheoremConst`, `AtanTheoremSpecial`), among them `AtanTheoremConst.atan_inf`, which places `pio2_hi + pio2_lo` within `2^-64` of `π/2`.  The table lists the chain's own modules in dependency order.  Two of them are generated: `tools/arc/asin/mkratio.py` writes `AsinTheoremRatio.lean`, and `tools/arc/asin/mkmid.py` writes `AsinTheoremMid.lean`, both with constants from the range analyses of the `model*.py` files in the same directory ([the journal](../../../../devnotes.md#2026-10-10-full-theorems-for-log1p-atan-atan2-asin-and-acos-track-arc)).

| Module | Content |
|---|---|
| `AsinKernelPoly` | Kernel bound `asin_kernel_error`. |
| `AsinTheoremSupport` | Clearing the low word of `s`: the same exponent, `s - w < 2^-20 s`, and at most 21 significant bits, so `w · w` is exact. |
| `AsinTheoremRatio` | Error chains of `asinRatio t` for seven ranges of `t` (`ratio_S1`, `ratio_S2`, `ratio_A1` to `ratio_A4`, `ratio_W`), with partial sums of both Horner schemes bounded by `PolyBound.check`. |
| `AsinTheoremBranches` | Branches of `asin` and `acos` as equations on the high word. |
| `AsinTheoremSmall` | `asin` below `1/2`. |
| `AsinTheoremHalf` | Half-angle identities and exact `z`. |
| `AsinTheoremBig`, `AsinTheoremMid` | `asin` from `0.975` to 1, and from `1/2` to `0.975` in three ranges (`mid_A`, `mid_B`, `mid_C`). |
| `AsinTheorem` | `asin_within_one`. |
| `AcosTheoremBranches`, `AcosTheoremSmall`, `AcosTheoremNeg`, `AcosTheoremPos`, `AcosTheorem` | Same for `acos`: the exact `z = (1 ± x)/2`, the paths below `1/2`, below `-1/2`, and above `1/2`, and `acos_within_one`. |
| `AsinTheoremSpecial`, `AsinBytes`, `AsinFile` | Exceptional values, byte theorems, and the file theorem. |

### Kernel bound

`AsinKernelPoly.asin_kernel_error` states `|arcsin x - x - x³ P(x²)/Q(x²)| ≤ |x|³ · (11/16) · 2^-56` for `|x| ≤ 1/2`, where `x³ P/Q` is the code's `x R(x²)` in exact arithmetic.  The proof compares `P/Q` with the Taylor polynomial `T` of `(arcsin x - x)/x³` in `t = x²` of degree 34 through the weighted bound `|T q - p| ≤ ε q` with `ε = (43/64) · 2^-56`.  `PolyBound.check` proves the two one-sided bounds `T q - p - ε q ≤ 0` and `T q - p + ε q ≥ 0`, each on four pieces of `[0, 1/4]` (`asin_up_1` to `asin_up_4`, `asin_lo_1` to `asin_lo_4`), and `asin_q_range` places `q` in `[1/2, 1]` there.  A plain bound divided by the smallest denominator would lose accuracy, since `q` falls from 1 to about 0.515 on the range.

Mathlib has no series for `arcsin`, so [the arcsine remainder](../../../../LeanExe/ProofKit/AsinRemainder.lean) proves one without series.  The truncation `S` of the binomial series of `(1 - u)^(-1/2)` to 36 terms satisfies `1 - (1 - u) S(u)² = u^36 G(u)`: `defect_low` checks that the first 36 coefficients of the left side vanish, and `defect_high` bounds `G` by `1/2` on `[0, 1/4]`.  With `y = 1/√(1 - u)`, the identity `(y - S)(1 - u)(y + S) = u^36 G(u)` bounds `y - S`, and the mean value inequality, applied to `arcsin` minus its Taylor polynomial, whose derivative is `y - S` at `u = t²`, bounds the remainder by `(4/3) γ |x|^73`.  The derivative of `arcsin` and the mean value inequality come from Mathlib [7].

fdlibm's comment bounds the Remez error of `R` by `2^-58.75`, which describes the approximation with exact coefficients.  `pS0` is `1/6` rounded down, and its rounding alone gives an error of `1/6 - pS0 ≈ 2^-56.58` at `x = 0`, the largest on `[0, 1/2]` ([the journal on the kernel polynomials](../../../../devnotes.md#2026-10-10-kernel-polynomials-of-stage-3-track-poly)).  The function proofs use the proved bound, `(11/16) · 2^-56`, about `2^-56.54`, and the margins below include it.

### Error budget

Each path ends with one of the criteria that [the `log1p` document](../Log1p/README.md#error-budget) describes.  `F64RoundNearest.sub_within` and `add_within` charge nothing for the last rounding: they accept an exact value of the last operation less than one spacing of a binade at or below the target from the target.  `add_within_rel` and `within_one_of_rounded_rel` accept an exact value within the fraction `1/(2^53 + 1)` of the target, and `F64WithinSelf.within_one_of_self` covers a result equal to the argument.  The bounds and allowances of the table are the constants of the Lean statements.

| Function and range | Theorem | Proved bound | Allowance |
|---|---|---|---|
| `asin`, `\|x\| < 2^-26` | `AsinTheoremSmall.tiny_within` | `\|arcsin x - x\| ≤ \|x\|³/5` | relative `2^-53` |
| `asin`, `2^-26 ≤ \|x\| < 1/2` | `AsinTheorem.small_within` | relative `0.9 · 2^-53` | relative `1/(2^53 + 1)` |
| `asin`, `[1/2, 3/5]` and `[3/5, 9/10]` | `AsinTheoremMid.mid_A`, `mid_B` | `0.98 · 2^-53`, result at or above `1/2` | one spacing, `2^-53` |
| `asin`, `[9/10, 0.975]` | `mid_C` | `0.625 · 2^-52`, result at or above 1 | one spacing, `2^-52` |
| `asin`, `[0.975, 1)` | `AsinTheoremBig.big_within` | `0.5 · 2^-52` | one spacing, `2^-52` |
| `acos`, `\|x\| < 2^-56` | `AcosTheoremSmall.tiny_within` | `2^-54` between `pio2_hi + pio2_lo` and `arccos x`, result in `[1, 3/2]` | one spacing, `2^-52` |
| `acos`, `2^-58 ≤ \|x\| < 1/2` | `AcosTheoremSmall.small_within` | `0.75 · 2^-52`, result in `[1, 2.1)` | one spacing, `2^-52` |
| `acos`, `-1 < x ≤ -1/2` | `AcosTheoremNeg.neg_within` | `0.875 · 2^-51`, result in `[2π/3, π]` | one spacing, `2^-51` |
| `acos`, `1/2 ≤ x < 1` | `AcosTheoremPos.pos_within` | relative `0.7 · 2^-53` | relative `1/(2^53 + 1)` |
| both, `\|x\| = 1` | `AsinTheorem.asin_unit`, `AcosTheorem.acos_unit` | constants | one step |

The code takes the tiny path of `acos` below `(1 + 2^-20) · 2^-57`, inside the range of `tiny_within`, and `small_within` covers the rest from `2^-58` on.  The smallest margin is that of `mid_A` and `mid_B`, 2 percent of a spacing of `[1/2, 1)`, which serves as the allowance for results from `π/6` to `arcsin 0.9 ≈ 1.12`.  On the positive range of `acos` the result reaches down to about `2^-26`, so its bounds are relative to `s₀ = √z`, and the doubling `2 (w + ...)` keeps a nearest word nearest (`F64RoundDouble`).  A negative `x` in `asin` gives the negated word, and `AsinTheorem.signed_asin` carries the bound through the negation.

### Shared modules

The analysis uses [error tracking for straight-line code](../../../../LeanExe/ProofKit/F64Approx.lean), [half-spacing sums](../../../../LeanExe/ProofKit/F64HalfUlp.lean), [nearest rounding of sums](../../../../LeanExe/ProofKit/F64RoundNearest.lean), [doubling a nearest word](../../../../LeanExe/ProofKit/F64RoundDouble.lean), [functions that return their argument](../../../../LeanExe/ProofKit/F64WithinSelf.lean), [exact operations and Sterbenz's lemma](../../../../LeanExe/ProofKit/F64Exact.lean), [exact products](../../../../LeanExe/ProofKit/F64ExactProduct.lean), [fdlibm's high-word tests](../../../../LeanExe/ProofKit/F64UpperWord.lean), [the polynomial checker](../../../../LeanExe/ProofKit/PolyBound.lean), [its unions of intervals and weighted bounds](../../../../LeanExe/ProofKit/PolyChecks.lean), [Taylor remainders](../../../../LeanExe/ProofKit/TaylorRemainder.lean), and [the arcsine remainder](../../../../LeanExe/ProofKit/AsinRemainder.lean).  The square root's rounding enters through `F64Approx.fapprox_sqrt`, which rests on `F64SqrtBounds`.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| Weighted bound of `T q - p` by `(43/64) · 2^-56 q` on eight one-sided pieces of `[0, 1/4]` | `AsinKernelPoly.asin_up_1` to `asin_up_4`, `asin_lo_1` to `asin_lo_4` |
| `q` in `[1/2, 1]` on `[0, 1/4]` | `asin_q_range` |
| The first 36 coefficients of `1 - (1 - u) S(u)²` vanish, and the rest is bounded by `1/2` on `[0, 1/4]` | `defect_low`, `defect_high` |
| Bounds of the partial Horner sums in seven ranges of `t` | `AsinTheoremRatio.ratio_S1`, `ratio_S2`, `ratio_A1` to `ratio_A4`, `ratio_W` |
| Thresholds of the high-word tests as rationals | `AsinTheorem.ix_one`, `ix_26`, `ix_half`, `ix_big`, `AcosTheorem.ix_tiny` |
| Functions 3 and 4 are exported as `asin` and `acos` | `AsinBytes.asin_export`, `acos_export` |
| The file's bytes equal the encoder's | `AsinFile.asin_file` |

### History

`AsinTheoremMid` and `AcosTheoremPos.pos_core` raise `maxHeartbeats` to 1,000,000 and 4,000,000, because their many `nlinarith` calls run in large contexts.  `nlinarith` also spent minutes in `whnf` on a power when the context held `scaledMagnitude w = q * 2^(e - 1 + 32)`, which `AsinTheoremMid` clears once used.  `rw [← hsqv]` with `hsqv : √t * √t = t` also rewrote the `t` inside `√t`, so the proofs name `√t` with `set` ([the journal](../../../../devnotes.md#2026-10-10-full-theorems-for-log1p-atan-atan2-asin-and-acos-track-arc)).

## Tests

[The accuracy check](../../../../tests/TestSupport/Numerics/AsinAccuracy.lean) compares `Asin.asin` and `Asin.acos` natively with the doubles nearest to `arcsin x` and `arccos x`, computed by `ArcReference.asinFixed`, as `2 atan (x/(1 + √(1 - x²)))`, and `ArcReference.acosFixed`, as `2 atan √((1 - x)/(1 + x))`, or `π - 2 atan √((1 + x)/(1 - x))` for negative `x`, and it fails at the first result more than one step away.  Its 200,188 arguments, each giving one result of each function, are 100,001 evenly spaced values from -1 to 1, 100,000 hashed values over the exponents below 1 with both signs, the 106 doubles `±(1 - 2^-k)` for `k` from 1 to 53, the five doubles at and next to each of ten thresholds, `±1` among them, 11 special values, and the 20 inputs of `WorstCases.asin` and `WorstCases.acos`.  Those 20 are the inputs of the largest known errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [8], whose Table 3 lists 0.981 units for FreeBSD 15.1's `asin` and 0.930 for its `acos`.

In the test run of 2026-10-11, all 400,376 results lie within one step of the reference, and 13,563 of them differ from it, so the largest measured distance equals the proved bound.  The C library of the test run lies within one step at the same arguments, with 239 results unequal to the reference.  The reference's docstrings bound its truncation errors below `2^-390` relative for `asin` and `2^-560` for `acos`, and no theorem proves these bounds.

## Limits

The limits of [the exponential theorem](../Exp/README.md#limits) apply in the same way: the theorem is about Talos's semantics, the interpreter and the decoder are trusted, the file theorem trusts `binary_file%`, Talos implements the deterministic profile in which every NaN result is canonical [6], and the argument is the bits of a Lean `Float`, whose only NaN is the canonical one (`F64Bits.toBits_canonical`), so the theorems cover only the canonical NaN among the NaN words a WebAssembly caller can pass.  The byte theorems cover sequences of calls to `asin` and `acos`, and a host that calls `alloc`, `release`, or `asinRatio` or writes the memory between calls needs a theorem that the action preserves `Ready`.  The module reads no table, so the store invariant has only the allocator invariant and the memory cap.

The byte theorems state the bound only on the domain `|a| ≤ 1`.  `AsinTheoremSpecial` gives the words of the exceptional inputs for the Lean functions, and the byte theorems' equality `w = (Asin.asin x).toBits`, or the same for `acos`, carries them to the module.  The docstring of `Asin.lean` gives fdlibm's bound of `2^-58.75` for `P/q` as a bound for exact coefficients, which the stored coefficients exceed at `x = 0`, as the section on the kernel bound explains.  The Python scripts in `tools/arc/asin` generated modules that Lean checks, so the theorems do not rest on them.

## References

1. FreeBSD, [`lib/msun/src/e_asin.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_asin.c) and [`lib/msun/src/e_acos.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_acos.c).
2. Sun Microsystems, [FDLIBM version 5.3 readme](https://www.netlib.org/fdlibm/readme), netlib.
3. NIST, *Digital Library of Mathematical Functions*, [§4.24 Inverse Trigonometric Functions: Further Properties](https://dlmf.nist.gov/4.24), Eq. 4.24.1.
4. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229), clause 9.2, Table 9.1, and clause 9.2.1.
5. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9, F.9.1.1, and F.9.1.2; WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf), September 7, 2007.
6. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html).
7. The Mathlib Community, Mathlib, [`Mathlib/Analysis/SpecialFunctions/Trigonometric/InverseDeriv.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Trigonometric/InverseDeriv.lean) (`Real.hasDerivAt_arcsin`) and [`Mathlib/Analysis/Calculus/MeanValue.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/Calculus/MeanValue.lean) (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`).
8. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026, Tables 3 to 11.
