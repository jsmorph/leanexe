# The base-10 logarithm

[The implementation](Program.lean) exports `log10`, a port of fdlibm's `log10` as FreeBSD's msun has it [1, 2]: a reduction `x = 2^k (1 + f)` with `√2/2 < 1 + f < √2`, the kernel `k_log1p` of `k_log.h`, which evaluates a polynomial of degree 14 in `s = f/(2 + f)`, and a sum `(f - f²/2 + k_log1p f)/ln 10 + k log10 2` carried in extra precision.  The port comes from fdlibm because Arm's optimized-routines has no double `log10` in `math/`.  The decided bound, which [the plan's table of functions](../../../../transcendentals.md#functions) records, is one representable step from the nearest-even rounding of `log x / log 10`, `F64SignedRounding.WithinSteps 1`, as [the journal section on the port](../../../../devnotes.md#2026-10-10-ports-of-exp2-exp10-log2-log10-and-pow) proposes.  `Log10Theorem.log10_within_one` proves the bound for every finite positive input, subnormals included, `Log10Theorem.log10_pow10` proves `log10 (10^n) = n` for `n` from 0 to 22, and `Log10Theorem.log10_bytes_accuracy` carries the bound to the decoded WebAssembly module, with `Log10File.log10_file` connecting that module to `build/verified/log10.wasm`.  Every theorem below reports no axioms other than `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`log10` computes `Real.logb 10` of the value of its argument, which Mathlib defines as `Real.log x / Real.log 10` [7].  The domain is the finite doubles with positive value, where `|log10 x|` stays below 324, so every result in the domain is finite.  The theorem's target is `Real.logb 10`, and its proof works with `(k log 2 + log (1 + f))/log 10`.

`Log10Theorem.log10_within_one` states the bound: for finite `x` with `0 < value x.toBits`, `F64SignedRounding.WithinSteps 1 (Real.logb 10 (value x.toBits)) (Log10.log10 x).toBits`.  [The signed reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean) defines `WithinSteps n y w` to hold when `w` is not a NaN and its `position` on the ordered line of doubles lies within `n` of the position of the nearest-even reference of `y`, which negates the reference of `|y|` for negative `y`.  `Log10Theorem.log10_pow10` adds the exact results at the powers of ten that binary64 holds, which the one-step bound alone would not give.

| Input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `1` | `+0` (bits `0`) | IEEE 754-2019 9.2.1 [4], C99 F.9.3.8 [5] | `log10_one_bits` |
| `10^n`, `0 ≤ n ≤ 22` | the double `n` | correct rounding, IEEE 754-2019 9.2, since `n` is a double | `log10_pow10` |
| `+0`, `-0` | `-∞` (`0xFFF0000000000000`) | IEEE 754-2019 9.2.1 (with the divideByZero exception), C99 F.9.3.8 | `log10_zero` |
| `+∞` | `+∞` | IEEE 754-2019 9.2.1, C99 F.9.3.8 | `log10_pos_infinity` |
| negative, `-∞` included, other than `-0` | the canonical NaN `0x7FF8000000000000` | IEEE 754-2019 9.2 (a quiet NaN outside the domain `[0, +∞]`, with the invalid exception), C99 F.9.3.8 | `log10_negative` |
| NaN | the canonical NaN | IEEE 754-2019 9.2 (a quiet NaN for a NaN operand), C99 F.9 paragraph 11, the deterministic profile of WebAssembly [6] | `log10_nan` |

IEEE 754-2019 lists `log10` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [4].  The one-step bound is weaker than correct rounding.  fdlibm states no error for `log10`, and `k_log.h` states an error below one unit in the last place for the natural logarithm that the same kernel computes [2].  The theorem says nothing about the divideByZero and invalid exceptions, which the port does not compute.

## Algorithm

The comment of `k_log.h` states the method [2].  The reduction finds `k` and `f` with `x = 2^k (1 + f)` and `√2/2 < 1 + f < √2`.  With `s = f/(2 + f)`, `log (1 + f) = log (1 + s) - log (1 - s) = 2s + (2/3) s³ + (2/5) s⁵ + …`, written `2s + s R`, and a Remez polynomial `Lg1 s² + … + Lg7 s^14` of degree 14 approximates `R` on `[0, 0.1716]` within `2^-58.45`.  `k_log1p` returns `s (f²/2 + R)`, which equals `log (1 + f) - f + f²/2` in exact arithmetic, since `f²/2 - s f = s f²/2`, although the header comment of `k_log.h` says that it returns `log (1 + f) - f`.  The caller adds `f - f²/2` and the multiple of `ln 2`, for accuracy in other bases [2].

`log10` takes the high word of `x`, scales a subnormal argument by `2^54`, and adds 1 to `k` when the top 20 fraction bits reach `0x6a09c`, those of `√2`, so that the exponent field of the reduced `x'` is that of 1 or of `1/2` [1].  It computes `f = x' - 1`, `hfsq = f²/2`, and `r = k_log1p f`, and splits `f - hfsq` into `hi`, with its low 32 bits cleared, and `lo = (f - hi) - hfsq + r`.  The result is `val_lo + w`, where `w = k · log10_2hi + hi · ivln10hi` and `val_lo` collects `k · log10_2lo`, `(lo + hi) · ivln10lo`, `lo · ivln10hi`, and the rounding error of `w`, with `1/ln 10 = ivln10hi + ivln10lo` and `log10 2 = log10_2hi + log10_2lo` each split in two [1].  fdlibm's comment says that the extra precision in adding `k · log10_2hi` reduces the error for many arguments at little cost, although no large cancellation occurs near `√2` or `√2/2` [1].

The guards on the high word handle the rest.  Both zeros give `-two54/0`, which is `-∞`, a negative argument gives `(x - x)/0`, which is NaN, `+∞` and a NaN without the sign bit give `x + x`, and `1` gives `+0` [1].  The scaling of a subnormal argument by `2^54` is exact, and `k` starts at -54 for it.

## Implementation

The source is `lib/msun/src/e_log10.c` and `lib/msun/src/k_log.h` of FreeBSD [1, 2].  Both files carry Sun Microsystems' notice: "Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.  Developed at SunSoft, a Sun Microsystems, Inc. business.  Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved."  The module docstring of [the implementation](Program.lean) quotes the notice verbatim, as the notice requires.  The functions use only double arithmetic and word operations, so no configuration choice arises.

The port uses the Verified dialect, the subset of Lean that [the Verified compiler](../../../../Verified/README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [kLog1p, log10]` generates the module, whose functions are `alloc` (0), `release` (1), `kLog1p` (2), and `log10` (3).  The module has no tables, so its `Ready` invariant holds only the allocator invariant and the memory cap.  The port writes each constant as `Float.ofBits` of the bit pattern that fdlibm gives beside its decimal value.

| C code | Port | Reason |
|---|---|---|
| signed `int32_t hx`, tested with `hx < 0x00100000` and `hx < 0` | the word `x.toBits >>> 32`, with the sign bit tested first | The dialect's words are unsigned, and a comparison with a positive bound must also test the sign. |
| zero test inside `hx < 0x00100000`, then `hx < 0`, then the subnormal scaling | the zero test for a negative or small `hx`, then the sign, then the scaling | Same results in the same cases, as nested tests on words. |
| signed `int32_t k`, `y = (double) k` | a two's complement word, converted as `Log.logCore` converts its `k` | The dialect converts unsigned words. |
| `-two54/vzero`, `(x - x)/zero` | `-two54 / 0.0`, `(x - x) / 0.0` | The dialect has no floating-point flags, and these expressions keep their values. |
| `SET_HIGH_WORD`, `SET_LOW_WORD`, `EXTRACT_WORDS` | shifts, masks, and `Float.ofBits` | The dialect reads and writes the words of a double through `toBits` and `ofBits`. |

| Constant | Bits | Decimal in fdlibm |
|---|---|---|
| `two54` | `0x4350000000000000` | `1.80143985094819840000e+16` |
| `ivln10hi`, `ivln10lo` | `0x3FDBCB7B15200000`, `0x3DBB9438CA9AADD5` | `4.34294481878168880939e-01`, `2.50829467116452752298e-11` |
| `log10_2hi`, `log10_2lo` | `0x3FD34413509F6000`, `0x3D59FEF311F12B36` | `3.01029995663611771306e-01`, `3.69423907715893078616e-13` |
| `Lg1` to `Lg7` | `0x3FE5555555555593` to `0x3FC2F112DF3E5244` | `6.666666666666735130e-01` to `1.479819860511658591e-01` |

In `e_log10.c` and `k_log.h` at the pinned commit, each of the twelve decimal values converts to the bit pattern beside it, and the port holds each of those bit patterns.  `Lg1` to `Lg7` are the words of `Lp1` to `Lp7` in fdlibm's `s_log1p.c` [3], which [the port of `log1p`](../Log1p/Program.lean) holds.  `Log1pKernelPoly.log1p_kernel_error` therefore bounds the polynomial of both functions.

## Theorems

The theorems are in [the base-10 logarithm theorem module](Log10Theorem.lean) and [the file module](Log10File.lean).  `x` is a Lean `Float`, and a word is the `UInt64` bit pattern of a double.  The byte theorem uses `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `log10_normal_within` | For a positive normal `x` other than 1, `WithinSteps 1 (Real.logb 10 (value x.toBits)) (Log10.log10 x).toBits`. |
| `log10_subnormal_within` | Same bound for a positive subnormal `x`. |
| `log10_within_one` | Same bound for every finite `x` with positive value. |
| `log10_pow10` | For `n ≤ 22` and `value x.toBits = 10^n`, `value (Log10.log10 x).toBits = n`. |
| `log10_one_bits`, `log10_zero`, `log10_pos_infinity` | Bits `0`, `0xFFF0000000000000`, and `0x7FF0000000000000` for `1`, `±0`, and `+∞`. |
| `log10_negative`, `log10_nan` | A negative argument other than `-0`, `-∞` included, and a NaN give `Wasm.IEEE64.canonicalNaN`. |
| `ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant and a memory cap of at most 65,535 pages. |
| `log10_entry_call` | A call of function 3 from a store satisfying `Ready` returns, without a trap, the bits of `Log10.log10 x` and leaves a store satisfying `Ready` in which every heap region keeps its bytes. |
| `log10_bytes_accuracy` | `Log10.compiled.module` encodes to bytes that decode to it, exports function 3 as `log10`, starts in a `Ready` store, and every call from a `Ready` store returns the bits of `Log10.log10 x`, within one step of `Real.logb 10` for finite `x` with positive value, and leaves a `Ready` store.  The statement covers every call in a sequence of calls to `log10`. |
| `Log10File.log10_file`, `log10_file_decode` | `build/verified/log10.wasm` holds `encode Log10.compiled.module` and decodes to the module of `log10_bytes_accuracy`. |

Every theorem in the table has a `#print axioms` line, and `log10_bytes_accuracy` reports only the three permitted axioms, as [the journal](../../../../devnotes.md#2026-10-11-decisions-on-tanh-the-reflector-and-the-bessel-bounds) records.  `tests/verified/run.sh` builds `Library.Numerics.Float64.Log10.Log10Theorem`, checks `Log10File.lean` against the `log10.wasm` that it writes earlier in the same run, and fails unless both file theorems report exactly the three permitted axioms.  Its run of 2026-10-11 passed that check and printed the permitted report for every theorem in the table.

## Proof

### Modules

The proof has six modules in `Library/Numerics/Float64/Log10/` above the implementation, besides the file module.  It reuses the guards of `LogBranches`, the subnormal and power lemmas of the `log2` proof, and `Log1pKernelPoly` for the polynomial.  The table lists them in dependency order, and [the library aggregate](../../../../Library.lean) includes `Log10Theorem`.

| Module | Content |
|---|---|
| `Log10Bits` | `kLog1p` and the tail after `f` on words, the reduction of the argument word (`xr_fields`), and the path lemmas. |
| `Log10Consts` | `log 10 = 3 log 2 + log (5/4)` within `2^-89`, the split constants within `2^-86` of `1/log 10` and `log 2/log 10`, and `\|log (1 + f)\| ≥ 2 (1 - 2^-58) \|s\|`. |
| `Log10Kernel` | `kernel10`: the errors of `s`, `hfsq`, and `k_log1p` as multiples of `u σ` for `σ = \|s\|`. |
| `Log10Final` | `tail10`: one step for the arithmetic after `f` and the double of `k`. |
| `Log10Main` | `reduce10` and `main10`: the reduction for an argument word and its composition with `tail10`. |
| `Log10Theorem` | Guards, the normal and subnormal arguments, the exceptional values, the powers of ten, `Ready`, and the byte theorem. |

### Error budget

With `σ = |s| ≤ 0.1716` and `u = 2^-53`, the proof compares each word with its value in exact arithmetic, and each error is a multiple of `u σ` plus a term below `2^-1060`.  `Log10Kernel.kernel10` gives the rows for `s`, `hfsq`, and `r`, and `Log10Final.tail10` the rest.  The terms in `|k|` come from the split constants and stay below `2^-85 |k|`.

| Step | Fact |
|---|---|
| Reduction | `x = 2^k x'` with `x'` from 0.70710 to 1.41422, from the exponent and fraction fields (`Log10Bits.xr_fields`). |
| `f = x' - 1` | exact by Sterbenz's lemma [8], on the grid of `2^-53` |
| `0.5 f`, `hi · ivln10hi`, `y · log10_2hi` | exact products: `hi` has at most 21 significant bits, `ivln10hi` 32, `y` 11, and `log10_2hi` 40 |
| `f - hi`, `y · log10_2hi - w` | exact by Sterbenz's lemma, or a subtraction from 0 |
| `s`, `hfsq`, `r` | within `2.0001 u σ`, `0.50001 u σ`, and `0.6713 u σ` of their exact values |
| polynomial | `log (1 + f)` within `(93/128) 2^-58 σ` of `s (2 + Lg1 s² + …)` (`Log1pKernelPoly.log1p_kernel_error`) |
| `hi + lo` | within `1.2772 u σ` of `s (2 + Lg1 s² + …)` |
| constants | `ivln10hi + ivln10lo` and `log10_2hi + log10_2lo` within `2^-86` of `1/log 10` and `log 2/log 10` |
| sum before the final rounding | within `0.7026 u σ + 2 · 10^-10 u \|k\| + 21 · 2^-1070` of `log10 x` |

The rounded-result lemmas of the other logarithms do not suffice here: near `f = 0.414` and `k = 0` the error before the final rounding is about 0.82 units of the result, beyond the `15/32` that `F64RelativeStepWide` leaves.  [The rounded-step lemma](../../../../LeanExe/ProofKit/F64RoundedStep.lean), `F64RoundedStep.within_one_add`, takes the exact sum of the two words of the final addition, where those lemmas take its rounded result, and gives one step when that sum lies within `(63/64) u |y|` of `y`.  For `k = 0`, `|log10 x| ≥ 2 (1 - 2^-58) σ/2.303 ≥ 0.8684 σ`, so the allowance is about `0.855 u σ` against `0.7026 u σ`.  For `k ≠ 0`, `|log10 x| ≥ 0.1472 |k|`, so the allowance is about `0.145 u |k|` against at most `0.121 u |k|`.  The errors use about 82 and 83 percent of the allowance in the two cases, the margin of about 18 percent that the journal records.

### Shared modules

The proof uses ProofKit modules, including the arithmetic chains that prove Lean's `Float` and `Float32` operations equal to Talos's functions.  The modules specific to the error analysis are [the signed reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean), [the rounded-step lemma](../../../../LeanExe/ProofKit/F64RoundedStep.lean), which this proof added to ProofKit, [the error tracker](../../../../LeanExe/ProofKit/F64ErrorTrack.lean), [the exact subtraction module](../../../../LeanExe/ProofKit/F64Sterbenz.lean), [the high-word module](../../../../LeanExe/ProofKit/F64HighWord.lean), [exact products](../../../../LeanExe/ProofKit/F64ExactProduct.lean), [division bounds](../../../../LeanExe/ProofKit/F64DivBounds.lean), [the kernel-checked polynomial bound](../../../../LeanExe/ProofKit/PolyBound.lean), and [the series of `log (1 + x) - log (1 - x)`](../../../../LeanExe/ProofKit/LogRatioRemainder.lean).  The last rests on Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one` [9].  Each product of two error bounds that shrink with `σ` takes one factor in a form valid for all `σ ≤ 0.1716`, so every bound is linear in `σ`, and `linarith` checks the chain.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| `ivln10hi + ivln10lo` and `log10_2hi + log10_2lo` against `1/lnTenQ` and `S/lnTenQ`, with `lnTenQ = 3 S + log (5/4)` from 20 terms of the series of `atanh (1/9)` and `S` the split of `ln 2` from `ExpReductionBounds` | `Log10Consts.const_checks` |
| Polynomial `2 + Lp1 z + … + Lp7 z^7` against the series on `\|s\| ≤ 0.1716` | `Log1pKernelPoly.log1p_kernel_error`, through `PolyBound.check` |
| Values and bounds of the constants | `Log10Kernel.consts10`, `bounds10`, `Log10Final.consts_tail`, `bounds_tail` |
| `tailWord` at the 22 words of `10^n`, `1 ≤ n ≤ 22`, gives the word of `n` | `Log10Theorem.pow10_checks` |
| Function 3 is exported as `log10`, and the file's bytes equal the encoder's | `Log10Theorem.log10_export`, `Log10File.log10_file` |

### History

[The journal section](../../../../devnotes.md#2026-10-11-log10-theorem-track-log) records the choices that shaped the proof.  An exact-rational Python model of the chain fixed the constants of the error bounds before the Lean proof.  The bound before the final rounding exceeds what the rounded-result lemmas allow, so the proof adds `F64RoundedStep.within_one_add`, which cases over the binades of the sum and of `y` and applies `F64FullStep.one_step_binades` whenever the sum lies within `63/64` units of `y`.  `nlinarith` in the long proof of `tail10` exhausted 8,000,000 heartbeats, and since every bound there is linear, `linarith` checks it.

## Tests

[The accuracy check of `log2` and `log10`](../../../../tests/TestSupport/Numerics/Log2Accuracy.lean) compares `Log10.log10` natively with the double nearest to `log10 x` from [the power reference](../../../../tests/TestSupport/Numerics/PowerReference.lean), which divides [the integer reference](../../../../tests/TestSupport/Numerics/Reference.lean)'s logarithm by `ln 10` at 500 bits, and it fails at the first result more than one step away.  Its 342,219 arguments are 100,001 evenly spaced values from 0 to 20, 100,001 from 0.9 to 1.1, 100,000 hashed positive values over all exponents, 40,000 doubles on both sides of 1 at hashed distances of up to `2^36` units, the five doubles at and around each of 13 edges, among them the words near `√2/2` and `√2` where `k` changes, the 52 subnormal and 2,046 normal powers of two, the 23 powers of ten from 1 to `10^22`, nine special and negative values, and the 22 inputs of `WorstCases.log2` and `WorstCases.log10`.  The ten inputs of `WorstCases.log10` are those that give the largest known `log10` errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [10], whose Table 3 lists 0.814 units for FreeBSD 15.1, OpenLibm, and Musl and 1.62 for GNU libc 2.44 and the Arm Performance Library.

In a run of `tests/verified/run.sh`, all 342,219 results of `log10` lie within one step of the reference, and 1,225 of them differ from it, so the largest measured distance equals the proved bound.  The C library of the test run lies within two steps at the same arguments, with 50,056 results unequal to the reference.  The reference's docstrings state its truncation errors, a relative error below `2^-420` for these logarithms, and no theorem proves them.  Such an error can change the reference only for an exact value within that distance of a midpoint between two doubles, where the reference may name the other double beside the midpoint.

## Limits

The theorem is about Talos's semantics of WebAssembly.  It trusts the Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode`, as [the design notes](../../../../docs/design.md#scope-of-the-theorem) record, and the file theorem trusts the elaborator `binary_file%`, which reads `log10.wasm`.  Talos implements the deterministic profile, in which every NaN result is canonical [6], and an engine outside that profile, such as a browser, may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, and every NaN `Float` has the canonical bits, so the theorem covers only the canonical NaN among the NaN words a WebAssembly caller can pass.  For another NaN word the compiled code returns `x + x` or `(x - x)/0`, both the canonical NaN in Talos, but no theorem states it.  `log10_bytes_accuracy` covers sequences of calls to `log10` only, and a host that calls another export of the module or writes its memory between calls needs a theorem that the action preserves `Ready`.  `log10_pow10` is a statement about the Lean function, and it reaches the compiled module through the byte theorem's equality of the result with `Log10.log10 x`.

## References

1. FreeBSD, [`lib/msun/src/e_log10.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_log10.c).  Copyright (C) 1993 by Sun Microsystems, Inc., with the permission quoted under Implementation.
2. FreeBSD, [`lib/msun/src/k_log.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_log.h), same commit: the method, the polynomial with its stated error, and the stated error of the natural logarithm.
3. FreeBSD, [`lib/msun/src/s_log1p.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_log1p.c), same commit, whose `Lp1` to `Lp7` the `log1p` port holds.
4. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229).  This document cites clause 9.2 with Table 9.1 (the domain of `log10`, correct rounding, NaN operands) and clause 9.2.1 (special values).
5. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.3.8, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
6. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
7. The Mathlib Community, Mathlib, [`Mathlib/Analysis/SpecialFunctions/Log/Base.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Log/Base.lean), `Real.logb b x := log x / log b`.
8. R. P. Brent and P. Zimmermann, [*Modern Computer Arithmetic*](https://arxiv.org/abs/1004.4710), version 0.5.1, 2010, Theorem 3.2.2 (Sterbenz): for floating-point numbers `x` and `y` of the same precision with `y` in `[x/2, 2x]`, `y - x` is exactly representable if there is no underflow.  The book cites P. H. Sterbenz, *Floating-Point Computation*, Prentice Hall, 1974, whose text is not checked here.
9. The Mathlib Community, Mathlib at the same commit, [`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean), `Real.hasSum_log_sub_log_of_abs_lt_one`.
10. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
