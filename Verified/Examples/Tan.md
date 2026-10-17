# The tangent

[The implementation](Tan.lean) exports `tan`, a port of fdlibm's `tan` and `__kernel_tan` as FreeBSD's msun has them [1, 2], with the argument reduction of [the sine and cosine](Trig.md).  The decided bound is one representable step from the nearest-even rounding of the real tangent, `F64SignedRounding.WithinSteps 1`.  `transcendentals` proves the bound for every finite binary64 input and the exceptional values as equalities of bits, and `TanTheorem.tan_bytes_accuracy` carries both to the decoded WebAssembly module, with `TanFile.tan_file` connecting that module to the file `build/verified/tan.wasm`.  No accepted theorem depends on an axiom other than `propext`, `Classical.choice`, and `Quot.sound`, and `tests/verified/run.sh` checks the file theorem against the file it writes.

## Specification

`tan` computes `Real.tan` of the value of its argument.  Mathlib's `Real.tan x` equals `Real.sin x / Real.cos x` (`Real.tan_eq_sin_div_cos`) and is 0 where the cosine vanishes, but no double is an odd multiple of `π/2`, so that value never applies.  Every finite double is in the domain, and the result is finite: `TrigReduce.remPio2_spec`, which rests on `TrigDistance.quadrant_distance`, keeps arguments on the reduction path at least `2^-63` from a multiple of `π/2`, so `-1/tan r` is finite in the odd quadrants.  For finite `x` the bound is `WithinSteps 1 (Real.tan (value x.toBits)) (Tan.tan x).toBits`, with [the signed reference](../../LeanExe/ProofKit/F64SignedRounding.lean) that [the sine and cosine document](Trig.md#specification) describes.

| Input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `+0` | `+0` | IEEE 754-2019 9.2.1 [3]; C99 F.9.1.7 [4] | `tan_pos_zero` |
| `-0` | `-0` | the same | `tan_neg_zero` |
| `±∞` | the canonical NaN | IEEE 754-2019 9.2, Table 9.1 (outside the domain, a quiet NaN); C99 F.9.1.7 | `tan_nonfinite` |
| NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [5] | `tan_nonfinite` |
| finite nonzero `x` with `\|x\| < 2^-27` | `x` | the one-step bound | `tan_within` |

IEEE 754-2019 lists `tan` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [3].  The one-step bound is weaker than correct rounding, and the port is not correctly rounded: the accuracy check finds 4,383 results one step from the nearest double.  The pinned `s_tan.c` states that "TRIG(x) returns trig(x) nearly rounded" [1].  The theorems say nothing about floating-point exceptions, which the port does not compute.

## Algorithm

Above `π/4` the argument is reduced to `x = N π/2 + r`, with `r` returned as the sum `y0 + y1`, by the reduction that [the sine and cosine document](Trig.md#algorithm) describes, and `tan x` is `tan r` for even `N` and `-1/tan r` for odd `N`, as the table in `s_tan.c` lists [1].  On `|y0| < 0.67434`, below the high word `0x3FE59428`, the kernel evaluates `tan (y0 + y1) ≈ y0 + T0 y0³ + ... + T12 y0²⁷ + (1 + y0²) y1`, an odd polynomial of degree 27 with the tail taken to first order [2].  The code computes the terms after `y0` as one correction `c`, the variable `r` of `k_tan.c`, so that the result for even `N` is `y0 + c` rounded.  `k_tan.c` bounds the polynomial's quotient by `y0` within `2^-59.2` of `tan y0 / y0` on `[0, 0.67434]`.  The kernel evaluates the terms from `y0⁵` on as two polynomials in `y0⁴`, one with the coefficients `T1, T3, ..., T11` and one, multiplied by `y0²`, with `T2, T4, ..., T12`.

From `0.67434` to `π/4` the kernel evaluates the polynomial at `y = π/4 - |y0 + y1|`, with `π/4` in two words, and uses `tan (π/4 - y) = (1 - tan y)/(1 + tan y) = 1 - 2 (tan y - tan² y/(1 + tan y))` [2], so the polynomial runs only on `|y| ≤ 0.111`.  With `w = y + c` for the correction `c` at `y`, the code computes `v - 2 (y - (w²/(w + v) - c))`, which equals `T_v (w) = v - 2 w v/(w + v)` in exact arithmetic, and multiplies it by the sign of `y0`.  `v = 1` gives `T_1 (tan y) = tan (π/4 - y)` for even `N`, and `v = -1` gives `T_{-1} (tan y) = -1/tan (π/4 - y)` for odd `N`.  For odd `N` below `0.67434`, the kernel returns `-1/(y0 + c)` computed with a compensation: `w = y0 + c` and `a = -1/w` are truncated to their high 32 bits `z` and `t`, so that `t z` is exact, and the result is `t + a (1 + t z + t d)`, where `z + d = y0 + c`.  `k_tan.c` notes that the plain quotient would allow an error up to two units [2].

## Implementation

The sources are FreeBSD msun's `s_tan.c` (Copyright (C) 1993 by Sun Microsystems, Inc.) and `k_tan.c` (Copyright 2004 Sun Microsystems, Inc.) at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1, 2], each with the notice "Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved".  The module docstring of [the implementation](Tan.lean) names both files and the commit and quotes their notices verbatim, as the notices require.  The port is written in the Verified dialect, the subset of Lean that [the Verified compiler](../README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [Trig.remSmall, Trig.remMedium, Trig.mul64, Trig.clz64, Trig.window, Trig.mulTop, Trig.shiftTop, Trig.remLarge, Trig.remPio2, kernelTan, tanWith, tan]` lists the reduction of [the trigonometric module](Trig.lean), so the reflector compiles those Lean definitions again into this module, and the theorems about `Trig.remPio2` apply to `Tan.tanWith` unchanged.

The module's functions are `alloc` (0), `release` (1), the listed definitions from 2 on, and `tan` (13).  `tan` passes the tables `Trig.invPi` and `Trig.halfPi`, which the module borrows at addresses 4096 and 4264.  [The `π x` functions](Sinpi.lean) list `Tan.kernelTan` in their own module.

| C code | Port | Reason |
|---|---|---|
| `__ieee754_rem_pio2 (x, y)` on signed `x` | `Trig.remPio2 inv half x.abs`, with the result negated for a negative `x` | `tan` is odd.  Every operation of fdlibm's reduction and kernel is odd under rounding to nearest, so the negation gives fdlibm's result for the same reduction, as the module docstring and [the ports section](../../devnotes.md#2026-10-10-ports-of-log1p-atan-atan2-asin-acos-and-tan) of the journal state. |
| `__kernel_rem_pio2` from `2^20 · π/2` on | the Payne–Hanek reduction of `Trig.remLarge` | The shared reduction.  There the reduced argument may differ from fdlibm's in its last bits. |
| `__kernel_tan (x, y, iy)` with `iy = ±1` | `kernelTan x y odd`, with the Boolean `odd` | `odd` is `iy = -1`, read from `n &&& 1` of the count. |
| `(double) (1 - ((hx >> 30) & 2))` | `if hx >>> 31 == 1 then -1.0 else 1.0` | The sign of `x` as `±1`, from the high word as a word. |
| `if ((int) x == 0) return x;` below `2^-27` | `ix < 0x3e400000 && x.toUInt64 == 0` | Both truncations give 0 for every `x` below `2^-27` in magnitude, where the test runs. |
| `SET_LOW_WORD (z, 0)` | `Float.ofBits (w.toBits &&& 0xFFFFFFFF00000000)` | The dialect reads and writes words through `toBits` and `ofBits`. |
| `ix >= 0x3FE59428` as an `int` comparison | `let big : Bool := ix ≥ 0x3FE59428` | Without the annotation `big` binds a proposition, which the reflector rejects. |

| Constant | Bits | Value |
|---|---|---|
| `T0` to `T6` | `0x3FD5555555555563`, `0x3FC111111110FE7A`, `0x3FABA1BA1BB341FE`, `0x3F9664F48406D637`, `0x3F8226E3E96E8493`, `0x3F6D6D22C9560328`, `0x3F57DBC8FEE08315` | the kernel's coefficients |
| `T7` to `T12` | `0x3F4344D8F2F26501`, `0x3F3026F71A8D1068`, `0x3F147E88A03792A6`, `0x3F12B80F32F0A7E9`, `0xBEF375CBDB605373`, `0x3EFB2A7074BF7AD4` | the kernel's coefficients |
| `pio4`, `pio4lo` | `0x3FE921FB54442D18`, `0x3C81A62633145C07` | `π/4` rounded, and the rounded remainder |

Each of the 16 decimal values in `k_tan.c` rounds to the word printed beside it, and the 15 words written as `Float.ofBits` in `Tan.lean` are among those words.  The journal records the same check for all 77 annotated constants of the `log1p`, `atan`, `atan2`, `asin`, `acos`, and `tan` sources ([the ports section](../../devnotes.md#2026-10-10-ports-of-log1p-atan-atan2-asin-acos-and-tan)).  Against `π` from Machin's formula at 1,600 bits, `pio4` is `π/4` rounded to nearest and `pio4lo` is the remainder rounded to nearest, so the pair lies within `2^-110` of `π/4`, and the proof uses the weaker `2^-68` that `TanBigWords.pi_close` derives from Mathlib's bounds on `π`.  `TanKernelPoly` restates `T0` to `T12` as `PolyBound.ratOfWord` of the same words, and `k_tan.c` at the pinned commit has a SHA-256 beginning `0021bc1b`, the hash that [the polynomial section](../../devnotes.md#2026-10-10-kernel-polynomials-of-stage-3-track-poly) of the journal records for its copy.

## Theorems

The theorems are in [the tangent theorem module](TanTheorem.lean), [the accuracy module](TanWith.lean), and [the file module](TanFile.lean).  `x` is a Lean `Float`, `value x.toBits` its real value, and a word is the `UInt64` bit pattern of a double.  The byte theorem uses `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `TanWith.tan_within` | For finite `x`, `WithinSteps 1 (Real.tan (value x.toBits)) (Tan.tan x).toBits`. |
| `TanTheorem.tan_pos_zero`, `tan_neg_zero` | `tan (+0)` has the bits `0` and `tan (-0)` the bits `0x8000000000000000`. |
| `tan_nonfinite` | For an infinity or a NaN, the result has the bits `Wasm.IEEE64.canonicalNaN`. |
| `ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant, `Trig.invPi` borrowed at 4096, `Trig.halfPi` at 4264, and a memory cap of at most 65,535 pages. |
| `tan_entry_call` | A call of function 13 from a `Ready` store returns, without a trap, the bits of `Tan.tan x`, and leaves a `Ready` store in which every heap region keeps its bytes. |
| `tan_export` | Function 13 is exported as `tan`. |
| `tan_bytes_accuracy` | `Tan.compiled.module` encodes to bytes that decode to it, exports function 13 as `tan`, starts in a `Ready` store, and every call from a `Ready` store returns the bits of `Tan.tan x`, within one step for finite `x`, and leaves a `Ready` store.  The statement covers every call in a sequence of calls to `tan`. |
| `TanFile.tan_file` | `build/verified/tan.wasm` holds `encode Tan.compiled.module`. |
| `tan_file_decode` | The file decodes to the module of `tan_bytes_accuracy`, whose bytes it uses, so its axiom report covers that theorem. |

Each proof module has `#print axioms` lines for its results.  The builds that accepted the proof are `tan-odd-9.log`, `tan-oddstep-1.log`, `tan-big-1.log` to `tan-big-7.log`, `tan-with-1.log`, `tan-theorem-2.log`, and `tan-file-1.log` under `build/transcendentals/` in a separate worktree on the build host ([the theorem section](../../devnotes.md#2026-10-11-the-tan-theorem-track-trig)).  The integration build `opus-merge-tan-1.log` under `build/transcendentals/` in the primary checkout, a separate checkout on the build host, completed 9,426 jobs and printed the three axioms for `tan_within` and `tan_bytes_accuracy` ([the integration](../../devnotes.md#2026-10-12-integration-of-tan-the-bessel-foundations-and-the-gamma-and-bessel-ports)).

[The root `Verified` import](../../Verified.lean) includes `TanTheorem`, so `lake build Verified` checks the proof.  `tests/verified/run.sh` writes `build/verified/tan.wasm`, builds `Verified.Examples.TanTheorem`, checks `TanFile.lean` against the file through its entry `tan:TanTheorem:TanFile`, and fails unless both file theorems report exactly the three permitted axioms.  The recorded run in the primary checkout, `opus-verified-tests-14.log` of 2026-10-11, printed the three axioms for `tan_within` and every declaration of `TanTheorem` and passed the file check of `tan.wasm`.

## Proof

### Modules

The proof adds 16 modules in `Verified/Examples/` to the chain of [the sine and cosine proof](Trig.md#modules), and `TanFile` holds the file theorems.  From that chain it takes the reduction (`TrigReduce.remPio2_spec`), the final step for tiny inputs (`F64SelfStep.self_step`), the error tracking (`TrigApprox`), the exact sums (`F64SignedNearestSum`, `F64ValueExact`), and the facts about high words (`TrigSinCos`, `TrigTheorem`).  The table lists the modules by stage, in dependency order within each stage.  `TanWith` imports `TrigTheorem`, so building `Verified.Examples.TanTheorem` builds the whole trigonometric chain as well.

| Stage | Modules | Content |
|---|---|---|
| Kernel on words | `TanWords` | `kernelTan` as `smallW` below `0x3FE59428` and `bigW` from it on. |
| Polynomial | `TanKernelPoly`, `TanPoly`, `TanMath` | The polynomial against `tan`, the rounding error of the correction `c`, and the real facts: `cos ≥ 0.76` on `\|x\| ≤ 0.6745`, and the kernel's first-order tail. |
| Final steps | `TanStep` | `near_bin` and `near_rel`, for a word nearest to a real `t` close to `T`. |
| Even path | `TanTrunc`, `TanEven` | The truncation to 32 high bits, Sterbenz's lemma, and `even_within`. |
| Odd path | `TanComp`, `TanOdd`, `TanOddStep` | The compensated reciprocal in real numbers, `odd_spec`, and `odd_within`. |
| Path from `0.67434` | `TanBigReal`, `TanBigWords`, `TanBigClose`, `TanBigStep` | The real error of the final expression (`big_real`), the argument `π/4 - \|y0 + y1\|` and the chain of operations (`arg_spec`, `chain_spec`), the identities of `T_v (y) = v - 2 y v/(y + v)`, and `big_within`. |
| Assembly | `TanWith`, `TanTheorem` | `tan_quadrant`, `reduced_tan`, `tan_within`, and the byte theorem. |

### Error budget

Let `u = 2^-53`, `η = 2^-1075`, and `X = |y0|`.  `TanKernelPoly.tan_kernel_error` bounds the polynomial against `tan x` by `(59/64) · 2^-59 |x|` on `|x| ≤ 0.67434`, above the `2^-59.2` of `k_tan.c`, since the largest sampled error is `2^-59.147` at `x ≈ 0.670` ([the polynomial section](../../devnotes.md#2026-10-10-kernel-polynomials-of-stage-3-track-poly)).  The check is weighted: with `S` and `C` the Taylor polynomials of `sin x / x` and `cos x`, sixteen kernel-checked pieces bound `S - C P` by `ε C`, and the remainders of `sin` and `cos` and the bound `cos x ≥ 0.76` complete it.  A plain bound on `S - C P` divided by the smallest cosine would lose about 0.36 bits, as the same section records.  `TanPoly.corr_AB` bounds the rounding error of the correction `c` by `u (1.336 X³ + 1.8 X⁵) + u² (12 X³ + 6 X) + 9 η`.

The final steps use the error of a real `t` to which the result is a nearest word.  `TanStep.near_bin` accepts `t` less than one spacing from `T` when both lie in one binade, since two reals less than a spacing apart round to words at most one step apart, and `near_rel` accepts `|t - T| ≤ 0.74 u |T|` across binade boundaries.  The kernel lemmas accept a reduction error up to `|r|/2^59`, twice the `|r|/2^60` that `Reduced` provides.

| Inputs | Path | Bound on `t` | Allowance | Theorem |
|---|---|---|---|---|
| `0 < \|x\| < 2^-27` | the result is `x` | `\|tan x - x\| ≤ \|x\|³` | `2^-54` relative to the word | `TanWith.tiny_tan` through `F64SelfStep.self_step` |
| even `N` or no reduction, `X < 0.4643` | `y0 + c` | `0.6 u X` (`TanOddStep.even_err_odd`) | `0.74 u \|tan r\|` | `TanEven.even_within` through `near_rel` |
| even `N` or no reduction, `0.4643 ≤ X < 0.67434` | `y0 + c` | at most `0.9397 u` (`TanOddStep.err_b4`), below one spacing of `[1/2, 1)` | one spacing, `u` | `TanEven.even_within` through `near_bin` |
| odd `N`, `X < 0.4643` | the compensated reciprocal | within the allowance, from `even_err ≤ 0.6 u X` and `odd_spec` | `0.74 u \|tan r\|^-1` | `TanOddStep.odd_within` through `near_rel` |
| odd `N`, `0.4643 ≤ X < 0.67434` | the compensated reciprocal | at most 0.90 of a spacing of `[1, 2)`, on four intervals with lower bounds on `tan` from `Real.sin_bound` and `Real.cos_bound` | one spacing, `2u` | `TanOddStep.odd_within` through `near_bin` |
| `0.6743 ≤ X ≤ 0.78541`, `\|y\| ≥ 0.05` | `±(v - 2 (y - (w²/(w + v) - c)))` | below `0.95 u`, with `T` in `[0.79, 0.91]` or `[-1.27, -1.09]` | one spacing, `u` for even `N` and `2u` for odd `N` | `TanBigStep.big_within` through `near_bin` |
| `0.6743 ≤ X ≤ 0.78541`, `\|y\| < 0.05` | the same | below `0.45 u` with `\|T\| ≥ 0.9` | `0.74 u \|T\|` | `TanBigStep.big_within` through `near_rel` |

`TanOdd.odd_spec` shows that the compensated reciprocal is a nearest word to a real `τ` within `u/(2^11 |W|)` of `-1/W` for `W = y0 + c`: the truncated heads have 21 significant bits, so `t z` is exact, and the other roundings act on quantities of size `2^-17`.  On the path from `0.67434`, `TanBigWords.arg_spec` places the argument `y` within `u |P - |y0 + y1|| + 2^-100` of `P - |y0 + y1|`, where the two words `P` lie within `2^-68` of `π/4` by Mathlib's `Real.pi_gt_d20` and `Real.pi_lt_d20` [6], and the first difference is exact by Sterbenz's lemma.  `TanBigReal.big_real` bounds the computed value within `2.4 u |y| + 4 η` of `W v/(W + v)`, and `TanBigClose.tan_quarter` proves `T_1 (tan b) = tan (π/4 - b)` and `T_{-1} (tan b) = -1/tan (π/4 - b)`, against which `big_close_hi` and `big_close_lo` bound the result.  `TanWith.tan_quadrant` turns `tan r` or `-1/tan r` into `tan |x|` by the parity of `N`, and the result is negated for a negative `x`.

The tightest margins are 5 percent on the path from `0.67434` with even `N`, where `0.95 u` meets a spacing of `u`, 6 percent on the even path below it, where `even_err`, which `TanOddStep.even_err_le` shows increasing, reaches at most `0.9397 u` at `0.67434`, and 10 percent on the odd path, where the largest ratio is 0.90 ([the theorem section](../../devnotes.md#2026-10-11-the-tan-theorem-track-trig)).  On the paths that use `near_rel`, the even path's `0.6 u X` leaves 19 percent of `0.74 u |tan r|`, and the bound `0.45 u` with `|T| ≥ 0.9` stays below `0.5 u |T|`, 32 percent under the allowance.  `TanOddStep.odd_rel` proves the odd path within `0.74 u |tan r|^-1` and states no smaller bound, and the tiny path's bound `|x|³` stays below the allowance `2^-54 |x|` with a margin that vanishes as `|x|` approaches `2^-27`.

### Shared modules

The proof reuses [the sine and cosine proof](Trig.md#shared-modules) and [checks on adjacent intervals and weighted bounds](../../LeanExe/ProofKit/PolyChecks.lean).  The tangent modules import `PolyChecks`, [division bounds](../../LeanExe/ProofKit/F64DivBounds.lean), [exact products](../../LeanExe/ProofKit/F64ExactProduct.lean), [conversions between words and floats](../../LeanExe/ProofKit/F64Convert.lean), [Taylor remainders](../../LeanExe/ProofKit/TaylorRemainder.lean), and [borrowed tables kept across calls](../../LeanExe/ProofKit/BorrowedKept.lean) directly, and the rest through the trigonometric chain.

`PolyChecks.Covers` states a check as a conjunction over adjacent intervals, each its own declaration, because the kernel keeps every intermediate result of a declaration.  On the `atan` kernel, one `decide +kernel` over the whole interval ran for more than four and a half minutes and reached 5.7 GB under the runner's 6 GiB limit before it was stopped ([the polynomial section](../../devnotes.md#2026-10-10-kernel-polynomials-of-stage-3-track-poly)).  `TanKernelPoly`, with its sixteen pieces as separate declarations, built in 53 seconds.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| The weighted polynomial bound, in eight upper and eight lower pieces over `x²` in `[0, 59603/131072]`, with bisection to depth 18 | `TanKernelPoly.tan_up_1` to `tan_up_8`, `tan_lo_1` to `tan_lo_8`, `tan_up_covers`, `tan_lo_covers` |
| The kernel polynomial in `x²` within 1/4 of 1 on the same range | `TanKernelPoly.tan_range` |
| Bounds on the rational values of `T0` to `T12` | `TanPoly.coeffs_checked` |
| The words `pio4` and `pio4lo` and the thresholds `0x3E400000` and `0x3FE59428` as rationals | `TanBigWords.value_pio4`, `value_pio4lo`, `TanWith.thresholds` |
| Function 13 is exported as `tan` | `TanTheorem.tan_export` |
| The file's bytes equal the encoder's | `TanFile.tan_file` |

The reduction's kernel-checked facts are those of [the sine and cosine proof](Trig.md#kernel-checked-facts): the 1,025 distance certificates, the windows of `2/π`, and the pieces of `π/2`.  The tangent proof adds no table.  The only constant it compares with `π` is `π/4`, whose two words it bounds with Mathlib's decimal bounds on `π` [6].

### History

The first build of `TanOdd` held the build host's Lean lock for 26 minutes at the 4 GB memory limit before it was stopped ([the kernel section](../../devnotes.md#2026-10-11-the-tan-kernel-track-trig)).  Probes located the cause in one declaration, `smallW_odd : smallW x y true = oddW x (corrW x y) := rfl`, whose definitional check unfolded `Wasm.IEEE64.add` and the other operations and passed 3 GB in 16 seconds.  `simp only` with the definitions proves the same equation in 6 seconds, and the proof of `odd_spec` is split into one lemma per rounding step, so the module builds in about 20 seconds with 0.55 GB of anonymous memory (`tan-odd-9.log`).  The journal and the plan's notes on resuming the work require equations between definitions built from IEEE operations to be proved with `simp only`, never with `rfl`.

## Tests

[The accuracy check](TanAccuracy.lean) compares `Tan.tan` natively with the double nearest to `tan x`, the quotient of the sine and cosine of [the integer reference](Reference.lean), and it fails at the first result more than one step away.  Its 180,059 arguments are those of [the sine and cosine check](TrigAccuracy.lean) without that check's worst inputs of `sin` and `cos`: 100,000 hashed values with exponents from `2^-30` to `2^1023` and both signs, 20,001 evenly spaced values from 0 to 100, the 60,000 doubles at and next to the rounded `k · π/2` for `k` from 1 to 20,000, where `tan` has its zeros and poles, and five hard arguments and their negatives.  To these it adds the five doubles at and around each of the six thresholds `±0x3FE59428`, `±0x3FE921FB`, and `±0x3E400000`, nine special values, and the nine inputs of `WorstCases.tan`.  Those nine are the double-precision inputs that give the largest known `tan` errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [7], whose Table 3 lists 1.02 units for FreeBSD 15.1, Newlib, OpenLibm, and Musl and 0.619 for GNU libc 2.44.

In `opus-verified-tests-14.log` all 180,059 results lie within one step of the reference, and 4,383 of them differ from it, so the largest measured distance equals the proved bound.  The C library on the build host lies within 14 steps, with 301 results unequal to the reference.  The journal traces the 14 steps to glibc 2.41's `tan` at `6381956970095103 · 2^797`, 14.4 units from a 900-bit integer computation, where the port agrees with the reference ([Zimmermann's inputs in the checks](../../devnotes.md#2026-10-11-zimmermanns-inputs-in-the-accuracy-checks), [the ports section](../../devnotes.md#2026-10-10-ports-of-log1p-atan-atan2-asin-acos-and-tan)).  The check's docstring states that the reference's sine and cosine lie within a relative `2^-231` of their values and that the truncated quotient adds less than `2^-238`, and these bounds are not proved.

## Limits

The limits of [the sine and cosine theorems](Trig.md#limits) apply to the tangent.  The theorems are about Talos's semantics of WebAssembly: the Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode` are trusted, as [the design notes](../../docs/design.md#scope-of-the-theorem) record, and the file theorem trusts the elaborator `binary_file%`, which reads `tan.wasm`.  Talos implements the deterministic profile, in which every NaN result is canonical [5], and an engine outside that profile may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, and every NaN `Float` has the canonical bits (`F64Bits.toBits_canonical`), so the theorems cover only the canonical NaN among the NaN words a WebAssembly caller can pass.  For another NaN word the compiled code reaches `x - x`, which returns the canonical NaN in Talos, but no theorem states it.  The byte theorem covers sequences of calls to `tan` only: the module also exports `alloc`, `release`, the reduction functions, `kernelTan`, `tanWith`, its memory, and the allocation counters, and a host that calls another export or writes the tables between calls needs a theorem that the action preserves `Ready`.

## References

1. FreeBSD, msun, [`lib/msun/src/s_tan.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_tan.c), commit `20381bce4b63975494a2f4bc84257f6932e6d379`.  Copyright (C) 1993 by Sun Microsystems, Inc., with the notice quoted above.
2. FreeBSD, msun, [`k_tan.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_tan.c), same commit.  Copyright 2004 Sun Microsystems, Inc., with the same notice.  It states the polynomial's error bound `2^-59.2` and the method from `0.67434` on.
3. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clause 9.2 with Table 9.1 (domains and exceptions) and clause 9.2.1 (special values).
4. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.1.7, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
5. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
6. The Mathlib Community, Mathlib at commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`, [`Mathlib/Analysis/Real/Pi/Bounds.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/Real/Pi/Bounds.lean), `Real.pi_gt_d20` and `Real.pi_lt_d20`.
7. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
