# The tangent

[The implementation](Tan.lean) exports `tan`, a port of fdlibm's `tan` and `__kernel_tan` as FreeBSD's msun has them [1, 2], with the argument reduction of [the sine and cosine](Trig.md).  The decided bound is one representable step from the nearest-even rounding of the real tangent, `F64SignedRounding.WithinSteps 1`.  The bound is proved for every finite binary64 input, the exceptional values are proved exactly, and `TanTheorem.tan_bytes_accuracy` carries both to the decoded WebAssembly module, with `TanFile.tan_file` connecting that module to the file `build/verified/tan.wasm`.  Every accepted theorem reports only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  The theorem is merged into `transcendentals` (commit `e2a9d5a2`), but at commit `77ce56f4` neither `tests/verified/run.sh` nor [the root `Verified` import](../../Verified.lean) checks it, as the section on theorems explains.

## Specification

`tan` computes `Real.tan` of the value of its argument, which Mathlib defines as `Real.sin x / Real.cos x`.  Every finite double is in the domain: no double is an odd multiple of `π/2`, so Mathlib's value 0 at those points never applies, and `TrigDistance.quadrant_distance` keeps every reduced argument at least `2^-63` from 0, so the result is finite.  The bound is `WithinSteps 1 (Real.tan (value x.toBits)) (Tan.tan x).toBits` for finite `x`, with [the signed reference](../../LeanExe/ProofKit/F64SignedRounding.lean) that [the sine and cosine document](Trig.md#specification) describes.

| Input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `+0` | `+0` | IEEE 754-2019 9.2.1 [3]; C99 F.9.1.7 [4] | `tan_pos_zero` |
| `-0` | `-0` | the same | `tan_neg_zero` |
| `±∞` | the canonical NaN | IEEE 754-2019 9.2, Table 9.1 (outside the domain, a quiet NaN); C99 F.9.1.7 | `tan_nonfinite` |
| NaN | the canonical NaN | IEEE 754-2019 9.2; C99 F.9 paragraph 11; the deterministic profile of WebAssembly [5] | `tan_nonfinite` |
| finite nonzero `x` with `\|x\| < 2^-27` | `x` | the one-step bound | `tan_within` |

IEEE 754-2019 lists `tan` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [3].  The one-step bound is weaker than correct rounding, and the port is not correctly rounded.  The pinned `s_tan.c` states that "TRIG(x) returns trig(x) nearly rounded" [1], and the theorems say nothing about floating-point exceptions, which the port does not compute.

## Algorithm

Above `π/4` the argument is reduced to `x = N π/2 + r` with `r = y0 + y1`, by the reduction that [the sine and cosine document](Trig.md#algorithm) describes, and `tan x = tan r` for even `N` and `-1/tan r` for odd `N`.  On `|y0| < 0.67434` the kernel evaluates `tan (y0 + y1) ≈ y0 + T0 y0³ + ... + T12 y0²⁷ + (1 + y0²) y1`, an odd minimax polynomial of degree 27 with the tail taken to first order [2].  `k_tan.c` bounds the polynomial's quotient by `y0` within `2^-59.2` of `tan y0 / y0` on `[0, 0.67434]`.  The kernel evaluates the terms from `y0⁵` on as two polynomials in `y0⁴`, one with the coefficients `T1, T3, ..., T11` and one, multiplied by `y0²`, with `T2, T4, ..., T12`.

From `0.67434` to `π/4` the kernel evaluates the polynomial at `y = π/4 - |y0 + y1|`, with `π/4` in two words, and uses `tan (π/4 - y) = (1 - tan y)/(1 + tan y) = 1 - 2 (tan y - tan² y/(1 + tan y))`, so the polynomial runs only on `|y| ≤ 0.111`.  For odd `N` below `0.67434`, the kernel returns `-1/(x + r)` computed with its correction: `w = x + r` and `a = -1/w` are truncated to their high 32 bits `z` and `t`, so that `t z` is exact, and the result is `t + a (1 + t z + t v)`, where `z + v = x + r`.  `k_tan.c` notes that the plain quotient would allow an error up to two units [2].

## Implementation

The sources are FreeBSD msun's `s_tan.c` (Copyright (C) 1993 by Sun Microsystems, Inc.) and `k_tan.c` (Copyright 2004 Sun Microsystems, Inc.) at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1, 2], with the notice "Permission to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved", which the module docstring of [the implementation](Tan.lean) cites.  The port is written in the Verified dialect, the subset of Lean that [the Verified compiler](../README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [Trig.remSmall, Trig.remMedium, Trig.mul64, Trig.clz64, Trig.window, Trig.mulTop, Trig.shiftTop, Trig.remLarge, Trig.remPio2, kernelTan, tanWith, tan]` lists the reduction of [the trigonometric module](Trig.lean), so the reflector compiles those Lean definitions again into this module, and the theorems about `Trig.remPio2` apply to `Tan.tanWith` unchanged.

The module's functions are `alloc` (0), `release` (1), the listed definitions from 2 on, and `tan` (13).  `tan` passes the tables `Trig.invPi` and `Trig.halfPi`, which the module borrows at addresses 4096 and 4264.  [The `π x` functions](Sinpi.lean) list `Tan.kernelTan` in their own module.

| C code | Port | Reason |
|---|---|---|
| `__ieee754_rem_pio2 (x, y)` on signed `x` | `Trig.remPio2 inv half x.abs`, with the result negated for a negative `x` | `tan` is odd.  The ports track's audit records that every operation of fdlibm's reduction and kernel is odd under rounding to nearest, so the negation gives fdlibm's result for the same reduction. |
| `__kernel_rem_pio2` from `2^20 · π/2` on | the Payne–Hanek reduction of `Trig.remLarge` | The shared reduction.  There the reduced argument may differ from fdlibm's in its last bits. |
| `__kernel_tan (x, y, iy)` with `iy = ±1` | `kernelTan x y odd`, with the Boolean `odd` | `odd` is `iy = -1`, read from `n &&& 1` of the count. |
| `(double) (1 - ((hx >> 30) & 2))` | `if hx >>> 31 == 1 then -1.0 else 1.0` | The sign of `x` as `±1`, from the high word as a word. |
| `if ((int) x == 0) return x;` below `2^-27` | `ix < 0x3e400000 && x.toUInt64 == 0` | Both truncations give 0 for every `x` below `2^-27` in magnitude, where the test runs. |
| `SET_LOW_WORD (z, 0)` | `Float.ofBits (w.toBits &&& 0xFFFFFFFF00000000)` | The dialect reads and writes words through `toBits` and `ofBits`. |
| `ix >= 0x3FE59428` as an `int` comparison | `let big : Bool := ix ≥ 0x3FE59428` | The reflector rejects a binding of a proposition. |

| Constant | Bits | Value |
|---|---|---|
| `T0` to `T6` | `0x3FD5555555555563`, `0x3FC111111110FE7A`, `0x3FABA1BA1BB341FE`, `0x3F9664F48406D637`, `0x3F8226E3E96E8493`, `0x3F6D6D22C9560328`, `0x3F57DBC8FEE08315` | the kernel's coefficients |
| `T7` to `T12` | `0x3F4344D8F2F26501`, `0x3F3026F71A8D1068`, `0x3F147E88A03792A6`, `0x3F12B80F32F0A7E9`, `0xBEF375CBDB605373`, `0x3EFB2A7074BF7AD4` | the kernel's coefficients |
| `pio4`, `pio4lo` | `0x3FE921FB54442D18`, `0x3C81A62633145C07` | `π/4` rounded, and the rounded remainder |

For this document a script compared the port with `k_tan.c`.  The 15 words written as `Float.ofBits` in `Tan.lean` are words that `k_tan.c` prints beside its decimal values, every decimal value in the file rounds to its printed word, and `pio4` is `π/4` rounded to nearest against a 1,500-bit `π`.  The SHA-256 of the fetched `k_tan.c` begins with `0021bc1b`, as the polynomial track recorded.

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

Each module has `#print axioms` lines, and the journal records that every result reports only `propext`, `Classical.choice`, and `Quot.sound`.  The track's builds are `tan-odd-9.log`, `tan-oddstep-1.log`, `tan-big-1.log` to `tan-big-7.log`, `tan-with-1.log`, `tan-theorem-2.log`, and `tan-file-1.log` in its worktree ([the theorem section](../../devnotes.md#2026-10-11-the-tan-theorem-track-trig)).  The integration build `opus-merge-tan-1.log` in the primary checkout on minideb1 completed 9,426 jobs and printed the three axioms for `tan_bytes_accuracy`.

The journal gives the `tests/verified/run.sh` entry as `tan:TanTheorem:TanFile`, but the committed `run.sh` at `77ce56f4` has no such entry, and the committed `Verified.lean` imports `Tan` without `TanTheorem`.  The primary checkout on minideb1 holds both changes, uncommitted, in its working tree.  Its latest run, `opus-verified-tests-13.log` of 2026-10-11, used that working tree: it built `Verified.Examples.TanTheorem`, printed the three axioms for `tan_within` and `tan_bytes_accuracy`, and passed the file check of `tan.wasm`.  Until those changes are committed, a run of the committed `run.sh` does not check `TanFile`.

## Proof

### Modules

The proof adds 16 modules in `Verified/Examples/` to the chain of [the sine and cosine proof](Trig.md#modules), from which it takes the reduction (`TrigReduce.remPio2_spec`), the final steps for tiny inputs (`TrigTiny.self_step`), the error tracking (`TrigApprox`), the exact sums (`TrigNearest`, `TrigFloatTools`), and the facts about high words (`TrigSinCos`, `TrigTheorem`).  The table lists the modules by stage, in dependency order within each stage.  `TanWith` imports `TrigTheorem`, so building `Verified.Examples.TanTheorem` builds the whole trigonometric chain as well.

| Stage | Modules | Content |
|---|---|---|
| Kernel on words | `TanWords` | `kernelTan` as `smallW` below `0x3FE59428` and `bigW` from it on. |
| Polynomial | `TanKernelPoly`, `TanPoly`, `TanMath` | The polynomial against `tan`, the rounding error of the correction `r`, and the real facts: `cos ≥ 0.76` on `\|x\| ≤ 0.6745`, and the kernel's first-order tail. |
| Final steps | `TanStep` | `near_bin` and `near_rel`, for a word nearest to a real `t` close to `T`. |
| Even path | `TanTrunc`, `TanEven` | The truncation to 32 high bits, Sterbenz's lemma, and `even_within`. |
| Odd path | `TanComp`, `TanOdd`, `TanOddStep` | The compensated reciprocal in real numbers, `odd_spec`, and `odd_within`. |
| Path from `0.67434` | `TanBigReal`, `TanBigWords`, `TanBigClose`, `TanBigStep` | The argument `π/4 - \|y0 + y1\|`, the chain of operations, the identities of `T_v (y) = v - 2 y v/(y + v)`, and `big_within`. |
| Assembly | `TanWith`, `TanTheorem` | `tan_quadrant`, `reduced_tan`, `tan_within`, and the byte theorem. |

### Error budget

Let `u = 2^-53`, `η = 2^-1075`, and `X = |y0|`.  `TanKernelPoly.tan_kernel_error` bounds the polynomial against `tan x` by `(59/64) · 2^-59 |x|` on `|x| ≤ 0.67434`, above the `2^-59.2` of `k_tan.c`, since the largest sampled error is `2^-59.147` at `x ≈ 0.670` ([the polynomial track](../../devnotes.md#2026-10-10-kernel-polynomials-of-stage-3-track-poly-minideb2)).  The check is weighted: with `S` and `C` the Taylor polynomials of `sin x / x` and `cos x`, sixteen kernel-checked pieces bound `S - C P` by `ε C`, and the remainders of `sin` and `cos` and the bound `cos x ≥ 0.76` complete it.  `TanPoly.corr_AB` bounds the rounding error of the correction `r` by `u (1.336 X³ + 1.8 X⁵) + u² (12 X³ + 6 X) + 9 η`.

The final steps use the error of a real `t` to which the result is a nearest word.  `TanStep.near_bin` accepts `t` less than one spacing from `T` when both lie in one binade, since two reals less than a spacing apart round to words at most one step apart, and `near_rel` accepts `|t - T| ≤ 0.74 u |T|` across binade boundaries.  The kernel lemmas accept a reduction error up to `|r|/2^59`, twice the `|r|/2^60` that `Reduced` provides.

| Inputs | Path | Bound on `t` | Allowance | Theorem |
|---|---|---|---|---|
| `0 < \|x\| < 2^-27` | the result is `x` | `\|tan x - x\| ≤ \|x\|³` | `2^-54` relative to the word | `TanWith.tiny_tan` through `TrigTiny.self_step` |
| even `N` or no reduction, `X < 0.4643` | `x + r` | within the allowance | `0.74 u \|tan r\|` | `TanEven.even_within` through `near_rel` |
| even `N` or no reduction, `0.4643 ≤ X < 0.67434` | `x + r` | below one spacing of `[1/2, 1)` | one spacing | `TanEven.even_within` through `near_bin` |
| odd `N`, `X < 0.4643` | the compensated reciprocal | within the allowance, from `even_err ≤ 0.6 u X` and `odd_spec` | `0.74 u \|tan r\|^-1` | `TanOddStep.odd_within` through `near_rel` |
| odd `N`, `0.4643 ≤ X < 0.67434` | the compensated reciprocal | at most 0.90 of a spacing of `[1, 2)`, on four intervals with lower bounds on `tan` from `Real.sin_bound` and `Real.cos_bound` | one spacing | `TanOddStep.odd_within` through `near_bin` |
| `0.6743 ≤ X ≤ 0.78541`, `\|y\| ≥ 0.05` | `±(v - 2 (y - (w²/(w + v) - r)))` | below `0.95 u`, with `T` in `[0.79, 0.91]` or `[-1.27, -1.09]` | one spacing, `u` for even `N` and `2u` for odd `N` | `TanBigStep.big_within` through `near_bin` |
| `0.6743 ≤ X ≤ 0.78541`, `\|y\| < 0.05` | the same | below `0.45 u` with `\|T\| ≥ 0.9` | `0.74 u \|T\|` | `TanBigStep.big_within` through `near_rel` |

`TanOdd.odd_spec` shows that the compensated reciprocal is a nearest word to a real `τ` within `u/(2^11 |W|)` of `-1/W` for `W = x + r`: the truncated heads have 21 significant bits, so `t z` is exact, and the other roundings act on quantities of size `2^-17`.  On the path from `0.67434`, `TanBigWords.arg_spec` places the argument `y` within `u |y|` and `2^-100` of `P - |y0 + y1|`, where the two words `P` lie within `2^-68` of `π/4` by Mathlib's `Real.pi_gt_d20` and `Real.pi_lt_d20` [6], and the first difference is exact by Sterbenz's lemma.  `TanBigReal.big_real` bounds the computed value within `2.4 u |y| + 4 η` of `W v/(W + v)`, and `TanBigClose` proves `T_1 (tan b) = tan (π/4 - b)` and `T_{-1} (tan b) = -1/tan (π/4 - b)` and bounds the result against them.  `TanWith.tan_quadrant` turns `tan r` or `-1/tan r` into `tan |x|` by the parity of `N`, and the result is negated for a negative `x`.

The tightest margins are 5 percent on the path from `0.67434` with even `N`, where `0.95 u` meets a spacing of `u`, and 10 percent on the odd path, where the largest ratio is 0.90.  The path from `0.67434` covers reduced arguments up to `0.78541`, since the reduction allows `|y0|` that far.  The margins on the paths that use `near_rel` are not stated in the journal or the sources, and this document does not estimate them.

### Shared modules

The proof imports 97 ProofKit modules, those of [the sine and cosine proof](Trig.md#shared-modules) and [checks on adjacent intervals and weighted bounds](../../LeanExe/ProofKit/PolyChecks.lean), [nearest rounding against relative errors](../../LeanExe/ProofKit/F64NearestRelative.lean), [nearest quotients](../../LeanExe/ProofKit/F64NearestDiv.lean), and [division bounds](../../LeanExe/ProofKit/F64DivBounds.lean).  `PolyChecks.Covers` states a check as a conjunction over adjacent intervals, each its own declaration, because one `decide +kernel` over a whole interval keeps every intermediate result, and on the `atan` kernel it reached 5.7 GB under the runner's 6 GiB limit before it was stopped.  `TanKernelPoly`, with its sixteen pieces as separate declarations, built in 53 seconds.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| The weighted polynomial bound, in eight upper and eight lower pieces over `x²` in `[0, 59603/131072]`, with bisection to depth 18 | `TanKernelPoly.tan_up_1` to `tan_up_8`, the lower pieces, `tan_up_covers`, `tan_lo_covers` |
| Function 13 is exported as `tan` | `TanTheorem.tan_export` |
| The file's bytes equal the encoder's | `TanFile.tan_file` |

The reduction's kernel-checked facts are those of [the sine and cosine proof](Trig.md#kernel-checked-facts).  They include the 1,025 distance certificates, the windows of `2/π`, and the pieces of `π/2`.  The tangent proof adds no table, and the only constant it compares with `π` is `π/4`, whose two words it bounds with Mathlib's decimal bounds on `π`.

### History

The first build of `TanOdd` held minideb1's Lean slot for 26 minutes at the 4 GB memory limit ([the kernel section](../../devnotes.md#2026-10-11-the-tan-kernel-track-trig)).  Probes located the cause in one declaration, `smallW_odd : smallW x y true = oddW x (corrW x y) := rfl`, whose definitional check unfolded `Wasm.IEEE64.add` and the other operations and passed 3 GB in 16 seconds.  `simp only` with the definitions proves the same equation in 6 seconds, and the proof of `odd_spec` is split into one lemma per rounding step, so the module now builds in about 20 seconds with 0.55 GB of anonymous memory.  The rule since then is to prove equations between definitions built from IEEE operations with `simp only`, never with `rfl`.

## Tests

[The accuracy check](TanAccuracy.lean) compares `Tan.tan` natively with the double nearest to `tan x`, the quotient of the sine and cosine of [the integer reference](Reference.lean), and it fails at the first result more than one step away.  Its 180,059 arguments are those of [the sine and cosine check](TrigAccuracy.lean), which include the doubles at and next to the rounded `k · π/2` for `k` up to 20,000, where `tan` has its zeros and poles, together with the five doubles at and around each of the six thresholds `±0x3FE59428`, `±0x3FE921FB`, and `±0x3E400000`, nine special values, and the nine inputs of `WorstCases.tan`.  Those nine are the double-precision inputs that give the largest known `tan` errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [7], whose Table 3 lists 1.02 units for FreeBSD 15.1, OpenLibm, and Musl and 0.619 for GNU libc 2.44.

In `opus-verified-tests-13.log` all 180,059 results lie within one step of the reference, and 4,383 of them differ from it.  The largest measured distance therefore equals the proved bound.  The C library on minideb1 lies within 14 steps, with 301 results unequal, and the journal traces the 14 steps to glibc 2.41's `tan` at `6381956970095103 · 2^797`, 14.4 units from a 900-bit computation, where the port agrees with the reference.  The reference's truncation errors are stated in the check's docstring and are below `2^-231` relative, but they are not proved.

## Limits

The limits of [the sine and cosine theorems](Trig.md#limits) apply in the same way: Talos, `Module.initialStore`, the decoder, and `binary_file%` are trusted, the theorem covers only the canonical NaN argument, and the byte theorem covers sequences of calls to `tan` only.  The module also exports `alloc`, `release`, the reduction functions, `kernelTan`, `tanWith`, its memory, and the allocation counters, and a host that calls another export or writes the tables between calls needs a theorem that the action preserves `Ready`.  At commit `77ce56f4` the committed test driver does not check the file theorem, and the committed root import does not build `TanTheorem`, as the section on theorems records.

## References

1. FreeBSD, msun, [`lib/msun/src/s_tan.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_tan.c), commit `20381bce4b63975494a2f4bc84257f6932e6d379`.  Copyright (C) 1993 by Sun Microsystems, Inc., with the notice quoted above.
2. FreeBSD, msun, [`k_tan.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_tan.c), same commit.  Copyright 2004 Sun Microsystems, Inc., with the same notice.  It states the polynomial's error bound `2^-59.2` and the method from `0.67434` on.
3. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229).  Clause 9.2 with Table 9.1 (domains and exceptions) and clause 9.2.1 (special values) were read.
4. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.1.7, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
5. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
6. The Mathlib Community, Mathlib at commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`, [`Mathlib/Analysis/Real/Pi/Bounds.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/Real/Pi/Bounds.lean), `Real.pi_gt_d20` and `Real.pi_lt_d20`.
7. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
