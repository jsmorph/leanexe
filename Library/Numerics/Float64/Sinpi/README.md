# The sine, cosine, and tangent of π x

[The implementation](Program.lean) exports `sinpi`, `cospi`, and `tanpi`, ports of Steven G. Kargl's `sinpi`, `cospi`, and `tanpi` as FreeBSD's msun has them [1, 2, 3, 4], which call fdlibm's kernels of [the sine and cosine](../Trig/README.md) and [the tangent](../Tan/README.md).  The decided bound is one representable step from the nearest-even rounding of the real function, `F64SignedRounding.WithinSteps 1`, with bit equalities for the signed zeros at the integers, the zeros of `cospi`, the infinities of `tanpi`, and the NaN results.  The bound is proved for every finite binary64 input except the poles of `tanpi`, whose results are proved as words, and `SinpiTheorem.sinpi_bytes_accuracy`, `cospi_bytes_accuracy`, and `tanpi_bytes_accuracy` carry the results to the decoded WebAssembly module, with `SinpiFile.sinpi_file` connecting that module to `build/verified/sinpi.wasm`.  No accepted theorem depends on an axiom other than `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`sinpi x`, `cospi x`, and `tanpi x` compute `sin (π x)`, `cos (π x)`, and `tan (π x)` for the value `x` of the argument, the operations that IEEE 754-2019 names `sinPi`, `cosPi`, and `tanPi` [5] and C23 names `sinpi`, `cospi`, and `tanpi` [6].  Every finite double is in the domain of `sinpi` and `cospi`.  `tanpi` has poles at `n + 1/2` for integers `n`, where the rules prescribe an infinity, and Mathlib's `Real.tan`, equal to `Real.sin x / Real.cos x`, is 0 there by Mathlib's division by zero, so the accuracy theorem of `tanpi` excludes those inputs and a theorem of its own gives their words.

The bounds are stated with [the signed reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean) that [the sine and cosine document](../Trig/README.md#specification) describes.  For finite `x`, `SinpiWithin.sinpi_within` states `WithinSteps 1 (Real.sin (Real.pi * value x.toBits)) (Sinpi.sinpi x).toBits`, and `cospi_within` states the same for `Real.cos`.  `tanpi_within` states it for `Real.tan` when `value x.toBits ≠ n + 1/2` for every integer `n`.  `WithinSteps` places both zeros at position 0, so the signed zeros have their own theorems, which the table lists with the infinities at the poles.

| Input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `sinpi (±0)`, `tanpi (±0)` | `±0` | IEEE 754-2019 9.2.1; C23 F.10.1.13 and F.10.1.14 | `sinpi_int`, `tanpi_int` with `n = 0` |
| `sinpi (±n)`, positive integer `n` | `±0` | IEEE 754-2019 9.2.1; C23 F.10.1.13 | `sinpi_int` |
| `cospi (±0)` | `1` | IEEE 754-2019 9.2.1; C23 F.10.1.12 | one-step bound (`cospi_within`) |
| `cospi (n + 1/2)`, integer `n` | `+0` | IEEE 754-2019 9.2.1; C23 F.10.1.12 | `cospi_half` |
| `tanpi n`, integer `n ≠ 0` | `+0` for positive even and negative odd `n`, `-0` for positive odd and negative even `n` | IEEE 754-2019 9.2.1; C23 F.10.1.14 | `tanpi_int` |
| `tanpi (n + 1/2)`, integer `n` | `+∞` for even `n`, `-∞` for odd `n` | IEEE 754-2019 9.2.1 (with the divideByZero exception); C23 F.10.1.14 | `tanpi_half` |
| `±∞` | NaN, the canonical NaN in the deterministic profile [7] | IEEE 754-2019 Table 9.1 (outside the domain); C23 F.10.1.12 to F.10.1.14 | `nonfinite` |
| NaN | canonical NaN | IEEE 754-2019 9.2; C23 F.10 paragraph 14 | `nonfinite` |

The sources state the same rules in their comments [1, 2, 3].  `s_tanpi.c` also lists "tanpi(+-n+1/4) = +-1, for positive integers n", which IEEE 754-2019 and C23 do not list: the kernel returns 1 at a reduced argument of `1/4`, so `tanpi` returns `±1` with the sign of `x` at `±(n + 1/4)` for every integer `n ≥ 0`, and the theorems bound that result within one step.  From `2^52` on every double is an integer, so `sinpi` and `tanpi` return signed zeros there and `cospi` returns `±1` by parity, and from `2^53` on every double is even, so `cospi` returns 1.  IEEE 754-2019 asks for correct rounding of these operations in clause 9.2, Kargl states no error bound, and the one-step bound is weaker than correct rounding.  The theorems say nothing about floating-point exceptions, which the port does not compute.

## Algorithm

Kargl's method reduces the argument to `[0, 1/4]` before it multiplies by `π` [1].  For `|x| < 1`, `sinpi` reflects `|x|` with `sin (π x) = cos (π (1/2 - x))` and the similar identities: it uses the sine kernel on `[0, 1/4)`, the cosine kernel at `1/2 - x` on `[1/4, 1/2)` and at `x - 1/2` on `[1/2, 3/4)`, and the sine kernel at `1 - x` on `[3/4, 1)`.  `cospi` exchanges the two kernels and changes the sign from `1/2` on.  `tanpi` uses its kernel on `[0, 1/2)` and `tan (π x) = -tan (π (1 - x))` on `(1/2, 1)`, and the kernel uses `tan (π x) = 1/tan (π (1/2 - x))` above `1/4` [3].  The differences `1/2 - x`, `x - 1/2`, and `1 - x` are exact by Sterbenz's lemma, since `x` lies within a factor of 2 of the constant on each interval.  For `1 ≤ |x| < 2^52` the functions subtract the integer part `N` of `|x|`, which is exact, and use `sin (π (N + r)) = (-1)^N sin (π r)`, the same for `cos`, and `tan (π (N + r)) = tan (π r)` [1, 2, 3].

The kernels form `π r` as `hi + lo` for `r` in `[0, 1/4]` [4].  `hi = (float) r` rounds `r` to 24 bits, `lo = r - hi` is exact, and `π` is the sum of `pi_hi`, which has 26 significant bits, and `pi_lo`, so `hi · pi_hi`, a product of at most 50 bits, is exact.  The tail `lo · (pi_lo + pi_hi) + hi · pi_lo` and a Fast2Sum (`_2sumF`) give `hi + lo` with `|lo|` at most half a unit of `hi`, which `__kernel_sin`, `__kernel_cos`, or `__kernel_tan` takes as its argument and tail.  `s_tanpi.c` describes `pi_hi + pi_lo` as "an 80-bit approximation of pi" [3].

Below `2^-29` in magnitude, `sinpi x` and `tanpi x` are `π x`, computed from `x` scaled by `2^53` and split at its high 32 bits, so that subnormal inputs lose no bits, and scaled back by `2^-53` [1, 3].  `cospi` returns 1 there, which lies within `2^-55` of `cos (π x)`.  At the poles `tanpi` divides `±1` by zero, at the integers `sinpi` and `tanpi` return signed zeros, and at `n + 1/2` `cospi` returns `+0`.

## Implementation

The sources are `s_sinpi.c`, `s_cospi.c`, `s_tanpi.c`, `k_sinpi.h`, and `k_cospi.h` [1, 2, 3, 4], the three source files "Copyright (c) 2017, 2023 Steven G. Kargl" and the two headers "Copyright (c) 2017 Steven G. Kargl", under the BSD-2-Clause license, whose conditions require that redistributions of source code retain the notice, the conditions, and the disclaimer, and that redistributions in binary form reproduce them in the documentation or other materials provided with the distribution.  The kernels they call are fdlibm's, under Sun's notice, which [the sine and cosine document](../Trig/README.md#implementation) quotes.  The module docstring of [the implementation](Program.lean) names the five files and the commit and quotes both notices verbatim, with the conditions and the disclaimer.  The port is written in the Verified dialect, the subset of Lean that [the Verified compiler](../../../../Verified/README.md) translates to WebAssembly with a correctness theorem.

`verified_compile compiled := [Trig.kernelSin, Trig.kernelCos, Tan.kernelTan, toSingle, piProduct, kernelSinpi, kernelCospi, kernelTanpi, piTiny, ffloor, oddPart, sinpi, cospi, tanpi]` generates the module, so the reflector compiles the Lean definitions of the three fdlibm kernels again into it.  Its functions are `alloc` (0), `release` (1), the listed definitions from 2 on, `sinpi` (13), `cospi` (14), and `tanpi` (15).  The module has no tables, and `tools/Emit.lean` writes it as 5,806 bytes.

| C code | Port | Reason |
|---|---|---|
| `hi = (float) x` | `toSingle x`, which rounds the 52-bit fraction to 23 bits, ties to even, with any carry into the exponent field | The dialect has no single precision.  `toSingle` is `(float) x` for zero and for every double whose single-precision value is normal, which covers every kernel argument, 0 or from `2^-54` to `1/2`. |
| `FFLOOR (x, j0, ix, lx)` | `ffloor ix lx` on 64-bit words with 32-bit masks | Macro of `math_private.h` [8] on words. |
| `if (j0 > 30) x -= 0x1p30; j0 = (uint32_t) x; if (j0 & 1)` in `sinpi` and `cospi`, where `j0 > 30` holds for integer parts from `2^31` on | `oddPart`: the same test and subtraction, then the parity from `toUInt64` | From `2^32 + 2^30` on, `x - 2^30` exceeds the range of `uint32_t`, and C leaves that conversion undefined (C23 6.3.1.4 [6]).  `s_tanpi.c` takes the parity from `(uint64_t) x & 1`, and `SinpiFloor.oddPart_spec` proves that `oddPart` gives the parity of the integer part. |
| `__kernel_sinpi`, `__kernel_cospi`, `__kernel_tanpi` | `kernelSinpi`, `kernelCospi`, `kernelTanpi`, sharing `piProduct` | The three kernels start with the same computation of `π x` as `hi + lo`. |
| `_2sumF (hi, lo)` | `w = hi + lo` and `(hi - w) + lo` | Definition of the macro without `DEBUG` [8]. |
| `π x` below `2^-29` | `piTiny x hx` | Shared computation of `s_sinpi.c` and `s_tanpi.c`. |
| `vzero / vzero`, `1 / vzero`, `odd / vzero` | `0.0 / 0.0`, `1.0 / 0.0`, `odd / 0.0` | `vzero` is a volatile zero that prevents constant folding, and the dialect has no such qualifier. |
| `(int) ax == 0` in `cospi` | `ax.toUInt64 == 0` | Both truncations give 0 wherever the test runs. |
| `copysign (0, x)` | `if neg then -0.0 else 0.0` | `neg` is the sign bit of `x`. |

| Constant | Bits | Value |
|---|---|---|
| `pi_hi` | `0x400921FB58000000` | `3.1415926814079285`, 26 significant bits |
| `pi_lo` | `0xBE5DDE973DCB3B3A` | `-2.7818135228334233e-08` |
| `0x1p53`, `0x1p-53` | `0x4340000000000000`, `0x3CA0000000000000` | scale factors of the tiny path |

`s_sinpi.c`, `s_cospi.c`, and `s_tanpi.c` print the two words of `π` beside their decimal values, the port writes those words, and each decimal value rounds to its word, as the journal records for the 62 annotated constants of [the stage 6 ports](../../../../devnotes.md#2026-10-10-ports-of-sinpi-cospi-tanpi-erf-and-erfc).  `SinpiProduct.const_facts` evaluates in the kernel the values `52707179 · 2^-24` and `-8407515482766138 · 2^-78` of the two words and their rounded sum `pi_lo + pi_hi`, `0x400921FB54442D18`, the double nearest `π`.  A Python comparison of `toSingle` with C's conversion, through the `struct` module, found no difference at 200,000 random doubles from `2^-60` to 1 and at 500,000 doubles at and next to the rounding ties, as the same journal section records.

## Theorems

The theorems are in the modules `SinpiWithin`, `SinpiExact`, `SinpiExactTan`, `SinpiTheorem`, and `SinpiFile` of `Library/Numerics/Float64/Sinpi/`.  In the table, `x` is a Lean `Float`, `a = value x.toBits` its real value, and a word is the `UInt64` bit pattern of a double.  The byte theorems use `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `SinpiWithin.sinpi_within`, `cospi_within` | For finite `x`, `WithinSteps 1 (Real.sin (Real.pi * a)) (Sinpi.sinpi x).toBits`, and the same for `Real.cos` and `Sinpi.cospi`. |
| `SinpiWithin.tanpi_within` | For finite `x` with `a ≠ n + 1/2` for every integer `n`, `WithinSteps 1 (Real.tan (Real.pi * a)) (Sinpi.tanpi x).toBits`. |
| `SinpiExact.sinpi_int` | For finite `x` with an integer value, `sinpi x` has the bits `0x8000000000000000` when the sign bit of `x` is set and `0` otherwise. |
| `SinpiExact.cospi_half` | For finite `x` with `a = n + 1/2`, `cospi x` has the bits `0`. |
| `SinpiExact.nonfinite` | For an infinity or a NaN, the three functions give `Wasm.IEEE64.canonicalNaN`. |
| `SinpiExactTan.tanpi_int` | For finite `x` with the integer value `n`, `tanpi x` has the bits `0x8000000000000000` when the sign bit of `x` differs from the parity of `n`, and `0` otherwise. |
| `SinpiExactTan.tanpi_half` | For finite `x` with `a = n + 1/2`, `tanpi x` has the bits `0xFFF0000000000000` for odd `n` and `0x7FF0000000000000` for even `n`. |
| `SinpiTheorem.ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant and a memory cap of at most 65,535 pages. |
| `sinpi_entry_call`, `cospi_entry_call`, `tanpi_entry_call` | A call of function 13, 14, or 15 from a `Ready` store returns, without a trap, the bits of the Lean function, and leaves a `Ready` store in which every heap region keeps its bytes. |
| `exports` | Functions 13, 14, and 15 are exported as `sinpi`, `cospi`, and `tanpi`. |
| `sinpi_bytes_accuracy`, `cospi_bytes_accuracy`, `tanpi_bytes_accuracy` | `Sinpi.compiled.module` encodes to bytes that decode to it, exports the function, starts in a `Ready` store, and every call from a `Ready` store returns the bits of the Lean function, within one step on the domain of the accuracy theorem, and leaves a `Ready` store.  The statements cover every call in a sequence of calls to the three exports. |
| `SinpiFile.sinpi_file` | `build/verified/sinpi.wasm` holds `encode Sinpi.compiled.module`. |
| `sinpi_file_decode` | The file decodes to the module of the three byte theorems, whose bytes it takes from their conjunction, so its axiom report covers all three. |

Each module has `#print axioms` lines.  They print `[propext, Classical.choice, Quot.sound]` for the three accuracy theorems, the exact rules, every declaration of `SinpiTheorem`, and both file theorems, which `lake env lean Library/Numerics/Float64/Sinpi/SinpiFile.lean` checks after `tools/Emit.lean` writes `sinpi.wasm`.  [The journal section of 2026-10-12 on these functions](../../../../devnotes.md#2026-10-12-sinpi-cospi-and-tanpi-track-trig) records these builds and that `wasm-tools validate` accepts the file.  `Verified.lean` imports `SinpiTheorem`, and the entry `sinpi:SinpiTheorem:SinpiFile` of `tests/verified/run.sh` checks `SinpiFile` against the `sinpi.wasm` it writes.

## Proof

### Modules

The proof adds 22 modules in `Library/Numerics/Float64/Sinpi/`, above the chains of [the sine and cosine proof](../Trig/README.md#modules) and [the tangent proof](../Tan/README.md#modules).  From those chains it takes fdlibm's kernels with their final steps (`TrigKernelSpec.sinTail_spec`, `TrigCosKernel.cos_spec`, `TrigStep.sin_final`, `cos_final`, and `TanWith.kernel_within`), Sterbenz's lemma (`TanTrunc.sterbenz`), and facts about words from `TrigReduce` and from ProofKit's `F64SignedNearestSum` and `F64SelfStep`.  The table lists the modules by stage, in dependency order within each stage.

| Stage | Modules | Content |
|---|---|---|
| Product and kernels | `SinpiSingle`, `SinpiProduct`, `SinpiKernels`, `SinpiTanKernel` | `toSingle` within `2^-24` of its argument, relative, with at most 24 significant bits (`single_spec`), `piProduct r` within `r/2^62` of `π r` (`product_spec`), and the kernels within one step of `sin (π x)` and `cos (π x)` from `2^-54` to `1/4` and of `tan (π x)` from `2^-54` below `1/2` (`kernel_pair`, `kernel_tanpi`). |
| Reflections and words | `SinpiReflect`, `SinpiBits`, `SinpiFloor`, `SinpiPieces`, `SinpiCommon` | Exact reflections (`half_sub`, `sub_half`, `one_sub`), `ax` as `\|x\|` and `neg` as the sign bit (`ax_abs`, `neg_flag`), `ffloor` as the integer part and `oddPart` as its parity (`ffloor_bits`, `floor_spec`, `oddPart_spec`), reflected chains below 1 (`sin_chain`, `cos_pieces`, `tan_pieces`), thresholds of the high word, and integer value of every input from `2^52` on (`abs_thresholds`, `big_integer`). |
| Branches | `SinpiSin`, `SinpiCos`, `SinpiCosFloor`, `SinpiTanpi` | `sinpi_mid`, `sinpi_floor`, `sinpi_big`, `cospi_small`, `floor_frac`, `cospi_floor`, `tanpi_mid`, and `tanpi_floor`. |
| Tiny path | `SinpiTinyWords`, `SinpiTinySplit`, `SinpiTinyReal`, `SinpiTiny` | Exact head and tail of `x 2^53` (`tiny_bits`, `split_spec`), error of `piTiny` (`sum_error`, `final_error`, `tiny_spec`), `sinpi_tiny`, and `tanpi_tiny`. |
| Assembly | `SinpiWithin`, `SinpiExact`, `SinpiExactTan`, `SinpiTheorem`, `SinpiFile` | `cospi_big`, `tanpi_big`, the three accuracy theorems, the exact rules, the byte theorems, and the file theorems. |

### Error budget

Let `u = 2^-53`.  `SinpiProduct.product_spec` places the result `w + t` of `piProduct r` within `r/2^62` of `π r` for `r` from `2^-54` to `1/2`, with `|t| ≤ |w|/2^52`, from the `2^-24` of `single_spec` and `|pi_hi + pi_lo - π| ≤ 2^-66` (`pi_parts`, from Mathlib's twenty-digit bounds on `π` [9]).  Relative to `π r` that error is below `2^-63.6`, and the kernel lemmas accept any target `θ` within `|θ|/2^59` of their argument `w + t`, so `SinpiKernels.kernel_pair` and `SinpiTanKernel.kernel_tanpi` apply them with `θ = π r` and with at least the margins of [the sine and cosine budget](../Trig/README.md#error-budget) and [the tangent budget](../Tan/README.md#error-budget).  The kernel arguments `π r`, for the reduced arguments `r`, lie from `π · 2^-54` to `π/4`, inside the range `0.78541` of those lemmas.

The reflections are exact, and their results lie from `2^-54` to `1/4` or are 0 at `|x| = 1/2`, where `SinpiPieces.cospi_zero` evaluates `kernelCospi 0` to 1 in the kernel.  From 1 to `2^52`, `SinpiCosFloor.floor_frac` gives the integer part `N`, the exact fraction `|x| - N`, which is 0 or at least `2^-52`, and `2^31 ≤ N` whenever `oddPart` subtracts `2^30`.  `sin_shift`, `cos_shift`, and `tan_shift` move the target by `N π`, and the parity of `N` changes the sign of the sine and the cosine.

Below `2^-29`, `SinpiTiny.tiny_spec` places `piTiny x` within `(1 + 2^-10) u · max (|π x|, 2^-1021) + 2^-1085` of `π x`.  `SinpiTinySplit.split_spec` shows that `x 2^53`, its head `hi`, and the tail `lo` are exact, with `|lo| ≤ |x 2^53|/2^20 + 2^-989`, and that `hi` has at most 21 significant bits, so `pi_hi hi` is exact, and `SinpiTinyReal.final_error` adds the last rounding and the scaling by `2^-53`, which is exact when its result is normal.  `sin (π x)` and `tan (π x)` lie within `|π x|³ ≤ (5/16) u |π x|` of `π x` (`close_within`).  `SinpiLowStep.within_low` accepts a word within `(47/32) u · max (|y|, 2^-1021)` of `y` for `|y| ≥ 2^-1073`: it extends `F64RelativeStepWide.within_one_wide`, which requires `|y| ≥ 2^-1000`, to subnormal results through `F64FullStep.one_step_binades`.

| Inputs | Path | Bound | Allowance | Theorem |
|---|---|---|---|---|
| `sinpi`, `tanpi`, `0 < \|x\| < 2^-29` | `piTiny` | `(1 + 2^-10 + 5/16) u`, about `1.31 u`, relative to `max (\|π x\|, 2^-1021)`, plus `2^-1085` | `(47/32) u`, about `1.47 u` | `SinpiTiny.sinpi_tiny`, `tanpi_tiny` through `within_low` |
| `cospi`, `\|x\| < 2^-29` | the result is 1 | `\|1 - cos (π x)\| ≤ 2^-55` (`cos_tiny`) | `0.74 u` of `TanStep.near_rel` | `SinpiCos.cospi_small` through `one_near` |
| all three, `2^-29 ≤ \|x\| < 1` | reflection, `piProduct`, and kernel | `\|π r\|/2^63.6` for the product | `\|π r\|/2^59` in the kernel lemmas | `SinpiSin.sinpi_mid`, `SinpiCos.cospi_small`, `SinpiTanpi.tanpi_mid` |
| all three, `1 ≤ \|x\| < 2^52` | fraction, then as above | same | same | `SinpiSin.sinpi_floor`, `SinpiCosFloor.cospi_floor`, `SinpiTanpi.tanpi_floor` |
| all three, `\|x\| ≥ 2^52` | `±0`, `±1`, or `±0` | exact | | `SinpiSin.sinpi_big`, `SinpiWithin.cospi_big`, `tanpi_big` |

The margin of the tiny path is about 10 percent of its allowance.  The paths through the kernels keep at least the stated margins of the sine, cosine, and tangent proofs, 4 to 17 percent, since the product's error is less than a twentieth of the kernels' allowance for the argument.  `SinpiWithin.sinpi_within`, `cospi_within`, and `tanpi_within` combine the ranges, and the sign of `x` negates the results of `sinpi` and `tanpi`.

### Shared modules

The analysis of the `π x` functions uses [the wide relative step](../../../../LeanExe/ProofKit/F64RelativeStepWide.lean) and its extension below `2^-1000` (`F64RelativeStepLow.within_low`), [one step by binades](../../../../LeanExe/ProofKit/F64FullStep.lean) for subnormal results, [grid exactness](../../../../LeanExe/ProofKit/F64GridExact.lean) for the tails, [exact products by powers of two](../../../../LeanExe/ProofKit/F64ExactProduct.lean) for the scaling by `2^53` and `2^-53`, and the rounding bounds of [products](../../../../LeanExe/ProofKit/F64MulBounds.lean) and [sums](../../../../LeanExe/ProofKit/F64AddBounds.lean).  `SinpiProduct.pi_parts` takes `π` from Mathlib's `Real.pi_gt_d20` and `Real.pi_lt_d20`, and `SinpiCos.cos_tiny` uses `Real.one_sub_sq_div_two_le_cos` [9].

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| Values of `pi_hi` and `pi_lo`, and their rounded sum `0x400921FB54442D18` | `SinpiProduct.const_facts` |
| Scale factors `2^53` and `2^-53` | `SinpiTinyWords.consts53` |
| `piProduct 0` is `(0, 0)` and the cosine kernel gives 1 there, so `kernelCospi 0 = 1` | `SinpiPieces.cospi_zero` |
| Functions 13, 14, and 15 are exported as `sinpi`, `cospi`, and `tanpi` | `SinpiTheorem.exports` |
| The file's bytes equal the encoder's | `SinpiFile.sinpi_file` |

The kernel polynomial bounds are those of [the sine and cosine proof](../Trig/README.md#kernel-checked-facts) and [the tangent proof](../Tan/README.md#kernel-checked-facts), whose kernel lemmas this proof applies.  The module has no tables to check.  `pi_parts`, the only comparison with `π`, follows by `linarith` from Mathlib's decimal bounds.

### History

The journal section "2026-10-12: `sinpi`, `cospi`, and `tanpi` (track `trig`)" records two failures that shaped the modules.  `split_spec` first exhausted its 200,000 heartbeats because `push_cast` and `field_simp` evaluated `2^1074` into a 324-digit numeral, and the proof now splits into `tail_le` and `tail_grid` and rewrites with `Nat.cast_mul`, `Nat.cast_pow`, and `mul_div_assoc`.  `rw [if_neg (by decide)]` rewrites the first `if` of the goal, which after `cos_shift` was the real-valued `if N % 2 = 1`, so the proofs name each condition with `show` and apply the shift after the rewrites on words.

## Tests

[The accuracy check](../../../../tests/TestSupport/Numerics/SinpiAccuracy.lean) compares the three functions natively with references from `Reference.sinCosTurns` at `|x|/2` turns, with 64 bits above the precision of `x`, rounded to the nearest double, and it requires each result within one step and, where the reference is a zero or an infinity, its exact bits.  The references give the zeros and the poles, with their signs, by the rules in the table above, and use the series elsewhere.  Its 204,631 arguments are 100,001 evenly spaced values from -4 to 4, the five doubles at and around each multiple of `1/4` from -100 to 100, the five doubles at and around `±(2^k + 1/2)` for `k` from 0 to 51, 100,000 hashed values from `2^-60` to below `2^60` with both signs, the five doubles at and around the seven thresholds of the code with both signs, 13 special values, and the 22 inputs of `WorstCases.sinpi`, `cospi`, and `tanpi`.  Those 22 are the double-precision inputs that give the largest known errors of these functions in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [10], whose Table 3 lists 0.812, 0.812, and 0.969 units for FreeBSD 15.1 and 1.86, 1.86, and 2.85 for GNU libc 2.44.

In a run of `tests/verified/run.sh` on 2026-10-11, the 204,631 results of each function lie within one step of the reference with the signs of the zeros and infinities, and 4,641 of `sinpi`, 4,596 of `cospi`, and 5,185 of `tanpi` differ from it, so the largest measured distance equals the proved bound.  Lean has no binding of these functions, so the check reports no library distance.  Python models of the references agreed with 260-digit decimal computations at 1,353 arguments that are neither integers nor integers plus `1/2` ([the stage 6 ports](../../../../devnotes.md#2026-10-10-ports-of-sinpi-cospi-tanpi-erf-and-erfc)), and the docstring of `SinpiAccuracy.sinCosPi` bounds the error of the reference below a relative `2^-390`, a claim that is not proved.

## Limits

The one-step theorem of `tanpi` excludes the half-integers, where Mathlib's `Real.tan` is 0 because it divides by a zero cosine, and `tanpi_half` states the infinities there as words.  The limits of [the sine and cosine theorems](../Trig/README.md#limits) apply: Talos, `Module.initialStore`, the decoder, and `binary_file%` are trusted, the argument is a Lean `Float`, whose only NaN is the canonical one (`F64Bits.toBits_canonical`), so the theorems cover only the canonical NaN among the NaN words a WebAssembly caller can pass, and the byte theorems cover sequences of calls to `sinpi`, `cospi`, and `tanpi`.  A host that calls another function of the module, such as `alloc` or `release`, or writes its memory between calls needs a theorem that the action preserves `Ready`.

No theorem states the bits of the results that are exactly `±1`, such as `cospi n` for integers `n`, `sinpi (n + 1/2)`, and `tanpi (±(n + 1/4))`: the code returns `±1` there, and the theorems bound these results within one step.  The proof uses the properties of `toSingle` that `single_spec` states, so its equality with C's `(float) x`, which holds where the single-precision value is normal, rests on the Python comparison.  The code and the C sources subtract `2^30` from `2^31` on (`j0 > 30`), as the docstring of `Sinpi.oddPart` states, and `floor_frac` and `oddPart_spec` prove the parity for the code as written.

## References

1. Steven G. Kargl, FreeBSD msun, [`lib/msun/src/s_sinpi.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_sinpi.c).  Copyright (c) 2017, 2023 Steven G. Kargl, BSD-2-Clause.  The comment describes the method and the special cases.
2. Steven G. Kargl, FreeBSD msun, [`s_cospi.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_cospi.c), same commit and license.
3. Steven G. Kargl, FreeBSD msun, [`s_tanpi.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/s_tanpi.c), same commit and license, with its kernel `__kernel_tanpi`.
4. Steven G. Kargl, FreeBSD msun, [`k_sinpi.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_sinpi.h) and [`k_cospi.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/k_cospi.h), same commit and license.
5. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229): clause 9.2 with Table 9.1 (domains and exceptions of `sinPi`, `cosPi`, and `tanPi`) and clause 9.2.1 (their special values).
6. ISO/IEC 9899:2024, *Programming languages — C* (C23), clause 6.3.1.4 (conversion of floating values to integers), clauses 7.12.4.12 to 7.12.4.14, and Annex F, clauses F.10 and F.10.1.12 to F.10.1.14, as in WG14 working draft [N3220](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3220.pdf) (February 2024).  The published standard was not consulted.
7. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
8. FreeBSD, msun, [`math_private.h`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/math_private.h), same commit: `FFLOOR` and `_2sumF`.
9. The Mathlib Community, Mathlib: [`Mathlib/Analysis/Real/Pi/Bounds.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/Real/Pi/Bounds.lean) (`Real.pi_gt_d20`, `Real.pi_lt_d20`) and [`Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean) (`Real.one_sub_sq_div_two_le_cos`).
10. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
