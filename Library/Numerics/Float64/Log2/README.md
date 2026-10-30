# The base-2 logarithm

[The implementation](Program.lean) exports `log2`, a port of Arm's optimized-routines `log2` [1, 2] in its configuration without fused multiply-add.  It reduces `x = 2^k z` as [the natural logarithm](../Log/README.md) does, with 64 subintervals where `log` has 128, forms `r/ln 2` from `r` split at its high 32 bits, and adds `r²` times a polynomial of degree 5 in `r`, with a polynomial of degree 11 in `x - 1` near 1.  The decided bound, which [the plan's table of functions](../../../../transcendentals.md#functions) records, is one representable step from the nearest-even rounding of `log x / log 2`, `F64SignedRounding.WithinSteps 1`, as [the journal section on the port](../../../../devnotes.md#2026-10-10-ports-of-exp2-exp10-log2-log10-and-pow) proposes.  `Log2Theorem.log2_within_one` proves the bound for every finite positive input, subnormals included, `Log2Power.log2_power` proves `log2 (2^k) = k` for every power of two other than 1, and `Log2Theorem.log2_bytes_accuracy` carries the bound to the decoded WebAssembly module, with `Log2File.log2_file` connecting that module to `build/verified/log2.wasm`.  Every theorem below reports no axioms other than `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`log2` computes `Real.logb 2` of the value of its argument, which Mathlib defines as `Real.log x / Real.log 2` [9].  The domain is the finite doubles with positive value, where `log2 x` lies from -1074 to below 1024, so every result in the domain is finite.  The internal lemmas state `Real.log x / Real.log 2`, and `log2_within_one` unfolds `Real.logb`.

`Log2Theorem.log2_within_one` states the bound: for finite `x` with `0 < value x.toBits`, `F64SignedRounding.WithinSteps 1 (Real.logb 2 (value x.toBits)) (Log2.log2 x).toBits`.  [The signed reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean) defines `WithinSteps n y w` to hold when `w` is not a NaN and its `position` on the ordered line of doubles lies within `n` of the position of the nearest-even reference of `y`, which negates the reference of `|y|` for negative `y`.  `Log2Power.log2_power` adds the exact results at the powers of two, which the one-step bound alone would not give.

| Input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `1` | `+0` (bits `0`) | IEEE 754-2019 9.2.1 [6], C99 F.9.3.10 [7] | `log2_one` |
| `2^k`, `-1074 ≤ k ≤ 1023`, `k ≠ 0` | the double `k` | correct rounding, IEEE 754-2019 9.2, since `k` is a double | `Log2Power.log2_power` |
| `+0`, `-0` | `-∞` (`0xFFF0000000000000`) | IEEE 754-2019 9.2.1 (with the divideByZero exception), C99 F.9.3.10 | `log2_zero` |
| `+∞` | `+∞` | IEEE 754-2019 9.2.1, C99 F.9.3.10 | `log2_pos_infinity` |
| negative, `-∞` included, other than `-0` | the canonical NaN `0x7FF8000000000000` | IEEE 754-2019 9.2 (a quiet NaN outside the domain `[0, +∞]`, with the invalid exception), C99 F.9.3.10 | `log2_negative` |
| NaN | the canonical NaN | IEEE 754-2019 9.2 (a quiet NaN for a NaN operand), C99 F.9 paragraph 11, the deterministic profile of WebAssembly [8] | `log2_nan` |

IEEE 754-2019 lists `log2` among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [6].  The one-step bound is weaker than correct rounding, and the port is not correctly rounded: Arm states 0.550 units in the last place on the main path and 0.55 near 1 without fused multiply-add [1].  The theorem says nothing about the divideByZero and invalid exceptions or about `errno`, which the port does not compute.

## Algorithm

Arm's comment in `log2_data.c` states the method [2]: write `x = 2^k z` with `z` in `[0x1.6p-1, 0x1.6p0)`, split that interval into `N = 64` subintervals, take a point `c` near the center of the subinterval that holds `z`, and use `log2 x = k + log2 c + log2 (z/c)`, with `log2 (z/c)` a polynomial in `r = z/c - 1` and `|r| < 1/128`.  Each table entry holds `invc ≈ 1/c`, `logc ≈ log2 c`, and `c` as `chi + clo`.  Arm chose each `c` among the `±2^29` doubles around the inverse of the center as `invc`, keeping one for which `0x1.8p10 + logc` is exact, the rounding error of `z - chi - clo` is below `2^-64`, and the error of `logc` is below `2^-68` [2].  The first condition puts `logc` on the grid of `2^-42`, so that `k + logc` is exact.  The reduction is that of `log`, which Harrison, Kubaska, Story, and Tang describe for the IA-64 logarithm [5].

The main path computes `r = (z - chi - clo) · invc`, splits `r` into `rhi`, its high 32 bits, and `rlo = r - rhi`, and forms `t1 = rhi · invln2hi`, `t2 = rlo · invln2hi + r · invln2lo`, and `t3 = k + logc`, where `invln2hi + invln2lo` approximates `1/ln 2` and `invln2hi` has 32 significant bits.  It returns `lo + r² p(r) + hi` with `hi = t3 + t1`, `lo = t3 - hi + t1 + t2`, and `p` of degree 5.  Arm's comment gives `0.5 + 2/(N ln 2)` units plus the polynomial's error times `2^56` and 0.003 without fused multiply-add, 0.550 in all, for results above `2^-4` [1].

Arguments from `1 - 0x1.5b51p-5` to below `1 + 0x1.6ab2p-5` take a polynomial of degree 11 in `r = x - 1`, a subtraction that is exact there.  That path forms `hi = rhi · invln2hi` from the high 32 bits of `r`, adds `p = r² (B0 + r B1)` to it with the rounding error of the sum recovered in `lo`, and adds `r⁴` times the remaining terms in `lo` [1].  The guards, the scaling of subnormal arguments by `2^52`, and the exceptional results are those of `log`: `1` gives `+0`, both zeros give `-∞`, `+∞` gives `+∞`, and negative numbers, `-∞`, and NaN give `(x - x)/(x - x)`.

## Implementation

The source is Arm's `math/log2.c` with the data of `math/log2_data.c` and the error results of `math/math_err.c` [1, 2, 3].  The files carry `Copyright (c) 2018-2025, Arm Limited` (`log2.c`) and `Copyright (c) 2018, Arm Limited` (`log2_data.c`, `math_err.c`), under `SPDX-License-Identifier: MIT OR Apache-2.0 WITH LLVM-exception` [4], and the module docstring of [the implementation](Program.lean) repeats the notice.  The configuration is the one that `math/math_config.h` selects without fast fused multiply-add: `LOG2_TABLE_BITS` 6, `LOG2_POLY_ORDER` 7, `LOG2_POLY1_ORDER` 11, `HAVE_FAST_FMA` 0, so the reduction reads `tab2` and splits `r` at its high word, and `WANT_ROUNDING` 1 [3].

The port uses the Verified dialect, the subset of Lean that [the Verified compiler](../../../../Verified/README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [log2Near1, log2Core, log2With, log2]` generates the module, whose functions are `alloc` (0), `release` (1), `log2Near1` (2), `log2Core` (3), `log2With` (4), and `log2` (5).  The port writes each constant as `Float.ofBits` of the bit pattern of Arm's hexadecimal float, and the two tables are arrays of 128 words in data segments, borrowed at addresses 4096 and 5128.  The deviations from the C code are those of `log`: 64-bit comparisons in place of Arm's 32-bit ones, with the same results, the arithmetic shift of `tmp` as a logical shift with the sign bits set, the conversion of a negative two's complement `k` through its negation, `-1.0 / 0.0` for `__math_divzero (1)`, `(x - x) / (x - x)` for `__math_invalid (x)` without `errno`, and the tables as the parameters `tab` and `tab2`.  The high word `asdouble (asuint64 (r) & -1ULL << 32)` becomes `Float.ofBits (r.toBits &&& 0xFFFFFFFF00000000)`.

| Constant | Bits | Value |
|---|---|---|
| `InvLn2hi`, `InvLn2lo` | `0x3FF7154765200000`, `0x3DE705FC2EEFA200` | `0x1.7154765200000p+0`, `0x1.705fc2eefa200p-33` |
| `A0` to `A5` | `0xBFE71547652B8339` to `0x3FCA6225E117F92E` | the `N == 64 && LOG2_POLY_ORDER == 7` polynomial |
| `B0` to `B9` | `0xBFE71547652B82FE` to `0x3FC0B32F285AEE66` | the `LOG2_POLY1_ORDER == 11` polynomial |
| `OFF`, subnormal scale | `0x3FE6000000000000`, `0x4330000000000000` | `0x1.6p-1`, `2^52` |
| bounds of the path near 1 | `0x3FEEA4AF00000000`, `0x3FF0B55900000000` | `1 - 0x1.5b51p-5`, `1 + 0x1.6ab2p-5` |

`log2Table` is Arm's `__log2_data.tab` for `N = 64`, with `invc` at word `2i` and `logc` at `2i + 1`, and `log2Table2` is `__log2_data.tab2`, with `chi` at `2i` and `clo` at `2i + 1`.  Both tables, 256 words in all, equal the `N = 64` sections of `__log2_data.tab` and `__log2_data.tab2` in `log2_data.c` at the pinned commit, and the 18 polynomial and `1/ln 2` constants and the two bounds of the path near 1 are the binary64 values of their expressions in `log2.c` and `log2_data.c` there.  `Log2Tables.checked_entries` and `checked_logs` check the 64 entries in the kernel, and `Log2Accuracy.tableEntryOk` checks them natively: `chi + clo` against `1/invc` within `2^-100` relatively and `logc` against `log2 c` within `2^-68`, the bound of Arm's comment.

## Theorems

The theorems are in [the base-2 logarithm theorem module](Log2Theorem.lean), [the main path module](Log2Main.lean), [the power-of-two module](Log2Power.lean), and [the file module](Log2File.lean).  `x` is a Lean `Float`, and a word is the `UInt64` bit pattern of a double.  The byte theorem uses `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `Log2Main.log2_normal_within` | For a positive normal `x` outside `[1 - 0x1.5b51p-5, 1 + 0x1.6ab2p-5)`, `WithinSteps 1 (Real.log (value x.toBits) / Real.log 2) (Log2.log2 x).toBits`. |
| `Log2Main.log2_subnormal_within` | Same bound for a positive subnormal `x`. |
| `Log2Theorem.near2_within` | Same bound on the path near 1, other than 1. |
| `log2_within_one` | `WithinSteps 1 (Real.logb 2 (value x.toBits)) (Log2.log2 x).toBits` for every finite `x` with positive value. |
| `Log2Power.log2_power` | For `-1074 ≤ k ≤ 1023`, `k ≠ 0`, and `value x.toBits = 2^k`, the result is finite with value `k`. |
| `log2_one`, `log2_zero`, `log2_pos_infinity` | Bits `0`, `0xFFF0000000000000`, and `0x7FF0000000000000` for `1`, `±0`, and `+∞`. |
| `log2_negative`, `log2_nan` | A negative argument other than `-0`, `-∞` included, and a NaN give `Wasm.IEEE64.canonicalNaN`. |
| `ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant, `log2Table` borrowed at 4096, `log2Table2` at 5128, and a memory cap of at most 65,535 pages. |
| `log2_entry_call` | A call of function 5 from a store satisfying `Ready` returns, without a trap, the bits of `Log2.log2 x` and leaves a store satisfying `Ready` in which every heap region keeps its bytes. |
| `log2_bytes_accuracy` | `Log2.compiled.module` encodes to bytes that decode to it, exports function 5 as `log2`, starts in a `Ready` store, and every call from a `Ready` store returns the bits of `Log2.log2 x`, within one step of `Real.logb 2` for finite `x` with positive value, and leaves a `Ready` store.  The statement covers every call in a sequence of calls to `log2`. |
| `Log2File.log2_file`, `log2_file_decode` | `build/verified/log2.wasm` holds `encode Log2.compiled.module` and decodes to the module of `log2_bytes_accuracy`. |

Every theorem in the table has a `#print axioms` line.  `log2_bytes_accuracy` reports only the three permitted axioms, as [the journal](../../../../devnotes.md#2026-10-11-integration-of-the-sine-cosine-and-log2-theorems) records.  `tests/verified/run.sh` builds `Library.Numerics.Float64.Log2.Log2Theorem`, checks `Log2File.lean` against the `log2.wasm` that it writes earlier in the same run, and fails unless both file theorems report exactly the three permitted axioms.  Its run of 2026-10-11 passed that check and printed the permitted report for every theorem in the table.

## Proof

### Modules

The proof has ten modules in `Library/Numerics/Float64/Log2/` above the implementation, besides the file module, and it reuses the logarithm's modules for the word arithmetic, the branch guards, the table method, and the subnormal scaling.  The table lists them by stage, in dependency order within each stage.  [The library aggregate](../../../../Library.lean) includes `Log2Theorem` and `Log2Power`.

| Stage | Modules | Content |
|---|---|---|
| Words | `Log2CoreBits`, `Log2Branches` | `log2Core_eq` restates `log2Core` through `LogCoreBits.reduced` and `final2`, with the subinterval among 64 from bits 46 to 51 of `tmp`, and the guards of `log2With`. |
| Arithmetic after `r` | `Log2CoreFinal` | `final2_error`: `rhi · invln2hi`, `k + logc`, and `t3 - hi` are exact, and the other operations add at most `2^-64` before the final rounding. |
| Tables and polynomials | `Log2Tables`, `Log2KernelPoly` | 64 entries checked in the kernel, and both polynomials against `log (1 + r)/log 2`. |
| Main path | `Log2CoreStep`, `Log2Main` | `core2_within`, one step for every argument word that reaches `log2Core`, and its use for normal and subnormal arguments. |
| Path near 1, powers of two, and assembly | `Log2Near1`, `Log2Power`, `Log2Theorem` | Errors of `log2Near1` proportional to `\|x - 1\|`, `log2 (2^k) = k`, the exceptional values, `Ready`, and the byte theorem. |

### Error budget of the main path

On the main path `|log2 x| ≥ 31/500` (`Log2CoreStep.log2_away`).  [The wide relative step lemma](../../../../LeanExe/ProofKit/F64RelativeStepWide.lean), `F64RelativeStepWide.within_one_wide`, gives one step from `|c - y| ≤ (47/32) u |y|` for a computed result `c`, which leaves `(15/32) u |y|` for the error before the final rounding, with `u = 2^-53`.  The allowance is therefore `(15/32) u (31/500)`, about `3.72 · 2^-60`.

| Term | Bound | Lemma |
|---|---|---|
| Rounding of `r = ((z - chi) - clo) invc`, divided by `ln 2 ≥ 0.69` and by `0.99` for the derivative of `log (1 + r)` | `2^-59/(0.99 · 0.69)`, about `2.93 · 2^-60` | `Log2CoreStep.reduced2_error` |
| `c · invc` against 1 | `2^-100` | `Log2Tables.checked_entries` |
| `logc` against `log2 c` | `2^-65` | `Log2Tables.log2_center` |
| Polynomial against `log2 (1 + r)` for `\|r\| ≤ 1/128` | `2^-63` | `Log2KernelPoly.main2_error` |
| Operations after `r`, before the final rounding | `2^-64` | `Log2CoreFinal.final2_error` |
| Total | about `3.15 · 2^-60` against `3.72 · 2^-60` | `Log2CoreStep.target2_close`, `core2_within` |

The terms use about 85 percent of the allowance, and the rounding of `r` dominates.  Two facts close the gap that the generic bound of [the relative step lemma](../../../../LeanExe/ProofKit/F64RelativeStep.lean) left.  `t3 - hi` is exact by Sterbenz's lemma [10], proved for binary64 words in [the exact subtraction module](../../../../LeanExe/ProofKit/F64Sterbenz.lean), because `|k + logc| ≥ 1/20` on every argument that reaches the main path.  For `k = 0` the seven subintervals 35 to 41 around 1 lie inside the path near 1, every other subinterval has `|logc| ≥ 1/20`, and for `k ≠ 0` the bound `|logc| ≤ 27/50` suffices.  `t1 = rhi · invln2hi` is exact because `rhi` has at most 21 significant bits ([the high-word module](../../../../LeanExe/ProofKit/F64HighWord.lean)) and `invln2hi` has 32.

### Error budget of the path near 1

Let `ρ = |x - 1|`, between `2^-53` and `1/22`.  `x - 1` is exact, `hi = rhi · invln2hi` is exact as on the main path, and `hi - y` is exact by Sterbenz's lemma, so the remaining errors are proportional to `ρ`.  `Log2Near1.rest_error` bounds the sum before the final rounding by `u ρ/9` against `r · eval near2 r`, and `Log2KernelPoly.near2_error` adds `2^-61 ρ`, about `0.004 u ρ`.  With `|log x| ≥ (15/16) ρ` from `LogTheorem.log_near_lower` and `ln 2 ≤ 0.69315`, `|log2 x| ≥ 1.35 ρ`, and `F64RelativeStep.within_one_relative` allows `(3/8) u |log2 x|`, about `0.507 u ρ`.  The errors use about 23 percent of that allowance.

### Shared modules

The proof uses ProofKit modules, including the arithmetic chains that prove Lean's `Float` and `Float32` operations equal to Talos's functions.  Beyond the modules of `log`, which are [the signed reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean), [the relative step lemma](../../../../LeanExe/ProofKit/F64RelativeStep.lean), [the error tracker](../../../../LeanExe/ProofKit/F64ErrorTrack.lean), [exact products](../../../../LeanExe/ProofKit/F64ExactProduct.lean), [the kernel-checked polynomial bound](../../../../LeanExe/ProofKit/PolyBound.lean), and [Taylor remainders](../../../../LeanExe/ProofKit/TaylorRemainder.lean), it uses three modules added for it.  These are [the wide relative step lemma](../../../../LeanExe/ProofKit/F64RelativeStepWide.lean), [the exact subtraction module](../../../../LeanExe/ProofKit/F64Sterbenz.lean), and [the high-word module](../../../../LeanExe/ProofKit/F64HighWord.lean), which shows that clearing the low 32 bits leaves at most 21 significant bits within `2^-20` relatively.  `ExpReductionBounds` supplies the rational split of `ln 2` within `2^-92`, and the polynomial checks compare the Taylor polynomial of `log (1 + r)` with that split times the code's polynomial, dividing by `ln 2` at the end.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| For each of the 64 entries: finiteness, `\|c · invc - 1\| ≤ 2^-100`, `\|(z - c) invc\| ≤ 0.00776` over the subinterval, `chi` on the grid of `2^-53` in `[1/2, 3/2]`, `\|clo\| ≤ 2^-50`, `logc` on the grid of `2^-42` with `\|logc\| ≤ 27/50`, and `\|logc\| ≥ 1/20` outside subintervals 35 to 41 | `Log2Tables.checked_entries` |
| For each entry, the Taylor polynomials of degree 19 of `exp` at `logc · S ∓ 2^-66`, with `S` the split of `ln 2`, bracket `c`, so `\|logc - log2 c\| ≤ 2^-65` | `Log2Tables.checked_logs`, `log2_center` |
| Both polynomials, times `S`, against the Taylor polynomial of `log (1 + r)` on their intervals | `Log2KernelPoly.main2_check`, `near2_check` |
| `log2Core` on `2^k` returns the word of `k`, for each `k` from -1074 to 1025, in 42 chunks of 50 | `Log2Power.chunk0` to `chunk41`, `pow_check` |
| Values and bounds of the constants | `Log2CoreFinal.constants2`, `constant2_bounds`, `Log2Near1.near2_constants`, `near2_bounds` |
| Function 5 is exported as `log2`, and the file's bytes equal the encoder's | `Log2Theorem.log2_export`, `Log2File.log2_file` |

### History

[The journal section](../../../../devnotes.md#2026-10-11-log2-theorem-track-log) records two choices that shaped the proof.  On the main path the generic `11/8` bound of `F64RelativeStep` did not suffice: at subinterval 42 the error reached 1.39 times the allowance, and the exact `t3 - hi` together with the wider factor `47/32` of `F64RelativeStepWide` closed the gap.  For the powers of two, one `decide` over all 2,100 values of `k` had not finished after 16 minutes and a fold over `Nat.rec` had not finished after 10, while chunks of 50 took 4 to 9 seconds each, so `Log2Power` checks 42 chunks.  The first build of `Log2Power` with the chunks elaborated in parallel stopped making progress, and with `Elab.async false` the module checks in about seven minutes.

## Tests

[The accuracy check](../../../../tests/TestSupport/Numerics/Log2Accuracy.lean) compares `Log2.log2` and `Log10.log10` natively with the doubles nearest to `log2 x` and `log10 x` from [the power reference](../../../../tests/TestSupport/Numerics/PowerReference.lean), which divides [the integer reference](../../../../tests/TestSupport/Numerics/Reference.lean)'s logarithm by `ln 2` or `ln 10` at 500 bits, and it fails at the first result more than one step away.  It first checks every entry of `log2`'s tables against its center.  Its 342,219 arguments are 100,001 evenly spaced values from 0 to 20, 100,001 from 0.9 to 1.1, 100,000 hashed positive values over all exponents, 40,000 doubles on both sides of 1 at hashed distances of up to `2^36` units, the five doubles at and around each of 13 edges, the 52 subnormal and 2,046 normal powers of two, the 23 powers of ten from 1 to `10^22`, nine special and negative values, and the 22 inputs of `WorstCases.log2` and `WorstCases.log10`.  The twelve inputs of `WorstCases.log2` are those that give the largest known `log2` errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [11], whose Table 3 lists 0.548 units for GNU libc 2.44, 0.555 for Musl, 0.554 for the Arm Performance Library, and 0.921 for FreeBSD 15.1.

In the test run, all 342,219 results of `log2` lie within one step of the reference, and 892 of them differ from it, so the largest measured distance equals the proved bound.  The C library of the test run lies within one step at the same arguments, with 859 results unequal to the reference.  The reference's docstrings state its truncation errors, a relative error below `2^-420` for these logarithms, and no theorem proves them.  Such an error can change the reference only for an exact value within that distance of a midpoint between two doubles, where the reference may name the other double beside the midpoint.

## Limits

The theorem is about Talos's semantics of WebAssembly.  It trusts the Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode`, as [the design notes](../../../../docs/design.md#scope-of-the-theorem) record, and the file theorem trusts the elaborator `binary_file%`, which reads `log2.wasm`.  Talos implements the deterministic profile, in which every NaN result is canonical [8], and an engine outside that profile, such as a browser, may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, and every NaN `Float` has the canonical bits, so the theorem covers only the canonical NaN among the NaN words a WebAssembly caller can pass.  For another NaN word the compiled code reaches the guard on `top &&& 0x7ff0` and returns `(x - x)/(x - x)`, which is the canonical NaN in Talos, but no theorem states it.  `log2_bytes_accuracy` covers sequences of calls to `log2` only, and a host that calls another export of the module or writes its memory, which holds the two tables, between calls needs a theorem that the action preserves `Ready`.  `log2_power` is a statement about the Lean function, and the byte theorem carries only the one-step bound, so the exact powers of two reach the compiled module through the equality of its result with `Log2.log2 x`.

## References

1. Arm Limited, optimized-routines, [`math/log2.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/log2.c).  Copyright (c) 2018-2025, Arm Limited, MIT OR Apache-2.0 WITH LLVM-exception.
2. Arm Limited, optimized-routines, [`math/log2_data.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/log2_data.c), same commit: the tables, the polynomials with their stated errors, and the comment that describes the algorithm and the choice of the centers.
3. Arm Limited, optimized-routines, [`math/math_err.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/math_err.c) and [`math/math_config.h`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/math_config.h), same commit.
4. Arm Limited, optimized-routines, [`LICENSE`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/LICENSE), same commit.
5. J. Harrison, T. Kubaska, S. Story, and P. T. P. Tang, ["The Computation of Transcendental Functions on the IA-64 Architecture"](https://www.cl.cam.ac.uk/~jrh13/papers/itj.pdf), *Intel Technology Journal*, Q4 1999.  Its section on `Ln` describes `ln x = ln (1/frcpa (x)) + ln (1 + r)` with a table of `ln (1/frcpa)`.
6. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229).  This document cites clause 9.2 with Table 9.1 (the domain of `log2`, correct rounding, NaN operands) and clause 9.2.1 (special values).
7. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.3.10, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
8. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
9. The Mathlib Community, Mathlib, [`Mathlib/Analysis/SpecialFunctions/Log/Base.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Log/Base.lean), `Real.logb b x := log x / log b`.
10. R. P. Brent and P. Zimmermann, [*Modern Computer Arithmetic*](https://arxiv.org/abs/1004.4710), version 0.5.1, 2010, Theorem 3.2.2 (Sterbenz): for floating-point numbers `x` and `y` of the same precision with `y` in `[x/2, 2x]`, `y - x` is exactly representable if there is no underflow.  The book cites P. H. Sterbenz, *Floating-Point Computation*, Prentice Hall, 1974, whose text is not checked here.
11. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
