# The natural logarithm

[The implementation](Program.lean) exports `log`, a port of Arm's optimized-routines `log` [1, 2] in its configuration without fused multiply-add: a reduction `x = 2^k z`, a table of 128 subinterval centers `c` with `1/c` and `log c`, a polynomial of degree 6 in `r = z/c - 1`, and a polynomial of degree 12 in `x - 1` near 1.  The decided bound is one representable step from the nearest-even rounding of the real logarithm, `F64SignedRounding.WithinSteps 1`, the bound that [the plan for the remaining functions](../../../../devnotes.md#2026-10-10-plan-for-the-remaining-functions) set on 2026-10-10 after the exponential.  `LogTheorem.log_within_one` proves the bound for every finite positive input, subnormals included, five theorems give the exceptional values exactly, and `LogTheorem.log_bytes_accuracy` carries both to the decoded WebAssembly module, with `LogFile.log_file` connecting that module to `build/verified/log.wasm`.  Every theorem below reports no axioms other than `propext`, `Classical.choice`, and `Quot.sound`.

## Specification

`log` computes `Real.log` of the value of its argument.  The domain is the finite doubles with positive value, from the smallest subnormal `2^-1074` to the largest finite double, where `|log x|` stays below 745, so every result in the domain is finite.  The result is negative below 1, and the bound measures it against the signed reference.

`LogTheorem.log_within_one` states the bound: for finite `x` with `0 < value x.toBits`, `F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits)) (Log.log x).toBits`.  [The signed reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean) defines `WithinSteps n y w` to hold when `w` is not a NaN and its `position` lies within `n` of the position of `roundNearestEven y`.  `position` places every word on the ordered line of doubles, both zeros at 0 and the infinities next to the largest finite values, and `roundNearestEven y` negates the nonnegative nearest-even reference of `|y|` for negative `y`.  Rounding to nearest, ties to even, is symmetric, so the signed reference is the rounding that IEEE 754-2019 defines [7].

| Input | Result | Source of the rule | Theorem |
|---|---|---|---|
| `1` | `+0` (bits `0`) | IEEE 754-2019 9.2.1 [7], C99 F.9.3.7 [8] | `log_one` |
| `+0`, `-0` | `-∞` (`0xFFF0000000000000`) | IEEE 754-2019 9.2.1 (with the divideByZero exception), C99 F.9.3.7 | `log_zero` |
| `+∞` | `+∞` | IEEE 754-2019 9.2.1, C99 F.9.3.7 | `log_pos_infinity` |
| negative, `-∞` included, other than `-0` | canonical NaN `0x7FF8000000000000` | IEEE 754-2019 9.2 (a quiet NaN outside the domain `[0, +∞]`, with the invalid exception), C99 F.9.3.7 | `log_negative` |
| NaN | canonical NaN | IEEE 754-2019 9.2 (a quiet NaN for a NaN operand), C99 F.9 paragraph 11, the deterministic profile of WebAssembly [9] | `log_nan` |

IEEE 754-2019 lists the logarithm among the recommended operations of clause 9.2, which a conforming implementation rounds correctly [7].  The one-step bound is weaker than correct rounding, and the port is not correctly rounded.  The theorem says nothing about the divideByZero and invalid exceptions or about `errno`, which the port does not compute.

## Algorithm

Arm's comment in `log_data.c` states the method [2]: write `x = 2^k z` with `z` in `[0x1.6p-1, 0x1.6p0)`, split that interval into `N = 128` subintervals, take a point `c` near the center of the subinterval that holds `z`, and use `log x = k ln 2 + log c + log (z/c)`, with `log (z/c) = log (1 + r)` for `r = z/c - 1` and `|r| < 1/256`.  A table gives `1/c` and `log c`, and a polynomial gives `log (1 + r)`.  Harrison, Kubaska, Story, and Tang describe the same reduction for the IA-64 logarithm, `ln x = ln (1/c) + ln (1 + r)` with a table indexed by the leading bits of `x` [6], and Tang published a table-driven logarithm in 1990 [5].

Each table entry holds `invc ≈ 1/c`, `logc ≈ log c`, and `c` as the sum `chi + clo` of two doubles.  Arm chose each `c` by trying the `±2^29` doubles around the inverse of the center as `invc` and keeping one for which `0x1.8p9 + logc` is exact, the rounding error of `z - chi - clo` is below `2^-66`, and the error of `logc` is below `2^-66` [2].  The first condition puts `logc` on the grid of `2^-43`, so that `k · ln2hi + logc` is exact, with `ln 2` split into a head `ln2hi` with trailing zeros and a tail `ln2lo` [2].  The second makes `r = (z - chi - clo) · invc` close to one rounding without fused multiply-add.

The main path forms `w = k · ln2hi + logc`, `hi = w + r`, and `lo = w - hi + r + k · ln2lo`, and returns `lo + r² A0 + r³ (A1 + r A2 + r² (A3 + r A4)) + hi`.  Arm's comment bounds its error by `0.5 + 2.06/N` units in the last place, plus the polynomial's error times `2^56` and 0.001 without fused multiply-add, for results above `2^-4` in magnitude [1], about 0.520 units in all.  Near 1 the absolute errors of `logc` and `r` would be large relative to `log x`, as Arm's comment notes for `|log x| < 2^-4` [2], so arguments from `1 - 2^-4` to below `1 + 0x1.09p-4` take a polynomial of degree 12 in `r = x - 1`, a subtraction that is exact there.  That path computes `r - r²/2` with `r` split into a head `rhi` of 26 bits, `rhi = r + 2^27 r - 2^27 r`, so that `rhi²` is exact, and Arm states about 0.507 units for it [1].

The guards on the top 16 bits of `x` handle the rest.  `x = 1` gives `+0`, both zeros give `-∞`, `+∞` gives `+∞`, and negative numbers, `-∞`, and NaN give `(x - x)/(x - x)`, which is NaN.  The code multiplies a subnormal argument by `2^52`, an exact product, and subtracts 52 from the exponent field of the result, so that the main path sees a normal word and the right `k`.

## Implementation

The source is Arm's `math/log.c` with the data of `math/log_data.c` and the error results of `math/math_err.c` [1, 2, 3].  The files carry `Copyright (c) 2018-2025, Arm Limited` (`log.c`) and `Copyright (c) 2018, Arm Limited` (`log_data.c`, `math_err.c`), under `SPDX-License-Identifier: MIT OR Apache-2.0 WITH LLVM-exception` [4], and the module docstring of [the implementation](Program.lean) repeats the notice.  The configuration is the one that `math/math_config.h` selects without fast fused multiply-add: `LOG_TABLE_BITS` 7, `LOG_POLY_ORDER` 6, `LOG_POLY1_ORDER` 12, `HAVE_FAST_FMA` 0, so the reduction reads `tab2`, and `WANT_ROUNDING` 1 [3].

The port uses the Verified dialect, the subset of Lean that [the Verified compiler](../../../../Verified/README.md) translates to WebAssembly with a correctness theorem.  `verified_compile compiled := [logNear1, logCore, logWith, log]` generates the module, whose functions are `alloc` (0), `release` (1), `logNear1` (2), `logCore` (3), `logWith` (4), and `log` (5).  The port writes each constant as `Float.ofBits` of the bit pattern of Arm's hexadecimal float, and the two tables are arrays of 256 words in data segments, borrowed at addresses 4096 and 6152.  `logWith` takes the tables as parameters, so that [the inverse hyperbolic functions](../Asinh/Program.lean) and [the Bessel functions](../Bessel/Program.lean) call it with `logTable` and `logTable2` where fdlibm calls its own `log`.

| C code | Port | Reason |
|---|---|---|
| 32-bit `top - 0x0010` against `0x7ff0 - 0x0010` | 64-bit comparison | The difference wraps for `top < 0x0010` in both widths and exceeds `0x7ff0 - 0x0010` either way, so the results agree.  The docstring of `logWith` records this. |
| `k = (int64_t) tmp >> 52`, an arithmetic shift | `tmp >>> 52` with the top 12 bits set when `tmp` is negative | The dialect's shift is logical. |
| `kd = (double) k` | `-(0 - k).toFloat` for a negative two's complement `k`, else `k.toFloat` | The dialect converts unsigned words. |
| `__math_divzero (1)` | `-1.0 / 0.0` | Expression that computes it in `math_err.c` [3]. |
| `__math_invalid (x)` | `(x - x) / (x - x)` | Expression that computes it, without `errno`. |
| `eval_as_double`, `WANT_ROUNDING` | identity, assumed 1 | WebAssembly arithmetic rounds to nearest, ties to even, and `log 1` returns `0.0`. |
| `__log_data` globals | parameters `tab` and `tab2`, read with `tab[i]!` | The tables are borrowed arrays of the module. |

| Constant | Bits | Value |
|---|---|---|
| `Ln2hi`, `Ln2lo` | `0x3FE62E42FEFA3800`, `0x3D2EF35793C76730` | `0x1.62e42fefa3800p-1`, `0x1.ef35793c76730p-45` |
| `A0` to `A4` | `0xBFE0000000000001`, `0x3FD555555551305B`, `0xBFCFFFFFFFEB4590`, `0x3FC999B324F10111`, `0xBFC55575E506C89F` | `N == 128 && LOG_POLY_ORDER == 6` polynomial |
| `B0` to `B10` | `0xBFE0000000000000` to `0xBFB5521375D145CD` | `LOG_POLY1_ORDER == 12` polynomial, `B0 = -1/2` |
| `OFF` | `0x3FE6000000000000` | `0x1.6p-1` |
| bounds of the path near 1 | `0x3FEE000000000000`, `0x3FF1090000000000` | `1 - 2^-4`, `1 + 0x1.09p-4` |
| split factor, subnormal scale | `0x41A0000000000000`, `0x4330000000000000` | `2^27`, `2^52` |

`logTable` is Arm's `__log_data.tab` for `N = 128`, with `invc` at word `2i` and `logc` at `2i + 1`, and `logTable2` is `__log_data.tab2`, with `chi` at `2i` and `clo` at `2i + 1`.  Both tables, 512 words in all, equal the `N = 128` sections of `__log_data.tab` and `__log_data.tab2` in `log_data.c` at the pinned commit, and the 23 constants above are the binary64 values of their expressions in `log.c` and `log_data.c` there.  `LogTables.checked_entries` and `checked_logs` check the 128 entries in the kernel, and `LogAccuracy.tableEntryOk` checks them natively: `chi + clo` against `1/invc` within `2^-100` relatively and `logc` against `log c` within `2^-66`, the bound of Arm's comment.

## Theorems

The theorems are in [the logarithm theorem module](LogTheorem.lean), [the main path module](LogMain.lean), and [the file module](LogFile.lean), in the namespaces `Library.Numerics.Float64.Log.LogTheorem`, `LogMain`, and `LogFile`.  `x` is a Lean `Float`, and a word is the `UInt64` bit pattern of a double.  The byte theorem uses `Wasm.Runs false`, which requires every run with enough fuel to return without a trap.

| Theorem | Statement |
|---|---|
| `LogMain.log_normal_within` | For a positive normal `x` outside `[15/16, 1 + 265/4096)`, `WithinSteps 1 (Real.log (value x.toBits)) (Log.log x).toBits`. |
| `LogMain.log_subnormal_within` | Same bound for a positive subnormal `x`. |
| `near1_within` | Same bound for `x` from `15/16` to below `1 + 265/4096`, other than 1. |
| `log_within_one` | Same bound for every finite `x` with positive value. |
| `log_one` | `log 1` has the bits `0`. |
| `log_zero` | `log (±0)` has the bits `0xFFF0000000000000`. |
| `log_pos_infinity` | `log (+∞)` has the bits `0x7FF0000000000000`. |
| `log_negative`, `log_nan` | A negative argument other than `-0`, `-∞` included, and a NaN give `Wasm.IEEE64.canonicalNaN`. |
| `ready_initial` | The module's initial store satisfies `Ready`: the allocator invariant, `logTable` borrowed at 4096, `logTable2` at 6152, and a memory cap of at most 65,535 pages. |
| `log_entry_call` | A call of function 5 from a store satisfying `Ready` returns, without a trap, the bits of `Log.log x` and leaves a store satisfying `Ready` in which every heap region keeps its bytes. |
| `log_bytes_accuracy` | `Log.compiled.module` encodes to bytes that decode to it, exports function 5 as `log`, starts in a `Ready` store, and every call from a `Ready` store returns the bits of `Log.log x`, within one step for finite `x` with positive value, and leaves a `Ready` store.  The statement covers every call in a sequence of calls to `log`. |
| `LogFile.log_file`, `log_file_decode` | `build/verified/log.wasm` holds `encode Log.compiled.module` and decodes to the module of `log_bytes_accuracy`. |

Each declaration of the three modules has a `#print axioms` line, and [the journal](../../../../devnotes.md#2026-10-10-logarithm-theorem-complete-track-log) records that each reports `[propext, Classical.choice, Quot.sound]`.  `tests/verified/run.sh` builds `Library.Numerics.Float64.Log.LogTheorem`, checks `LogFile.lean` against the `log.wasm` that it writes earlier in the same run, and fails unless both file theorems report exactly the three permitted axioms.  Its run of 2026-10-11 passed that check and printed the permitted report for every declaration of `LogMain` and `LogTheorem`.

Two modules serve the Bessel proofs.  `LogNearMain.core_near`, `normal_near`, and `subnormal_near` state the main path's error as a distance: the result is finite and within `u |log x| + 2^-59` of `log x`.  `LogNearAll.log_near` extends this to every finite `x` with positive value, with the bound `(6/5) u |log x| + 2^-59`.  These theorems report only the three permitted axioms.

## Proof

### Modules

The proof has nine modules in `Library/Numerics/Float64/Log/` above the implementation, besides the file module, and it reuses `ExpReductionBounds` for `ln 2`.  The table lists them by stage, in dependency order within each stage.  [The library aggregate](../../../../Library.lean) reaches `LogTheorem` through `Log2Theorem`, and `tests/verified/run.sh` builds `Library.Numerics.Float64.Log.LogTheorem` before it checks the file theorem.

| Stage | Modules | Content |
|---|---|---|
| Words | `LogCoreBits`, `LogBranches` | `logCore_eq` restates `logCore` through the reduced argument and the arithmetic after it.  The words of `i`, `k`, and `z` for an argument `E · 2^52 + f` modulo `2^64`, the exact value of `kd`, and the paths of `logWith` by argument bits. |
| Arithmetic after `r` | `LogCoreFinal` | `final_error`: `kd · ln2hi` and `kd · ln2hi + logc` are exact, and the other operations add at most `(5/4) 2^-61` before the final rounding. |
| Tables and polynomials | `LogTables`, `LogKernelPoly` | 128 entries checked in the kernel, and both polynomials against `log (1 + r)`. |
| Main path | `LogCoreStep`, `LogMain` | `core_within`, one step for every argument word that reaches `logCore`, and its use for normal and subnormal arguments. |
| Path near 1 and assembly | `LogNear1`, `LogTheorem` | Errors of `logNear1` proportional to `\|x - 1\|`, exceptional values, `Ready`, and byte theorem. |

### Error budget of the main path

A result `c` of a final addition with exact value `V` satisfies `|c - y| ≤ u |y| + (1 + u) |V - y|` for `u = 2^-53`.  [The relative step lemma](../../../../LeanExe/ProofKit/F64RelativeStep.lean), `F64RelativeStep.within_one_relative`, gives one step from `|c - y| ≤ (11/8) u |y|`, so the error before the final rounding may reach `(3/8) u |y|`.  On the main path the argument lies outside `[15/16, 1 + 265/4096)`, so `|log x| ≥ 6/100` (`LogCoreStep.log_away`) and the allowance is `(3/8) u (6/100)`, about `2.88 · 2^-60`.

| Term | Bound | Lemma |
|---|---|---|
| Rounding of `r = ((z - chi) - clo) invc`, with `z - chi` exact | `2^-60`, divided by `995/1000` for the derivative of `log (1 + r)` | `LogCoreStep.reduced_error` |
| `c · invc` against 1 | `2^-100` | `LogTables.checked_entries` |
| `logc` against `log c` | `2^-64` | `LogTables.log_center` |
| `ln2hi + ln2lo` against `ln 2`, times `\|k\| ≤ 1075` | `1075 · 2^-91` | `LogCoreStep.ln2_error` |
| Polynomial against `log (1 + r)` for `\|r\| ≤ 1/256` | `\|r\| (17/32) 2^-54 ≤ (17/32) 2^-62` | `LogKernelPoly.core_kernel_error` |
| Operations after `r`, before the final rounding | `(5/4) 2^-61` | `LogCoreFinal.final_error` |
| Total, as `LogCoreStep.core_within` sums it | about `1.83 · 2^-60` against `2.88 · 2^-60` | `LogCoreStep.target_close` |

The terms use about 63 percent of the allowance, and the rounding of `r` and of `w - hi` dominate.  The proof does not use the exactness of Arm's two-sum steps: tracking `w - hi` and `(w - hi) + r` with one unit of roundoff each costs `2^-61`, which the allowance absorbs.  The exact steps it needs are `kd · ln2hi`, `kd · ln2hi + logc`, whose relative error would otherwise reach a unit of `log x` for large `k`, and `z - chi`.

### Error budget of the path near 1

Let `ρ = |x - 1|`, between `2^-53` and `265/4096`.  `x - 1` is exact on the grid of `2^-53`, and [the error tracker](../../../../LeanExe/ProofKit/F64ErrorTrack.lean) carries every later operation with an error proportional to `ρ`, using `ρ² ≤ ρ/15`.  `LogNear1.near1_error` bounds the sum before the final rounding by `(1/15 + 1/13) u ρ`, about `0.144 u ρ`, against `r · eval near1Kernel r`, and `LogKernelPoly.near1_kernel_error` adds `(15/16) 2^-62 ρ`, about `0.002 u ρ`.  `LogTheorem.log_near_lower` gives `|log x| ≥ (15/16) ρ`, so the allowance is `(3/8)(15/16) u ρ`, about `0.352 u ρ`, and the errors use about 41 percent of it.  The two largest terms are the roundings of `rhi · rhi` and of `r - hi`, each about `u ρ/30`.  The split into `rhi` and `rlo` needs no exactness argument: the identity `rhi² + (r - rhi)(rhi + r) = r²` holds for the computed `rhi`, and only the roundings of `rlo` and of the product enter.

### Shared modules

The proof uses ProofKit modules, including the arithmetic chains that prove Lean's `Float` and `Float32` operations equal to Talos's functions.  The modules specific to the error analysis are [the signed reference](../../../../LeanExe/ProofKit/F64SignedRounding.lean), [the relative step lemma](../../../../LeanExe/ProofKit/F64RelativeStep.lean), [the error tracker](../../../../LeanExe/ProofKit/F64ErrorTrack.lean), [exact products](../../../../LeanExe/ProofKit/F64ExactProduct.lean), [grid exactness](../../../../LeanExe/ProofKit/F64GridExact.lean), [one step against the full reference](../../../../LeanExe/ProofKit/F64FullStep.lean), [the kernel-checked polynomial bound](../../../../LeanExe/ProofKit/PolyBound.lean), and [Taylor remainders](../../../../LeanExe/ProofKit/TaylorRemainder.lean), whose logarithm bound comes from Mathlib's `Real.abs_log_sub_add_sum_range_le` [10].  This proof added `F64RelativeStep`, `F64ErrorTrack`, `F64ExactProduct`, and [the borrowed-table frame](../../../../LeanExe/ProofKit/BorrowedKept.lean) to ProofKit.  `ExpTheorem.borrowed_kept` now applies the shared `BorrowedKept.borrowed_kept` theorem.

### Kernel-checked facts

| Fact | Declaration |
|---|---|
| For each of the 128 entries: finiteness, `\|c · invc - 1\| ≤ 2^-100`, `\|(z - c) invc\| ≤ 0.0039` over the subinterval, `chi` on the grid of `2^-53` in `[1/2, 3/2]`, `\|clo\| ≤ 2^-50`, `logc` on the grid of `2^-43` with `\|logc\| ≤ 3/8` | `LogTables.checked_entries` |
| For each entry, the Taylor polynomials of degree 19 of `exp` at `logc ∓ 2^-64`, with their remainders, bracket `c`, so `\|logc - log c\| ≤ 2^-64` | `LogTables.checked_logs` |
| Both polynomials against the Taylor polynomial of `log (1 + r)/r` on their intervals, by `PolyBound.check` | `LogKernelPoly.core_check`, `near1_check` |
| `ln2hi + ln2lo` within `2^-92` of the split of `ln 2` from `ExpReductionBounds` | `LogCoreStep.split_close` |
| Values and bounds of the constants | `LogCoreFinal.constants`, `constant_bounds`, `LogNear1.near1_constants`, `near1_bounds` |
| Function 5 is exported as `log`, and the file's bytes equal the encoder's | `LogTheorem.log_export`, `LogFile.log_file` |

### History

The journal sections of [the main path](../../../../devnotes.md#2026-10-10-logarithm-theorem-main-path-track-log) and [the complete theorem](../../../../devnotes.md#2026-10-10-logarithm-theorem-complete-track-log) record the failed runs.  The assembly of the main path first failed four times because `set` abstractions did not match terms created after them and `nlinarith` reached the recursion limit on products with `2^100`, so the proof divides it into a lemma of real arithmetic, `target_close`, a word equation, `core_word`, and `core_within`.  One theorem for the whole path near 1 ran past 200,000 heartbeats, and the proof divides it into `poly_error`, `split_error`, and `near1_error` over named words.  `ready_initial` needed `maxRecDepth` to compute the address of the second table.

## Tests

[The accuracy check](../../../../tests/TestSupport/Numerics/LogAccuracy.lean) compares `Log.log` natively with the double nearest to `log x` computed by [the integer reference](../../../../tests/TestSupport/Numerics/Reference.lean), and it fails at the first result more than one step away.  It first checks every table entry against its center.  Its 340,076 arguments are 100,001 evenly spaced values from 0 to 20, 100,001 from 0.9 to 1.1, 100,000 hashed positive values over all exponents, 40,000 doubles on both sides of 1 at hashed distances of up to `2^36` units, the five doubles at and around each of 11 edges of the paths, the binades, and the subnormals, nine special and negative values, and the ten inputs of `WorstCases.log`.  Those ten are the double-precision inputs that give the largest known `log` errors in Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [11], whose Table 3 lists 0.520 units for GNU libc 2.44, Musl, and the Arm Performance Library and 0.946 for FreeBSD 15.1.

In a run of `tests/verified/run.sh`, all 340,076 results lie within one step of the reference, and 234 of them differ from it, so the largest measured distance equals the proved bound.  The C library of the test run lies within one step at the same arguments, with 233 results unequal to the reference.  The reference's docstrings state its truncation errors, below `2^-230` relative, and no theorem proves them.  Such an error can change the reference only for an exact value within that distance of a midpoint between two doubles, where the reference may name the other double beside the midpoint.

## Limits

The theorem is about Talos's semantics of WebAssembly.  It trusts the Talos interpreter, `Module.initialStore`, and the decoder `Wasm.Encoding.decode`, as [the design notes](../../../../docs/design.md#scope-of-the-theorem) record, and the file theorem trusts the elaborator `binary_file%`, which reads `log.wasm`.  Talos implements the deterministic profile, in which every NaN result is canonical [9], and an engine outside that profile, such as a browser, may return other NaN bits.

The argument is `x.toBits` for a Lean `Float`, and every NaN `Float` has the canonical bits, so the theorem covers only the canonical NaN among the NaN words a WebAssembly caller can pass.  For another NaN word the compiled code reaches the guard `top &&& 0x7ff0 == 0x7ff0` and returns `(x - x)/(x - x)`, which is the canonical NaN in Talos, but no theorem states it.  `log_bytes_accuracy` covers sequences of calls to `log` only, and a host that calls another export of the module or writes its memory, which holds the two tables, between calls needs a theorem that the action preserves `Ready`.

## References

1. Arm Limited, optimized-routines, [`math/log.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/log.c).  Copyright (c) 2018-2025, Arm Limited, MIT OR Apache-2.0 WITH LLVM-exception.
2. Arm Limited, optimized-routines, [`math/log_data.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/log_data.c), same commit: the tables, the polynomials with their stated errors, and the comment that describes the algorithm and the choice of the centers.
3. Arm Limited, optimized-routines, [`math/math_err.c`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/math_err.c) and [`math/math_config.h`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/math/math_config.h), same commit.
4. Arm Limited, optimized-routines, [`LICENSE`](https://github.com/ARM-software/optimized-routines/blob/503fafe311c177de0e571c458c7c337b1ca5f522/LICENSE), same commit.
5. P. T. P. Tang, "Table-driven implementation of the logarithm function in IEEE floating-point arithmetic", *ACM Transactions on Mathematical Software* 16(4):378–400, December 1990, [doi:10.1145/98267.98294](https://doi.org/10.1145/98267.98294).  Crossref's record gives these bibliographic data.  The paper's text is not checked here, and this document attributes to it nothing beyond its title.
6. J. Harrison, T. Kubaska, S. Story, and P. T. P. Tang, ["The Computation of Transcendental Functions on the IA-64 Architecture"](https://www.cl.cam.ac.uk/~jrh13/papers/itj.pdf), *Intel Technology Journal*, Q4 1999.  Its sections on reduction and on `Ln` describe `ln x = ln (1/frcpa (x)) + ln (1 + r)` with a table of `ln (1/frcpa)` and a minimax polynomial for `ln (1 + r) - r`.
7. IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, 2019, [doi:10.1109/IEEESTD.2019.8766229](https://doi.org/10.1109/IEEESTD.2019.8766229).  This document cites clause 4.3.1 (rounding to nearest), clause 9.2 with Table 9.1 (the domain of `log`, correct rounding, NaN operands), and clause 9.2.1 (special values).
8. ISO/IEC 9899:1999, *Programming languages — C*, Annex F, clauses F.9 and F.9.3.7, as consolidated in WG14 committee draft [N1256](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1256.pdf) (September 7, 2007).
9. WebAssembly Community Group, *WebAssembly Core Specification*, version 3.0, appendix [Profiles](https://webassembly.github.io/spec/core/appendix/profiles.html): in the deterministic profile, "All NaN values generated by floating-point instructions are canonical and positive."
10. The Mathlib Community, Mathlib, [`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`](https://github.com/leanprover-community/mathlib4/blob/85e3a25e006c35636f0e53b0e9296caca2685bc0/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean), `Real.abs_log_sub_add_sum_range_le`.
11. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 (largest known errors in double precision) and Tables 4 to 11 (the inputs).
