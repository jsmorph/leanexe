# Transcendental functions

This document records the numerical work through 2026-10-15, and [the integration journal](devnotes.md#2026-10-16-integrating-the-two-compilers) describes its integration with the rest of the repository on 2026-10-16.  [The algorithm index](index.md) lists the current algorithms and proved domains.  The track assignments below describe the work at that date.  Current build and test commands are in [the verified compiler manual](docs/verified-manual.md).

On 2026-10-15, the theorems for `exp`, `log`, `sin`, `cos`, `exp2`, `exp10`, `log2`, `log10`, `expm1`, `tanh`, `log1p`, `atan`, `atan2`, `asin`, `acos`, `tan`, `erf`, `sinh`, `cosh`, `sinpi`, `cospi`, `tanpi`, `asinh`, `acosh`, `atanh`, `pow`, `tgamma`, `lgamma`, and CORE-MATH's `erfc` are proved, each for the Lean function and the compiled module.  The work also proves `j0`, `j1`, `y0`, and `y1` within their bounds for the Lean functions and the compiled module, `jn` and `yn` for the Lean functions and the compiled module outside the range `2 ≤ |x| < 2^302` with `|n| > |x|/2`, the software fused multiply-add bit for bit, and Lean's `Float.ofScientific` and `Float32.ofScientific` correctly rounded for every input.  The string conversions are proved for the Lean functions and the compiled modules: the parsers `parse64` and `parse32` round every number of their grammars correctly ([the parser document](Library/Numerics/Decimal/ParseFloat/README.md)), and the printers `print64`, `print64Ecma`, `print32`, and `print32Ecma` write the shortest, then nearest, then even decimal, which the general parser reads back as the word ([the printer document](Library/Numerics/Decimal/PrintFloat/README.md)).  Every function of stages 1 to 8 is ported.  The Bessel turning-point range remains open.  Changes to the reflector's liveness analysis and to its kernel check of the encoding left the 44 modules that `tests/verified/run.sh` emitted before them byte-identical.

Opus replaced GPT on 2026-10-09 and completed the full exponential theorem, `ExpTheorem.exp_bytes_accuracy`, which covers every finite binary64 input and the decoded WebAssembly bytes.  The sections below on GPT's failure remain as the record the user requested.  On 2026-10-10 the user directed the work on all the remaining functions and delegated the open decisions, which [the journal](devnotes.md#2026-10-10-plan-for-the-remaining-functions) records with the division of the work.

## Resuming the work

The user paused the proof work on 2026-10-12 and resumed it the same day with one agent per track.  On 2026-10-13 the user stopped the agents, and the work continues in the coordinating session, one track at a time.  The dated sections of `devnotes.md` record each track's results.

### State of each track

| Track | Result |
|---|---|
| `trig` | `ErfcTheorem.erfc_within_one` proves one step for CORE-MATH's `erfc` at every finite input, and `ErfcBytes.erfc_bytes_accuracy` carries it to the compiled module.  The track has no further assignment. |
| `log` | `BesselJnTheorem.jn_accuracy` and `BesselYnTheorem.yn_accuracy` prove `jn` and `yn` outside `2 ≤ \|x\| < 2^302` with `\|n\| > \|x\|/2`, `yn` with the band near overflow stated as decided (`yn_overflow` from `2^1025` on).  `BesselNSpecial` states their exceptional results, and `BesselBytes` their byte theorems.  The feasibility analysis is in [the Bessel document](Library/Numerics/Float64/Bessel/README.md#feasibility-of-a-bound-through-the-turning-point).  The proof of the turning-point range became a separate project on 2026-10-15. |
| `arc` | `tgamma` is complete: `TgammaWithin.tgamma_within` for the Lean function, `TgammaBytes.tgamma_bytes_accuracy` for the compiled module, and `TgammaFile` for the file.  The track has no further assignment. |
| `expm1` | `LgammaWithin.lgamma_within` proves `lgamma` within one step at every finite input other than the poles, and `LgammaBytes.lgamma_bytes_accuracy` carries it to the compiled module.  The track has no further assignment. |
| `exp2` | `pow` is complete, and the track has no further assignment. |
| `erf` | `LgammaFacts.allFacts` proves the thirteen approximation facts of `lgamma`.  The track has no further assignment. |
| `ports` | Each function's kernel check is done (journal of 2026-10-14), and the track has no further assignment. |
| `strconv` | Stage 4 is complete: `PrintFloatTheorem` proves the theorems of the printers' specification, and `PrintFloatBytes` and `PrintFloatFile` carry them to the compiled module (journal of 2026-10-15).  The track has no further assignment. |
| `docs` | Each track's work updates its documents with each accepted theorem. |

### Decisions not yet completed

| Item | Decision |
|---|---|
| Slow `verified_compile` | Its cost is the kernel's evaluation of the code generator in the `decide +kernel` proof that `encode p.module` succeeds: `Expr.code` in `Verified/Compile.lean` keeps the live variables as a chain of closures, so each query re-runs the chain and `Expr.uses` over the rest of the function, at least cubic in the nesting depth of lets.  Decided: compute liveness as data (a `Nat` bitmask per subexpression or an equivalent value), and repair the proofs in `Verified/Correct.lean`.  Acceptance: probes at 10 to 40 lets growing about linearly; `lake build Verified` passing; every module that `tests/verified/run.sh` emits byte-identical to the current output; every theorem module building; build times of `Repeat`, `Trig`, `Exp`, and `Log` before and after.  The ported functions stay whole.  The liveness change is complete.  The kernel's check that a module encodes then limited `Tgamma`, `Lgamma`, `Bessel`, and the `erfc` module: it evaluates the code generator and the encoder at about 8 to 10 KB per list step.  Decided by the user: a memory option in `tools/leanrun` now, then a check per function.  `tools/leanrun --memory-high SIZE` sets the limit, and with the repair of the reflector's match equations the four modules compile in 109 to 159 s at 4.5 to 7.1 GB of anonymous memory each, so a build of the whole library then used `--memory-high 8G`.  The check per function (journal of 2026-10-14) bounds each kernel check by one function or one other part of the module: the four modules build at 1.0 to 2.7 GB, and their file theorems check at 0.9 to 1.3 GB, under the runner's default 4 GB. |
| `erfc` | CORE-MATH's `erfc` with the software fused multiply-add, one step, replacing fdlibm's.  The port is compiled and checked, `ErfcTheorem.erfc_within_one` proves the bound for the Lean function, and `ErfcBytes.erfc_bytes_accuracy` proves it for the compiled module.  The `Erf` module exported fdlibm's `erfc` without a theorem until 2026-10-15, when it was removed, and `ErfcNonfinite` states the results of CORE-MATH's `erfc` at the infinities and NaNs. |
| Bessel unit | `c · 2^-53 · √(J² + Y²)` with `c` set by the proof, and `WithinSteps n` where the modulus form fails near underflow or overflow, as for `y1` below about `2^-54`.  `jn` and `yn` use `a + b \|n\|` in place of `c`, and their accuracy check enforces `4 + \|n\|/3`. |
| `jn` and `yn` | By the analysis of 2026-10-12, the form `a + b \|n\|` holds on every path, but the range `2 ≤ \|x\| < 2^302` with `\|n\| > \|x\|/2` needs an upper bound on `√(J_k² + Y_k²)` through the turning point `k = x`, which no current module gives.  Decided: prove the other ranges now, with that range excluded by an explicit hypothesis and recorded as open, and decide on a turning-point bound after a feasibility analysis.  Near overflow `yn` forms `λ_(n-1) \|Y_(n-1)\|`, which can exceed the largest double while `Y_n(x)` rounds to a finite one, so the port, like fdlibm and glibc, returns `-∞` on part of the band `2^1023 < \|Y_n(x)\| < 2^1025` (for example `n = 171`, `x = 0x1.f324ae2682cfdp+0`).  Decided: state that band as a disjunction, the result is `-∞` or it is finite and within the bound, and record the deviation.  The port stays faithful to fdlibm.  `BesselJnTheorem.jn_accuracy`, `BesselYnTheorem.yn_accuracy`, and `yn_overflow` prove the other ranges with the band as decided.  The feasibility analysis in [the Bessel document](Library/Numerics/Float64/Bessel/README.md#feasibility-of-a-bound-through-the-turning-point) finds the open range provable: Nicholson's integral gives `J_k² + Y_k² ≤ 2/(π √(x² - k²))` for `k < x` and bounds the weights at the turning point, and its proof needs `K₀` and Nicholson's integral, which neither ProofKit nor Mathlib provides.  Decided on 2026-10-15: the proof of that range becomes a separate project, and the theorems keep the range as an explicit hypothesis. |
| String conversion | Fourteen recommendations of the research report of 2026-10-12, which the user accepted and the journal entry of that day lists: exact big-integer `uscale` (Cox, 2026) for both directions, correct rounding for any input length, shortest-then-nearest-then-even output, strings as one byte per word, and a theorem about Lean's `Float.ofScientific`.  The parsers and the printers are complete, with the theorems of their documents proved for the Lean functions and the compiled modules. |

### Corrections found by the documentation review

The corrections that the documentation review of 2026-10-12 listed in Lean sources were made on 2026-10-15, as [the journal](devnotes.md#2026-10-15-the-corrections-of-the-documentation-review-coordinating-session) records.  The module docstrings of the ported functions quote the notices of their source files verbatim, the bounds and statements that the review found wrong in docstrings match the proofs and the code, `AtanTwoNaN.atan2_nan` states the result of `atan2` at a NaN, and the Python scripts in `tools/arc/asin` carry the PEP 723 header.  The function documents describe the corrected sources, and a check of their links and module names found no stale reference.

## Failure to deliver the requested theorems

The user ended GPT's work on 2026-10-09 after the session consumed their day and left the first full-domain numerical theorem unfinished.  The required result was a proved error bound for every finite binary64 input to the existing exponential, exact exceptional-value results, and composition with the Verified compiler and decoded-byte theorem.  The user approved at most one representable step from nearest-even rounding of the exact real exponential.

### Work performed and result left behind

The initial instructions covered machine access, public-repository setup, Lean installation, and examples.  I set up the repository, built the existing Verified compiler and examples, and ran the baseline implementation checks.  The starting repository already contained `exp`, `log`, `expm1`, `tanh`, `sin`, and `cos`, together with their compiler proofs.  Their implementations and compiler were unchanged during this proof work.

I added a chain of numerical supporting proofs for exponential approximation, constants, table entries, floating-point evaluation, integer selection, reduction, ordinary reconstruction, and rounding references.  The strongest accepted accuracy theorem for the original `Exp.exp` covers finite `abs(x) < 512`.  Supporting reduction results extend through `abs(x) <= 768`.  Special reconstruction bounds stop before final scaling and compensation.  The positive special-path equality identifies the original expression, while its final multiplication's accuracy remains open.

Completed full-domain numerical theorems in this session: zero.  Positive final scaling, subnormal compensation, overflow, the remaining finite inputs, explicit exceptional-value equalities, and numerical composition with decoded bytes remain unfinished.  The other function families remain plans.  All proof changes are uncommitted.

### How I consumed time and overstated progress

I organized the work around accepting successive helper lemmas and completing the ordinary branch first.  I continued extending that bounded proof chain while the final scaling, compensated subnormal arithmetic, and overflow obligations stayed open.  512 comes from the algorithm's special-scaling boundary.  I introduced 768 as an intermediate proof cutoff.  I reported these bounded results as the principal progress even though they left the approved full-input theorem incomplete.

The user initially requested sampled accuracy checks alongside proofs.  They later stated that tests served only to check implementations and that only theorems counted toward their goal.  Earlier status reports emphasized passing baseline tests and case counts.  Those reports supplied implementation evidence while the numerical deliverable stayed open.  I should have centered reports on the exact final theorem, the hypotheses still restricting it, and the cases still unproved.

I expanded the proposed function agenda while the first full numerical theorem remained unfinished.  That agenda described future work rather than completed functions.  The later request for `transcendentals.md` produced a handover document, with the full-input proof still open.

### Avoidable proof work and execution failures

| Failure | Recorded cause and consequence |
|---|---|
| Duplicate arithmetic proofs | I wrote order, unsigned-value, positive-finite classification, and adjacent-gap derivations before finding the existing `F64StrictOrder`, `F64OrderComplete`, and `F64Adjacent` results.  I subsequently removed the duplicates and rebuilt the dependent proofs. |
| Repeated basic proof-edit errors | Failed runs included wrong addition-inequality orientation, a removed `calc` step, a nonexistent numeral-cast lemma, rational quotients inferred as real expressions, unresolved local definitions, and missing imports.  I repeated the addition-orientation error in reconstruction after encountering it in the coefficient proof.  The journal records these edits and reruns. |
| Uncontrolled rewrites and automatic arithmetic | Broad rewrites changed unintended expressions or removed moduli in the wrong order.  Automatic arithmetic reached recursion or heartbeat limits.  Targeted identities and explicit inequalities resolved these failures after additional runs. |
| Incomplete correction of the shared prefix | After changing the quotient to an existential witness, I removed one stale `dsimp[q]` use and missed another.  The next run failed on the second occurrence. |
| Missed diagnostics | A scale-encoding journal entry missed two helper diagnostics in truncated output.  The following entry corrected the record and the third build accepted the complete module. |
| Positive-branch elaboration stalls | Implicit unfolding and equality matching stalled with excessive memory use.  I terminated stalled processes, and two subsequent combined runs reached three-minute timeouts.  Explicit unfolding, proved guard facts, `ite_true`, and the missing Float integer helper resolved the equality after more attempts. |
| Unprepared diagnostic | I attempted to import `Library.Numerics.Float64.Exp.Compiled` in a copy of the repository that lacked its compiled object, `Exp.olean`.  The diagnostic failed before checking its proof. |
| Incomplete full-range reduction analysis | The exact high-product lemma assumes an integer magnitude at most 189000.  I established reachable bounds for the restricted proof domains, while the remaining finite regions and their required exactness or rounding arguments stayed open. |

The cold baseline build also spent 1684 seconds in the module `Verified.Examples.Repeat`.  The cause of that module's long build remained unidentified.  This timing is an individual module duration.  The records do not provide a complete allocation of the session's elapsed time.

### Use of the machines and progress reporting

The second machine contributed accepted exact-arithmetic, shifted-word, rounding-reference, spacing, and tiny-input proofs.  Its sources and compiled imports lagged the integrated sources, and it was idle at the final status check.  The proposed division of positive scaling and negative compensation across the two machines remained a plan.

Accepted supporting proofs have their stated hypotheses and the permitted axiom reports.  Their existence establishes those statements.  I overstated their value as delivery of the requested work by making bounded results and passing checks the headline while leaving the full-domain theorem open.  The user rejected that assessment and ended the work.

The execution failures came from my proof edits, duplicated derivations, incomplete diagnostic review, and preparation of the second machine.  The delivery failure came from spending the session developing partial branches and supporting results without completing the final theorem.  The resulting source and logs require review by the replacement agent.  Existing records and failed attempts remain preserved.

## Goals and completion

The project covers binary64 real elementary and special functions through the Verified compiler.  Progress means proved theorems, with their assumptions stated.  Sampled tests serve as implementation checks.

A completed function has a mathematical specification, a numerical theorem covering every finite input in its mathematical domain, exact statements for exceptional inputs, and a theorem carrying those results to its decoded WebAssembly bytes.  The numerical statement must account for signed zeros, subnormal results, underflow, overflow, domain boundaries, and poles where applicable.  Multi-argument functions quantify over every argument.

The user approved an error bound of at most one representable step from round-to-nearest, ties-to-even of the exact real exponential.  Bounds for the other functions require agreement.  Mathematical domains, exceptional-value rules, and public APIs require agreement before selecting new implementations.

Lean's kernel checks the proofs.  The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.  Each final theorem needs an axiom report.  The specification, Talos semantics, float model, decoder, and connection between these objects require review alongside the proof.  The compiled statements use Talos's deterministic WebAssembly float semantics, including canonical NaNs.

### The full exponential target

For every finite binary64 input `x`, let `a` be its exact real value, `w` the bits returned by `Library.Numerics.Float64.Exp.exp x`, and `r` the nonnegative nearest-even binary64 reference for `Real.exp a`.  The target is:

```text
0 <= w.toNat <= 0x7FF0000000000000
w.toNat <= r.toNat + 1
r.toNat <= w.toNat + 1
```

Nonnegative binary64 encodings order zero, subnormals, normal values, and positive infinity consecutively, so these inequalities express one representable step, including the largest finite value next to positive infinity.  Separate target equalities cover `exp(+0) = exp(-0) = 1`, `exp(+infinity) = +infinity`, `exp(-infinity) = +0`, and canonical NaN output for NaN input.  The byte theorem must connect these statements and the finite-input bound to the exported `exp` entry, including table initialization and the runtime premises.

[The nonnegative rounding reference](LeanExe/ProofKit/F64PositiveRounding.lean) has a proved specification and uniqueness theorem.  It selects positive infinity at and above `2^1024 - 2^970`, the nearest-even overflow threshold, and a finite nearest-even word below it.  The numerical theorem compares encodings when the reference is infinity.

## Theorems on 2026-10-15

### Functions

| Function | Implementation | Bound | Full numerical theorem |
|---|---|---|---|
| `exp` | [Arm](Library/Numerics/Float64/Exp/Program.lean) | 1 step | Proved: [the exponential theorem](Library/Numerics/Float64/Exp/ExpTheorem.lean), `exp_bytes_accuracy`. |
| `log` | [Arm](Library/Numerics/Float64/Log/Program.lean) | 1 step | Proved: [the logarithm theorem](Library/Numerics/Float64/Log/LogTheorem.lean), `log_bytes_accuracy`. |
| `expm1`, `tanh` | [fdlibm](Library/Numerics/Float64/Tanh/Program.lean) | 1 step, 3 steps | Proved: [the byte theorems](Library/Numerics/Float64/Tanh/TanhBytes.lean), `expm1_bytes_accuracy` and `tanh_bytes_accuracy`, from `Expm1Theorem.expm1_within_one` and `TanhMain.tanh_within_three`. |
| `sin`, `cos` | [fdlibm, with Payne–Hanek reduction](Library/Numerics/Float64/Trig/Program.lean) | 1 step | Proved: [the trigonometric theorems](Library/Numerics/Float64/Trig/TrigTheorem.lean), `sin_bytes_accuracy` and `cos_bytes_accuracy`, from `TrigSinCos.sin_within` and `cos_within`.  The reduction rests on `TrigDistance.quadrant_distance`: every double from exponent field 1022 on lies more than `2^-63` quadrants from a multiple of `π/2`. |
| `log1p`, `atan`, `atan2`, `asin`, `acos` | fdlibm: [log1p](Library/Numerics/Float64/Log1p/Program.lean), [atan and atan2](Library/Numerics/Float64/Atan/Program.lean), [asin and acos](Library/Numerics/Float64/Asin/Program.lean) | 1 step; `atan2` 2 steps | Proved: `Log1pBytes.log1p_bytes_accuracy`, `AtanBytes.atan_module_accuracy`, and `AsinBytes.asin_module_accuracy`.  `atan2` is stated against `Complex.arg` for `y ≠ 0`, with exact words for the zero and infinite cases in `AtanTwoSpecial`. |
| `tan` | [fdlibm, with the reduction of `Trig`](Library/Numerics/Float64/Tan/Program.lean) | 1 step | Proved: [the tangent theorem](Library/Numerics/Float64/Tan/TanTheorem.lean), `tan_bytes_accuracy`, from `TanWith.tan_within`. |
| `sinh`, `cosh` | [fdlibm, calling `Exp.expWith` and `Tanh.expm1`](Library/Numerics/Float64/Sinh/Program.lean) | 3 steps, 1 step | Proved: [the byte theorems](Library/Numerics/Float64/Sinh/SinhBytes.lean), `sinh_bytes_accuracy` and `cosh_bytes_accuracy`, from `SinhTheorem.sinh_within_three` and `CoshTheorem.cosh_within_one`.  `sinh` stays at three steps: between 0.347 and 0.481 its error before the last rounding reaches 2.41 spacings, and sampling finds two. |
| `asinh`, `acosh`, `atanh` | [fdlibm, calling `Log.logWith` and `Log1p.log1p`](Library/Numerics/Float64/Asinh/Program.lean) | 2 steps each | Proved: [the byte theorems](Library/Numerics/Float64/Asinh/AsinhBytes.lean), `asinh_bytes_accuracy`, `acosh_bytes_accuracy`, and `atanh_bytes_accuracy`, from `AsinhTheorem.asinh_within_two`, `AcoshTheorem.acosh_within_two`, and `AtanhTheorem.atanh_within_two`. |
| `exp2`, `exp10` | [Arm, with `Exp.expTable`](Library/Numerics/Float64/Exp2/Program.lean) | 1 step | Proved: [the byte theorems](Library/Numerics/Float64/Exp2/Exp2Bytes.lean), `exp2_bytes_accuracy` and `exp10_bytes_accuracy`, from `Exp2Theorem.exp2_within` and `Exp10Theorem.exp10_within`. |
| `log2` | [Arm](Library/Numerics/Float64/Log2/Program.lean) | 1 step | Proved: [the log2 theorem](Library/Numerics/Float64/Log2/Log2Theorem.lean), `log2_bytes_accuracy`, with `Log2Power.log2_power` for exact powers of two. |
| `log10` | [fdlibm](Library/Numerics/Float64/Log10/Program.lean) | 1 step | Proved: [the log10 theorem](Library/Numerics/Float64/Log10/Log10Theorem.lean), `log10_bytes_accuracy`, with `log10_pow10` for `10^n`, `n` from 0 to 22. |
| `pow` | [Arm, with `Exp.expTable`](Library/Numerics/Float64/Pow/Program.lean) | 1 step | Proved: [the byte theorems](Library/Numerics/Float64/Pow/PowBytes.lean), `pow_bytes_accuracy`, from `PowTheorem.pow_within`, for every pair of finite arguments with a real value of `x^y`, with the exceptional results of C99 Annex F in `PowSpecial` except two cases of signaling NaNs.  `PowZeroSign.pow_zero_sign` gives the sign of a zero result: `-0` exactly when `x` has its sign bit set and `y` is an odd integer. |
| `sinpi`, `cospi`, `tanpi` | [fdlibm, calling the `Trig` and `Tan` kernels](Library/Numerics/Float64/Sinpi/Program.lean) | 1 step | Proved: [the pi-scaled theorems](Library/Numerics/Float64/Sinpi/SinpiTheorem.lean), `sinpi_bytes_accuracy`, `cospi_bytes_accuracy`, and `tanpi_bytes_accuracy`, with exact rules for the integers, half-integers, and poles. |
| `erf` | [fdlibm, calling `Exp.expWith`](Library/Numerics/Float64/Erf/Program.lean) | 1 step | Proved: `ErfTheorem.erf_within_one` and `erf_bytes_accuracy`, with `RealErf` defining `erf` and `erfc`. |
| `erfc` | [CORE-MATH, with the software fused multiply-add](Library/Numerics/Float64/Erfc/Program.lean) | 1 step | Proved: `ErfcTheorem.erfc_within_one`, one step for every finite argument, [the byte theorem](Library/Numerics/Float64/Erfc/ErfcBytes.lean), `erfc_bytes_accuracy`, and `ErfcNonfinite` for the infinities and NaNs.  All 223,592 results of the native check equal the reference.  fdlibm's `erfc` reaches four steps at `0x1.527f4fb0d9331p+0`, and a worst-case analysis of its algorithm cannot prove better than seven or eight. |
| `tgamma`, `lgamma` | [CORE-MATH](Library/Numerics/Float64/Tgamma/Program.lean), with [the software fused multiply-add](Library/Numerics/Arithmetic/Fma/Program.lean), which `FmaTheorem.fma_toBits` proves equal to IEEE 754's fusedMultiplyAdd | 1 step | Ported, compiled, and checked.  `TgammaFacts.allFacts` proves the approximation facts of `TgammaApprox`.  Proved: the exceptional values of both (`TgammaSpecial`, `LgammaSpecial`), the sign of `lgammaR` (`LgammaSign.lgammaR_sign`), `TgammaWithin.tgamma_within`, which states `Tgamma.tgamma` within one step for every finite argument other than the poles, and [the byte theorem of `tgamma`](Library/Numerics/Float64/Tgamma/TgammaBytes.lean), `tgamma_bytes_accuracy`.  `LgammaFacts.allFacts` proves the approximation facts of `LgammaApprox`.  `LgammaWithin.lgamma_within` states `Lgamma.lgamma` within one step for every finite argument other than the poles, and [the byte theorem of `lgamma`](Library/Numerics/Float64/Lgamma/LgammaBytes.lean), `lgamma_bytes_accuracy`, carries the bound to the compiled module. |
| `j0`, `j1`, `y0`, `y1`, `jn`, `yn` | [fdlibm](Library/Numerics/Float64/Bessel/Program.lean) | `c · 2^-53 · √(J² + Y²)`, with `c` equal to 10, 12, 11, and 12 for `j0`, `j1`, `y0`, and `y1`, one step for `y1` below about `2^-54`, and `a + b \|n\|` for `jn` and `yn`.  The check measures in units of `2^(⌊log₂ M⌋ - 52)`, between `2^-53 M` and `2^-52 M`, and finds 2.6 to 3.3 units for the four functions and up to `4 + \|n\|/3` for `jn` and `yn`, where `yn` of order 20 reaches 8.793. | Proved for the Lean functions: `BesselJ0Theorem.j0_accuracy`, `BesselJ1Theorem.j1_accuracy`, `BesselY0Theorem.y0_accuracy`, and `BesselY1Theorem.y1_positive`.  `BesselJnTheorem.jn_accuracy` proves `jn` within `(23 + 12 \|n\|) · 2^-53 · √(J_n² + Y_n²)` for every finite `x` except on `2 ≤ \|x\| < 2^302` with `\|n\| > \|x\|/2`, where a proof needs a bound on `√(J_k² + Y_k²)` through `k = x`, and `BesselYnTheorem.yn_accuracy` proves `yn` on the same ranges for every finite `x > 0`: the result is finite and within `(250 + 12 \|n\|) · 2^-53 · √(J_n² + Y_n²)`, or it is the infinity of the sign of `Y_n(x)` and `\|Y_n(x)\| > 2^1023`, and `yn_overflow` makes it that infinity from `2^1025` on.  `BesselNSpecial` proves the exceptional results of `jn` and `yn`.  The module compiles, and `BesselBytes` proves the byte theorems of all six functions (`bessel_module_accuracy`).  `BesselFile` states the file theorem. |

Each bound is the decided one, from the source's stated error, the sampled test that `tests/verified/run.sh` runs, and the errors of exact models of the ports at the worst inputs that Zimmermann's survey of libm accuracy lists for FreeBSD.  Those inputs raised `atan2` and `asinh` to two steps and fdlibm's `erfc`, since removed, to four, which the sampled tests had missed.  Every accuracy check now includes the double-precision inputs of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann, [Accuracy of Mathematical Functions](https://members.loria.fr/PZimmermann/papers/accuracy.pdf) (August 2026), and each check's largest distance is at most the decided bound: it equals the bound everywhere except `tanh` and `sinh`, whose checks find two steps against a proved three, and the CORE-MATH ports `erfc`, `tgamma`, and `lgamma`, whose checks find every result equal to the reference.  Where a port calls `Exp.expWith` or `Log.logWith` in place of fdlibm's own `exp` or `log`, the results can differ from fdlibm's in the last bit, and the journal records each such call.

The theorems that `verified_compile` generates establish that the compiled module computes each Lean algorithm.  The scalar routines have proofs allowing no trap under their runtime and table premises.  [The verified compiler's internals](Verified/README.md) describe those premises and the generated `denote_eq`, `implements`, `initial`, and `bytes` results.

### The exponential theorem

`ExpTheorem.exp_bytes_accuracy` states that the bytes of `Exp.compiled.module` decode to the module, that its function 5 is exported as `exp`, and that the module's initial store satisfies the store invariant `Verified.Ready`: the allocator invariant, the table borrowed at address 4096, and a memory cap of at most 65,535 pages.  A call of that entry from a store satisfying `Ready` returns without a trap a single `f64` and leaves a store satisfying `Ready`, in which every heap region of the earlier store keeps its bytes.  The theorem therefore covers every call in a sequence of calls to `exp` from the initial store.  The returned word is the bit pattern of `Exp.exp x`, and for finite `x` it is at most `0x7FF0000000000000` and within one encoding step of `F64PositiveRounding.roundNearestEven (Real.exp (value x))`.  `ExpTheorem.exp_one_step` states the bound for the Lean function, and `exp_pos_zero`, `exp_neg_zero`, `exp_pos_infinity`, `exp_neg_infinity`, and `exp_nan` give the exceptional results.  Every one of these theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.

| Inputs | Branch of `Exp.expWith` | Theorem |
|---|---|---|
| `abs(a) < 2^-54` and `2^-54 ≤ abs(a) < 512` | `1 + x` and the ordinary reconstruction | `ExpBranches.exp_small_one_step` (GPT) |
| `512 ≤ a ≤ 768` | `specialCase`, product with `2^1009` | `ExpSpecialPositive.positive_one_step` |
| `-768 ≤ a ≤ -512` | `specialCase`, product with `2^-1022`, compensated below 1 | `ExpSpecialNegative.negative_one_step` |
| `768 < abs(a) < 1024` | `specialCase` with a coarse residual bound | `ExpFarRange.far_positive`, `ExpFarRange.far_negative` |
| `abs(a) ≥ 1024`, finite | products `2^769 · 2^769` and `2^-767 · 2^-767` | `ExpTheorem.saturated_bits` |
| zeros, infinities, NaN | `1 + x` and the `-∞` test | `ExpTheorem.exp_pos_zero` through `exp_nan` |

The root `Library` import reaches the exponential theorem through the proofs of `exp2` and `exp10`, and `LeanExe.lean` imports the shared ProofKit modules.  `tools/leanrun --timeout 30m lake build Library.Numerics.Float64.Exp.ExpTheorem` builds the final theorem and every module it depends on.  After `tests/verified/run.sh` writes `build/verified/exp.wasm`, `tools/leanrun --timeout 10m lake env lean Library/Numerics/Float64/Exp/ExpFile.lean` checks the file theorem.  `tests/verified/run.sh` runs both checks after it writes the modules, and it fails unless `exp_file` and `exp_file_decode` report only the three permitted axioms.  The journal records the accepted builds, an independent rebuild from source, and the failures along the way.

### Limits of the exponential theorem

The user reviewed the statement on 2026-10-10, and the review found four limits.  Work the same day removed the first-call limit and added a theorem for the file.  The table lists the limits that remain.

| Limit | Detail | Plan |
|---|---|---|
| Talos and the decoder are trusted | `exp_bytes_accuracy` uses the CodeLib interpreter's `Wasm.run`, `Module.initialStore` for instantiation, and `Wasm.Encoding.decode`, which [the design notes](docs/design.md#scope-of-the-theorem) list as trusted.  The decoder test runs the binary decoder over the official WebAssembly testsuite, and [the Talos conformance driver](tests/talos/run.sh) runs the interpreter over it.  Engines outside the deterministic profile, such as browsers, may return other NaN bits. | `tests/verified/run.sh` and the WebAssembly testsuite passed on 2026-10-10.  The testsuite run recorded 64,751 passes, no failures, and 346 skips, and every float, conversion, integer, and memory-access file passed all its commands.  The run of `tests/talos/run.sh` on 2026-10-30 gave the same counts and a report equal to the one that Talos commits.  The testsuite runner reads modules through the interpreter's text decoder, so it tests execution.  `tests/decoder/DecodeTest.lean` ran the binary decoder over the same testsuite with no failures: 712 valid modules decoded to the text decoder's module and round-tripped, and 676 malformed modules were rejected. |
| `binary_file%` is trusted | `ExpFile.exp_file` proves that `build/verified/exp.wasm` holds `encode Exp.compiled.module`, and `exp_file_decode` that the file decodes to the module of `exp_bytes_accuracy`.  The elaborator `binary_file%`, which reads the file, is trusted, as for `gpt_file`. | None. |
| Canonical NaN argument only | `exp_bytes_accuracy` takes the argument `x.toBits` of a Lean `Float`, and `F64Bits.toBits_canonical` shows that every NaN `Float` has the canonical bits.  A WebAssembly caller can pass any of the other `2^53 - 3` NaN words.  For such a word the compiled code reaches `1.0 + x`, which gives the canonical NaN in Talos, but no theorem states this. | None.  The limit stays recorded. |
| Host actions between calls | `exp_bytes_accuracy` covers sequences of calls to `exp`.  The module also exports `alloc`, `release`, `specialCase`, `expCore`, `expWith`, its memory, and the globals `allocCount` and `freeCount`.  A host that calls another export or writes the memory between calls to `exp` needs a theorem that the action preserves `Ready`. | None planned. |

### Library results added for the theorem

| File | Content |
|---|---|
| [One step against the full reference](LeanExe/ProofKit/F64FullStep.lean) | One step between a word and the nearest-even reference, with the range allowed to end at positive infinity. |
| [Multiplication by a power of two](LeanExe/ProofKit/F64PowerScale.lean) | Exact product or infinity, and `dyadic_shifted_exact`, moved from `ExpReductionExact`. |
| [Grid exactness](LeanExe/ProofKit/F64GridExact.lean) | Exact sums and differences on a grid, moved from `ExpReductionExact`, and rounding of a positive sum within one binade with the half-ulp bound. |
| [Reconstruction one step](Library/Numerics/Float64/Exp/ExpOneStep.lean) | One step from the `(7/5) u 2^q H j` reconstruction bound, including the top binade next to infinity. |
| [Exponent, magnitude, and sign](LeanExe/ProofKit/F64Magnitude.lean) | Bounds between a word's exponent field and the magnitude of its value, the sign bit and the sign of the value, the value of a positive normal word, the words of zero, and sums of scaled values. |
| [Rounding stages](LeanExe/ProofKit/F64StageBounds.lean) | One rounded product or sum in a chain of bounded operations. |
| [Errors of rounded sums and products](LeanExe/ProofKit/RealRoundedError.lean) | Errors of sums and products whose operands carry errors. |

GPT's reconstruction lemmas now expose the bound before the final rounding (`presum_error`), the residual perturbation (`residual_change`), and the table perturbation (`table_change`).  The compensated subnormal path uses these pieces, and GPT's original statements are proved from them.  Several of GPT's hypotheses were widened where their proofs already allowed it, for example from `abs(a) ≤ 512` to 768 and from `abs(k) ≤ 147457` to `2^30`.

### The logarithm theorem

`LogTheorem.log_bytes_accuracy` has the form of the exponential theorem.  Its `Ready` borrows `logTable` at address 4096 and `logTable2` at 6152, and for every finite `x` with positive value, subnormals included, the word returned by the export `log` satisfies `F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits)) w`.  `log_within_one` states the bound for the Lean function, and `log_one`, `log_zero`, `log_pos_infinity`, `log_negative`, and `log_nan` give the exceptional results: `+0` for 1, negative infinity for both zeros, positive infinity for positive infinity, and the canonical NaN for negative inputs, negative infinity, and NaN.  `LogFile.log_file` and `log_file_decode` prove the contents of `build/verified/log.wasm`, and `tests/verified/run.sh` checks them as it checks `exp_file`.  The four limits of the exponential theorem apply in the same way.  The error before the final rounding is about `1.9 · 2^-60` in absolute terms on the main path, where `|log x| ≥ 0.06`, against an allowance of about `2.9 · 2^-60`, and about `0.145 u |x - 1|` against `0.35 u |x - 1|` near 1.

## Remaining work on the exponential proof

- [x] Review the final theorem's statement and premises with the user.
- [x] Commit the theorem with its limits recorded.
- [x] Prove the store invariant and the bound for every call in a sequence of calls to `exp`.
- [x] Add `exp_file` and run `tests/verified/run.sh`.
- [x] Run the interpreter testsuite.
- [x] Check the theorem in `tests/verified/run.sh`.  The user chose this over the root `Verified` import.
- [x] Consolidate the proof files.  General lemmas moved to ProofKit, which `LeanExe.lean` now imports, and four unused GPT lemmas were removed.

## Function agenda

| Stage | Functions | Main theorem work | Status |
|---|---|---|---|
| 1 | `exp` | Complete the obligations above and prove the numerical statement about bytes. | Proved: `ExpTheorem.exp_bytes_accuracy`. |
| 2 | Existing `log`, `expm1`, `tanh`, `sin`, `cos` | Log reduction and the near-one path.  Compensated exponential-minus-one arithmetic.  Hyperbolic saturation.  Both trig reduction methods, quadrant selection, and kernel errors, including arguments near zeros and the largest finite inputs. | All five proved. |
| 3 | `log1p`, `tan`, `atan`, `atan2`, `asin`, `acos` | Cancellation, endpoint behavior, reciprocal error, signed zeros, and quadrants.  Trig reduction feeds `tan`; each kernel needs its own approximation proof. | All six proved. |
| 4 | `sinh`, `cosh`, `asinh`, `acosh`, `atanh` | Piecewise formulas using proved exponential, logarithm, and square-root results.  Control cancellation, domains, and intermediate overflow. | `sinh` (three steps), `cosh` (one step), and `asinh`, `acosh`, and `atanh` (two steps each) proved. |
| 5 | `exp2`, `exp10`, `log2`, `log10`, `pow` | Base-specific reduction and exact powers.  For `pow`, logarithm-tail and product error, negative-base integer/parity classification, and exceptional inputs. | Proved. |
| 6 | `sinpi`, `cospi`, `tanpi`, `erf`, `erfc` | Reduction in units of pi.  Error-function definitions, approximation and remainder bounds, and the small `erfc` tail. | `erf`, `sinpi`, `cospi`, `tanpi`, and CORE-MATH's `erfc` proved. |
| 7 | `gamma`/`tgamma`, `lgamma` | Recurrence, reflection, approximation and asymptotic remainders, poles, sign, and overflow. | Ported from CORE-MATH, compiled, and checked.  The exceptional values of both are proved, and both within one step for the Lean functions and the compiled modules. |
| 8 | Bessel `j0`, `j1`, `y0`, `y1`, then `jn`, `yn` | Real specifications, small-argument and asymptotic errors, recurrence direction and stability, and accumulated error for integer order. | Ported from fdlibm and checked.  `j0`, `j1`, `y0`, and `y1` are proved for the Lean functions and for the compiled module's bytes, `jn` and `yn` are proved for the Lean functions and the compiled module's bytes outside `2 ≤ \|x\| < 2^302` with `\|n\| > \|x\|/2`. |

The broader special-function scope is open.  Candidate later families are beta, digamma, zeta, incomplete gamma, Airy, Dawson, and Fresnel functions.  Each needs a selected mathematical specification, input domain, error bound, and API before implementation.

### Decisions

The user delegated these decisions on 2026-10-10: Opus follows the precedent of the exponential work or its own recommendation after review, and records each choice in the journal.

| Decision | Choice |
|---|---|
| Inventory and order | Stages in the agenda, with stage 2 first.  Independent tracks run at once. |
| Numerical guarantees | `F64SignedRounding.WithinSteps n` with the `n` of the table of functions: one step where the implementation allows it, two for `atan2`, `asinh`, `acosh`, and `atanh`, and three for `tanh` and `sinh`, whose proofs compose worst-case bounds and reach three where sampling finds two.  `erfc` moves to CORE-MATH with one step.  The two-step allowance is about 0.74 times the composed error bound for `tanh` near `atanh(1/2)` and 0.83 times that bound for `sinh` near `\|x\| = 0.443`.  The Bessel functions get a bound in units of the modulus `√(J² + Y²)`, since no permissively licensed implementation reaches a step bound next to their zeros and the distance of every zero from its nearest doubles has not been computed. |
| Library placement | `Verified.Examples`, as for `exp`. |
| Gamma API | `Tgamma.tgamma : Float → Float`, `Lgamma.lgammaR : Float → Float × Float` returning `log \|Γ x\|` and the sign of `Γ x` as ±1, with CORE-MATH's choice of -1 at the negative integers, where `lgamma` is `+∞`, and `Lgamma.lgamma x := (lgammaR x).1`, from CORE-MATH (MIT) with a software fused multiply-add, since WebAssembly has no deterministic one.  fdlibm's `lgamma` errs by up to 4.45e15 units next to its negative zeros. |
| Bessel API | `j0`, `j1`, `y0`, `y1 : Float → Float`, and `jn`, `yn : UInt64 → Float → Float` with the order read as C's 32-bit `int` and `\|n\|` taken as `2^31` for `INT_MIN`, and the special values of fdlibm, which agree with POSIX.1-2017; POSIX.1-2024 gives `+HUGE_VAL` for `yn` of negative odd order at `±0` and `+0` at `+∞`, where the port returns `-0` for `yn(-1, +∞)`. |
| Algorithm or compiler changes | Reviewed and recorded in the journal before implementation. |
| Dependencies | Approval from the user before installing or adding one. |

### Sources and review

The implementation candidates include the versions already used by the repository: [FreeBSD fdlibm](https://github.com/freebsd/freebsd-src/tree/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src) and [Arm optimized-routines](https://github.com/ARM-software/optimized-routines/tree/503fafe311c177de0e571c458c7c337b1ca5f522/math).  Selecting a port includes an audit of its required operations, constant bits, operation order, non-FMA configuration, and license.  The current mathematical and float proof dependencies are Mathlib at `85e3a25e006c35636f0e53b0e9296caca2685bc0` and CodeLib/Talos at `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`, recorded in [the pinned dependency manifest](lake-manifest.json).  Mathematical definitions and approximation claims require proofs from the pinned sources.  An implementation's published error claim requires a Lean proof for the operations used here.

For Opus review, each completed function should identify its exact theorem statements and domains, implementation revision and configuration, constant and table proofs, reduction and approximation proofs, floating-point rounding proofs, exceptional-value proofs, byte theorem, axiom reports, and accepted build records.  Failed approaches and unresolved assumptions belong in the journal.  Status reports should name the strongest proved statement and its hypotheses.

## Lean execution and acceptance

[The repository instructions](AGENTS.md) govern every Lean, Lake, and Lean compiler invocation.  Run through `tools/leanrun`, with an explicit timeout.  The runner takes a machine-wide lock and, without options, sets one Lean thread and enforces these limits:

| Setting | Value |
|---|---|
| Memory high | 4 GiB |
| Memory maximum | 6 GiB |
| Swap maximum | 1 GiB |
| CPU quota | 100% |
| Scheduling | `nice -n 10`, `ionice -c 3` |
| Lean threads | `LEAN_NUM_THREADS=1` |

From the repository root, a focused numerical proof build has this form:

```sh
tools/leanrun --timeout 3m lake build Library.Numerics.Float64.Exp.ExpSpecialPositiveCore
```

This example names an earlier numerical leaf.  The final target is `Library.Numerics.Float64.Exp.ExpTheorem`.  Select the target and timeout for the changed proof and any prerequisite builds.  A timeout without a diagnostic requires a changed proof boundary or a checked reusable lemma before rerunning that target, as `AGENTS.md` specifies.  The options `--threads`, `--cpus`, and `--memory-high` select other thread counts, CPU quotas, and memory limits, as `AGENTS.md` describes.  Failure to create or enforce its scope requires stopping and asking the user.

Use `lake build` to rebuild changed imports.  A direct `lake env lean FILE` check reads existing compiled imports, so it requires those imports to have been rebuilt from the current sources.  Equations about Float computations are proved with `simp only` and the `F64Bits` bridge lemmas, never by `rfl` or `decide` that unfolds the IEEE operations.

Acceptance requires successful completion of the full selected build, review of its diagnostics, and an axiom report for the accepted declarations.  Review the accepted source and journal after each proof run.  A theorem printed before a later build failure requires a separate successful check before recording acceptance.

Repository test drivers, when an implementation check is needed, run directly as the first command token.  They invoke the runner themselves.  The Verified driver is `tests/verified/run.sh`.  Ordinary tests remain implementation checks.  Theorems determine completion.
