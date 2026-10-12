# The Bessel functions

[The implementation](Bessel.lean) exports the Bessel functions of the first and second kinds `j0`, `j1`, `y0`, `y1`, `jn`, and `yn`, ports of fdlibm's `e_j0.c`, `e_j1.c`, and `e_jn.c` as FreeBSD has them [1, 2, 3], with the earlier ports of `sin`, `cos`, and `log` in place of the C library's.  The decided bound is in units of the modulus `√(J² + Y²)` of the order, `c · 2^-53 · √(J² + Y²)` with `c` set by the proof, since no permissively licensed implementation reaches a step bound next to the zeros of the functions.  `transcendentals` proves in ProofKit the real functions `J0`, `J1`, `Y0`, and `Y1`, their large-argument forms, fdlibm's rational approximations of those forms, and lower bounds on the moduli, with only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  Branch `w/log` proves the exceptional results of `j0`, `j1`, `y0`, and `y1` and bounds on the rounded steps of their large-argument path, and these results are not yet merged.  The accuracy theorems of the six functions are open, the module's `verified_compile` call is commented out until the compiler change that [the plan's section "Resuming the work"](../../transcendentals.md#resuming-the-work) describes, and track `log` is doing the proofs.

## Specification

`j0`, `j1`, `y0`, and `y1` compute `J₀`, `J₁`, `Y₀`, and `Y₁` of the value of the argument, and `jn n x` and `yn n x` compute `J_n` and `Y_n` with the order `n` read as C's `int` in the low 32 bits of the word, in two's complement.  `J_(-n) = (-1)^n J_n` and `Y_(-n) = (-1)^n Y_n` define the negative orders, and the port takes `|n| = 2^31` for `n = -2^31`, where C's `-n` overflows, a choice that the decision of 2026-10-11 accepts ([the journal](../../devnotes.md#2026-10-11-a-software-fused-multiply-add-core-maths-gamma-functions-and-fdlibms-bessel-functions)).  The first-kind functions are defined for every finite `x`, and the second-kind functions for `x > 0`.  [ProofKit's definitions](../../LeanExe/ProofKit/Bessel.lean) give `J₀`, `J₁`, `Y₀`, and `Y₁` by their power series in `z = x²/4`, DLMF 10.2.2, 10.8.1, and 10.8.2 [4], with Euler's constant `Real.eulerMascheroniConstant` and the harmonic numbers, and no definition of `J_n` or `Y_n` for `|n| ≥ 2` exists yet.

The decided statement, from the integration of 2026-10-12 and [the plan](../../transcendentals.md#functions), is `|w - F (a)| ≤ c · 2^-53 · √(J_n (a)² + Y_n (a)²)` for the value `w` of the result, the real function `F`, and a constant `c` that the proof sets.  The plan's next steps for track `log` estimate `c` at most 12 and ask the track to report before stating a larger one ([the plan](../../transcendentals.md#state-of-each-track)).  For `jn` and `yn`, the decision of 2026-10-11 allows a bound `a + b |n|` that grows with the order ([the journal](../../devnotes.md#2026-10-11-decisions-on-tanh-the-reflector-and-the-bessel-bounds)).  The modulus never vanishes, so the allowed error stays positive at the zeros of `J` and `Y`, where a bound in steps would need the distance of every zero from its nearest doubles, which has not been computed for these functions ([the review](../../devnotes.md#2026-10-10-review-of-the-options-for-stages-7-and-8)).  For a negative `x`, `J_n` is defined, `Y_n` is not, and the native check measures with the modulus at `|x|`.  The statement for negative arguments of `j0`, `j1`, and `jn` has not been written.

The native check measures in another unit: `2^(⌊log₂ M⌋ - 52)` for the modulus `M`, which lies between `2^-53 M` and `2^-52 M`.  An error of `e` of the check's units is therefore between `e` and `2e` units of `2^-53 M`, and the check's bounds of 4 and `4 + |n|/3` do not fix `c`.  A result within 4 of the check's units lies within `8 · 2^-53 M`, and the largest measured error of the four functions, 3.243 units for `y1`, is at most `6.49 · 2^-53 M`.

The C standard's Annex F and the recommended operations of IEEE 754-2019 include no Bessel function, and POSIX specifies them in its XSI option [6, 7].  The port follows fdlibm's special values, which agree with POSIX.1-2017 and with POSIX.1-2024 except where the table says.  The table lists the port's results and the rule of POSIX.1-2024, and branch `w/log` proves, in `BesselSpecial`, the rows for NaN and the infinities of `j0`, `j1`, `y0`, and `y1` and the rows for the zeros and the negative arguments of `y0` and `y1`.

| Input | Result of the port | POSIX.1-2024 [6] |
|---|---|---|
| NaN, every function | the canonical NaN | NaN |
| `j0 (±0)` | `1` | not addressed |
| `j1 (±0)` | `±0` | not addressed |
| `jn n (±0)` with `\|n\| ≥ 2` | `±0`, negative for odd `n` and a negative signed argument after the change of sign for a negative order | not addressed |
| `j0 (±∞)` | `+0` | `+0` for `+∞` |
| `j1 (±∞)` | `±0` | `+0` for `+∞` |
| `jn n (±∞)` | `±0`, signed as at `±0` | `+0` for `+∞` |
| `y0`, `y1`, `yn` at `±0` | `-∞` | `-HUGE_VAL`, but `+HUGE_VAL` for `yn` with a negative odd order |
| `y0`, `y1`, `yn` at `x < 0`, `-∞` included | the canonical NaN | NaN, or the result at 0 |
| `y0 (+∞)`, `y1 (+∞)`, `yn n (+∞)` | `+0`, but `-0` for `yn (-1)` | `+0` |

POSIX.1-2017 gives `-HUGE_VAL` for `yn` at 0 with every order [7], and the review of 2026-10-10 recommended that rule as POSIX's, so the port's `-∞` for a negative odd order follows the 2017 edition and fdlibm and departs from the 2024 edition.  `yn (-1) (+∞) = -0` comes from fdlibm's `sign*y1(x)`, while POSIX.1-2024 gives `+0` for `+∞`.  fdlibm raises the divide-by-zero and invalid exceptions on these paths, and the port does not.

## Algorithm

The methods are those that fdlibm's comments describe [1, 2, 3].  Below 2, `j0` is `1 - z/4 + z² R₀(z)/S₀(z)` with `z = x²`, and `j1` is `x/2 + x z R(z)/S(z)`, rational approximations whose stated errors are `2^-63.67` and `2^-61.51`.  `Y₀ - (2/π) J₀ ln x` is even and `Y₁ - (2/π)(J₁ ln x - 1/x)` is odd, as the series of DLMF 10.8.2 and 10.8.1 show, so `y0` is `U(z)/V(z) + (2/π) j0(x) ln x` and `y1` is `x U(z)/V(z) + (2/π)(j1(x) ln x - 1/x)`, with stated errors `2^-72` and `2^-65.89`.  Tiny arguments take the leading terms: `j0 = 1` and `j1 = x/2` below `2^-27`, `y0 = u₀₀ + (2/π) ln x` below `2^-27`, and `y1 = -2/(π x)` below `2^-54`.

From 2 up, the functions are `√(2/(π x)) (P cos θ ∓ Q sin θ)` and `√(2/(π x)) (P sin θ ± Q cos θ)` with `θ = x - π/4` for order 0 and `θ = x - 3π/4` for order 1, the large-argument forms of DLMF 10.17.3 and 10.17.4 [4].  fdlibm's `pzero`, `qzero`, `pone`, and `qone` approximate `P` by `1 + R(t)/(1 + t S(t))` and `Q` by `(q₀ + R(t)/(1 + t S(t)))/x` with `t = 1/x²`, `q₀ = -1/8` or `3/8`, on the four ranges that start at 2, at about 2.8571, at about 4.5454, and at 8, chosen by the high word of `x`.  `cos θ` and `sin θ` are `(sin x ± cos x)/√2`, and the one of `sin x ± cos x` that cancels comes from `-cos (2x)` divided by the other, which avoids the cancellation.  Above `2^129` the code drops `P - 1` and `Q`, and from `2^1023` on it does not form `cos (2x)`.

`jn` uses the forward recurrence `J_(k+1) = (2k/x) J_k - J_(k-1)` from `j0` and `j1` when `n ≤ x`, where it is stable, and the leading term of the asymptotic expansion above `2^302`.  Below `2^-29` it takes the leading term `(x/2)^n/n!` of the series, and 0 for `n > 33`.  Otherwise it evaluates a continued fraction for `J_n/J_(n-1)`, whose depth a recurrence for its convergents sets, runs the recurrence backward to orders 0 and 1, rescaling by `1/b` when `b` exceeds `10^100` if `n ln (2n/x)` reaches `ln` of the largest double, 709.78, and normalizes by the larger of `j0 x` and `j1 x`.  `yn` uses the forward recurrence from `y0` and `y1`, which is stable for `Y`, and stops when the value reaches `-∞`.

## Implementation

The sources are FreeBSD's `lib/msun/src/e_j0.c`, `e_j1.c`, and `e_jn.c` at commit `20381bce4b63975494a2f4bc84257f6932e6d379` [1, 2, 3], each with the 1993 copyright notice of Sun Microsystems, which states that permission "to use, copy, modify, and distribute this software is freely granted, provided that this notice is preserved".  The module docstring of [the implementation](Bessel.lean) gives the copyright line and paraphrases the permission as "freely distributable with this notice", the same defect that the plan records for the docstrings of `Erf.lean`, `Tanh.lean`, `Sinh.lean`, and `Asinh.lean`.  The port follows the C code operation for operation in the Verified dialect, and the commented `verified_compile` call lists 40 functions: 13 of [the trigonometric functions](Trig.lean), 3 of [the logarithm](Log.lean), and 24 of this module.

| C code | Port | Reason |
|---|---|---|
| `sincos (x, &s, &c)` | `Trig.sinWith` and `Trig.cosWith` with `Trig.invPi` and `Trig.halfPi` | FreeBSD's `sincos` evaluates the kernel formulas of its `sin` and `cos`, of which `Trig` is a port, so the journal concludes that the values are FreeBSD's. |
| `cos (x + x)` | `Trig.cosWith` | The same. |
| `log` | `Log.logWith` with `Log.logTable` and `Log.logTable2` | Arm's `log`, whose results may differ from fdlibm's `log` in the last bit. |
| `sqrt` | `Float.sqrt` | Correctly rounded in both. |
| `int n` | the low 32 bits of a `UInt64`, two's complement, with `\|n\| = 2^31` for `n = -2^31` | The dialect's words are unsigned, and C's `-n` overflows there. |
| the `while` loop that sizes the continued fraction | `LeanExe.repeatWhile` with `2^32 - 1` steps of fuel | The dialect's loops are bounded, and the module's docstring states that the fuel exceeds the steps the loop can take. |
| `huge + x > one`, `one/vzero`, `vzero/vzero` | the same expressions with `1e300`, `1.0/0.0`, and `0.0/0.0` | The values are kept, and the dialect has no flags. |
| `verified_compile` | commented out | With it, the build exceeds the runner's memory limit, as [the gamma function's Proof section](Tgamma.md#proof) describes. |

The tables `j0Table` (92 words) and `j1Table` (102 words) hold the coefficients of `pzero` and `qzero`, or `pone` and `qone`, on the four ranges, and `j1Table` also those of `y1` below 2.  The other coefficients below 2 are written inline, and each word carries fdlibm's decimal literal in a comment.  The journal records that a script checked fdlibm's bit patterns against the rounding of each decimal literal.  A comparison of the port with the three C files at the pinned commit, run outside the repository, gives the results in the table.

| Check | Result |
|---|---|
| Floating-point literals of the C files | All 246 occurrences occur in the port as words or decimal literals, some with the opposite sign where the port writes a negation differently. |
| `double` arrays | All 34 occur in order as contiguous runs of `j0Table` or `j1Table`. |
| Comments | All 197 words with a decimal literal in their comment equal the nearest double to that literal. |

## Theorems

`transcendentals` contains no theorem about `Bessel.j0`, `j1`, `y0`, `y1`, `jn`, or `yn`.  The Lean module defines no `compiled` WebAssembly module, so there is no byte theorem and no file theorem, and `tests/verified/run.sh` writes no `bessel.wasm` and runs [the accuracy check](BesselAccuracy.lean) natively.  The real-analysis results below are proved in `LeanExe/ProofKit`, which [the library's root import](../../LeanExe.lean) imports, and in the integration build `opus-merge-tan-1.log`, in `build/transcendentals` on the build host, each of them reports only `propext`, `Classical.choice`, and `Quot.sound`.

| Theorem | Statement |
|---|---|
| `Bessel.hasDerivAt_J0`, `hasDerivAt_J1'`, `hasDerivAt_Y0`, `hasDerivAt_Y1` | `J₀' = -J₁` for every `x`, and `J₁' = J₀ - J₁/x`, `Y₀' = -Y₁`, and `Y₁' = Y₀ - Y₁/x` for `x ≠ 0`, so each function satisfies Bessel's equation of its order |
| `Bessel.wronskian` | `J₁ Y₀ - J₀ Y₁ = 2/(π x)` for `x ≠ 0`, DLMF 10.5.2 |
| `Bessel.Y0_sub_log`, `Y1_sub_log` | `Y₀ - (2/π) J₀ ln x` and `Y₁ - (2/π)(J₁ ln x - 1/x)` as series in `z` with the constant `γ - ln 2`, the parts that fdlibm approximates below 2 |
| `Bessel.a0_remainder`, `a1_remainder`, `c0_remainder`, `c1_remainder` | For `\|z\| ≤ 1` and `N ≥ 1`, each of the four series lies within `2 \|a_N\| \|z\|^N` of its partial sum of `N` terms |
| `EulerGamma.gamma_close`, `gamma_rad_small`, `log_two_close` | `γ` within `gammaRad < 2^-84` of a rational, and `ln 2` within `2^-100` of one |
| `BesselPQ.J0_large`, `Y0_large`, `J1_large`, `Y1_large`, `modulus0`, `modulus1` | The large-argument forms with `P` and `Q` defined by the inverse rotation, and `J² + Y² = (2/(π x))(P² + Q²)`, for `x > 0` |
| `BesselPQ.P0_system`, `P1_system` | `P'' = 2Q' - (κ/x²) P` and `Q'' = -2P' - (κ/x²) Q`, with `κ = 1/4` for order 0 and `-3/4` for order 1 |
| `BesselEnergy.energy0_bound`, `energy1_bound` | The energy of the error of an approximate solution grows by at most the integral of its residuals |
| `BesselLarge0.pieces_bound`, `asym_bound`, and the same in `BesselLarge1` | On `[2, ∞)`, `P` and `Q` of each order lie within `2^-80` of explicit polynomials: Taylor polynomials of degree 40 on seven pieces up to 30, and Hankel's expansion with 60 terms in `1/x` from 30 on |
| `BesselFd0a.pzero_2` to `BesselFd1b.qone_8` (16 theorems) | fdlibm's `pzero`, `qzero`, `pone`, and `qone`, without rounding, lie within `e · 2^-68 + 2^-70` of `P` and `Q` for every real `x` of each range, with `e` in the table below |
| `BesselModulus.modulus_product` | `(2/(π x))² ≤ M₀² M₁²` for `x > 0` |
| `BesselModulus.near0`, `near1`, `modulus0_large`, `modulus1_large` | `\|P - 1\| ≤ 1/10 + 2^-80` and `\|Q\| ≤ 1/5 + 2^-80` for `x ≥ 2`, so `(3/4)(2/(π x)) ≤ M² ≤ (13/10)(2/(π x))` |
| `BesselModulus.modulus0_small`, `modulus1_small` | `M₀² ≥ 1/25` and `M₁² ≥ 4/25` for `0 < x ≤ 2` |

| Function | From 2 | From `b3` (2.8571) | From `b5` (4.5454) | From 8 | Comment of the source |
|---|---|---|---|---|---|
| `pzero` | 1067 (`2^-57.94`) | 1662 (`2^-57.30`) | 277 (`2^-59.88`) | 261 (`2^-59.97`) | `2^-60.26` |
| `qzero` | 127 (`2^-61.01`) | 109 (`2^-61.23`) | 22 (`2^-63.52`) | 18 (`2^-63.81`) | `2^-61.22` of `x Q` |
| `pone` | 1472 (`2^-57.48`) | 2231 (`2^-56.88`) | 321 (`2^-59.67`) | 282 (`2^-59.86`) | `2^-60.06` |
| `qone` | 171 (`2^-60.58`) | 127 (`2^-61.01`) | 29 (`2^-63.13`) | 20 (`2^-63.66`) | `2^-61.13` of `x Q` |

The approximations of `P` exceed their comments by up to a factor of 6.7 below `b5`, and the proved bounds lie 8 to 10 percent above the maxima that a Python model measured at 4,000 points per range, the margin that the kernel's bisection needs.  The journal names these proved figures as the ones that a proof of `j0`, `y0`, `j1`, and `y1` should use in place of the comments.  In units of the amplitude `√(2/(π x))`, `2^-56.88` is about `2^-4` of a unit in the last place.

Branch `w/log`, in a separate worktree on the build host, holds the commits `278cd102` to the head of the branch, which are not yet merged into `transcendentals`, with the theorems in the next table.  Each of these theorems reports only `propext`, `Classical.choice`, and `Quot.sound` in the build named, in that worktree's `build/transcendentals`, and the branch's journal section "2026-10-12: Bessel functions, the Lean functions `j0`, `j1`, `y0`, and `y1`" records them, their failures, and the error budget.  `uv run tools/bessel/genpq.py` writes `BesselPQ0` and `BesselPQ1` on that branch, and the kernel checks every bound it chooses.  Here `u = 2^-53`, and `FApprox w y e` states that the double `w` is finite and lies within `e` of the real `y`.

| Theorem (module on `w/log`) | Statement | Commit, build |
|---|---|---|
| `TrigNear.sin_near`, `cos_near` | `Trig.sin x` and `Trig.cos x` within `(71/50) u` of `sin x` and `cos x` for every finite `x` | `278cd102`, `bes-trignear-3.log` |
| `LogNearAll.log_near` | `Log.log x` within `(6/5) u \|log x\| + 2^-59` of `log x` for every finite `x > 0` | `98612d56`, `bes-lognear-4.log` |
| `BesselSpecial.j0_infinity`, `j1_pos_infinity`, `j1_neg_infinity`, `y0_zero`, `y1_zero`, `y0_pos_infinity`, `y1_pos_infinity`, `negative_cases`, and the four `_nan` theorems | The exceptional results of `j0`, `j1`, `y0`, and `y1` in the table of the specification | `692d6d84`, `bes-special-2.log` |
| `BesselCS.asym0_near`, `asym1_near`, `asym0_huge`, `asym1_huge`, `quot_near` | For `x ≥ 2`, the pair `(cc, ss)` of `asym0` or `asym1` within `(96/25) u` and `(627/100) u` of `√2 cos θ` and `√2 sin θ`, one in each order by branch, and within `(96/25) u` for both from `2^1023` on | `ef3ed7ac`, `bes-cs-2.log` |
| `BesselRatioEval.pieces_sound`, `BesselPQEval.recip_sq`, `ratio_float`, `BesselPQRange.p_of_ratio`, `q0_of_ratio`, `q1_of_ratio` | The computed `ẑ = 1/(x x)` within `(2 + 2^-40) u/x²` of `1/x²` for `2 ≤ x ≤ 2^130`, the rounded quotient of two Horner evaluations as a distance from `R(z)/S(z)` under kernel checks on pieces, and the rounded `P` and `Q` terms of one range | `b49cfded`, `52688e88`, `bes-reval-2.log`, `bes-pqe-1.log`, `bes-pqr-2.log` |
| `BesselPQ0.pq_r0` to `pq_r3`, `BesselPQ1.pq_r0` to `pq_r3` | On each of fdlibm's four ranges from 2 to `2^129`, `Bessel.pAsym` and the code's `Q` term of each order within explicit bounds of `P` and `Q`, which combine the rounding with the bounds of `BesselFd0a` to `BesselFd1b`, and bounds on `P` and `Q` themselves | `6ed384f8`, `bes-pq-3.log` |
| `BesselCombine.invsqrtpi_near`, `tpi_near`, `combine_sub`, `combine_add`, `final_step`, `J0_form`, `Y0_form`, `J1_form`, `Y1_form`, `modulus_lower` | `invsqrtpi` within `0.07 u` of `1/√π` and `tpi` within `0.36 u` of `2/π`; the rounded bracket `P̂ ĉc ∓ Q̂ ŝs` or `P̂ ŝs + Q̂ ĉc` from its factors; `invsqrtpi · T / √x` within `finErr / √x + 2^-1075` of `T/√(π x)`; the four large-argument forms in terms of `sin x ± cos x`; and `√(2/(π x)) √(P² + Q²) ≥ 0.7978 Pl / √x` for `P ≥ Pl > 0` | `b2f71ebf`, `bes-comb-2.log` |
| `BesselCase.case_sub`, `case_add`, `case_one`, `case_finish`, `BesselLarge.large_sub`, `large_add`, `modulus_ge`, `huge_pq0`, `huge_pq1` | One case of the path from 2 against any `M ≥ 0.7978 Pl / √x` under numeric conditions that `norm_num` checks, both branches of `(cc, ss)` together, and `\|P - 1\| ≤ 262 · 2^-68` and `\|Q\| ≤ 19 · 2^-68` (order 0) or `283 · 2^-68` and `21 · 2^-68` (order 1) from `2^129` on | `b59e0975`, `e667a448`, `bes-case-2.log`, `bes-large-a1.log` |
| `BesselJ0Large.j0_large` | For finite `x` with `\|x\| ≥ 2`, `\|value (j0 x) - J₀(x)\| ≤ 10 u √(J₀(\|x\|)² + Y₀(\|x\|)²)`, on the four ranges, both branches, and the path from `2^129` | `e55ba4e9`, `bes-j0l-4.log` |
| `BesselY0Large.y0_large` | For finite `x ≥ 2`, `\|value (y0 x) - Y₀(x)\| ≤ 10 u √(J₀(x)² + Y₀(x)²)` | `94fcd632`, `bes-y0l-2.log` |
| `BesselY1Large.y1_large` | For finite `x ≥ 2`, `\|value (y1 x) - Y₁(x)\| ≤ 12 u √(J₁(x)² + Y₁(x)²)` | `bes-y1l-1.log` |

## Proof

### Modules

The ProofKit chain, in dependency order, is `EntireSeries`, `Bessel`, `BesselPQ`, `PolyCalc`, `EulerGamma`, `BesselConstants`, `BesselEnergy`, `BesselChain`, `BesselAsym`, `BesselStart`, `BesselLarge0`, `BesselLarge1`, `BesselRatio`, `BesselSeg0`, `BesselSeg1`, `BesselFd0a`, `BesselFd0b`, `BesselFd1a`, `BesselFd1b`, and `BesselModulus`, with `PolyBound`, `TaylorRemainder`, `PolyChecks`, and `AsinRemainder` from earlier tracks.  [The library's root import](../../LeanExe.lean) imports all twenty, and the integration build `opus-merge-tan-1.log` built them with 9,426 jobs.  The journal also records focused builds of each target, such as `bes-large-4.log` with 3,456 jobs.

| Module | Content |
|---|---|
| [Entire power series](../../LeanExe/ProofKit/EntireSeries.lean) | `psum a z`, its derivative by Mathlib's termwise differentiation, and the remainder after `N` terms under a ratio bound |
| [The Bessel functions of orders 0 and 1](../../LeanExe/ProofKit/Bessel.lean) | The definitions, derivatives, Wronskian, and series remainders |
| [The large-argument forms](../../LeanExe/ProofKit/BesselPQ.lean) | `P`, `Q`, the forms of DLMF 10.17, the moduli, and the system for `P` and `Q` |
| [Exact polynomial evaluation](../../LeanExe/ProofKit/PolyCalc.lean) | Rational evaluation and differentiation of coefficient lists that the kernel computes |
| [Euler's constant](../../LeanExe/ProofKit/EulerGamma.lean) | `γ` within `2^-84` from `H_n - ln n` with Euler–Maclaurin corrections at `n = 128`, and `ln 2` within `2^-100` |
| [Constants](../../LeanExe/ProofKit/BesselConstants.lean) | Enclosure arithmetic, `π` by Machin's formula within `2^-190`, where the module's docstring states `2^-180`, and `cos 2` and `sin 2` |
| [The energy method](../../LeanExe/ProofKit/BesselEnergy.lean), [chains](../../LeanExe/ProofKit/BesselChain.lean), and [the asymptotic piece](../../LeanExe/ProofKit/BesselAsym.lean) | The growth of the error energy across a piece, the jumps between pieces, and the induction over the pieces |
| [The start at 2](../../LeanExe/ProofKit/BesselStart.lean) | `P`, `Q`, and their derivatives at `x = 2` within `2^-86` of dyadic values, from the four series at `z = 1` |
| [Order 0 on `[2, ∞)`](../../LeanExe/ProofKit/BesselLarge0.lean) and [order 1](../../LeanExe/ProofKit/BesselLarge1.lean) | The pieces, the kernel checks, and the `2^-80` bounds |
| [Comparison with fdlibm](../../LeanExe/ProofKit/BesselRatio.lean), [segments of order 0](../../LeanExe/ProofKit/BesselSeg0.lean) and [of order 1](../../LeanExe/ProofKit/BesselSeg1.lean) | `pFd` and `qFd`, the integer bisection `ratioCheckI` and its soundness, and polynomials of degree 16 on 27 short segments per order |
| [`pzero` and `qzero` from 2](../../LeanExe/ProofKit/BesselFd0a.lean), [from 8](../../LeanExe/ProofKit/BesselFd0b.lean), [`pone` and `qone` from 2](../../LeanExe/ProofKit/BesselFd1a.lean), [from 8](../../LeanExe/ProofKit/BesselFd1b.lean) | One kernel check per segment and one for the expansion, and the 16 bounds |
| [The moduli](../../LeanExe/ProofKit/BesselModulus.lean) | The lower and upper bounds on `M²` |

### Method

The bounds on `P` and `Q` avoid an integral representation of the Bessel functions and the connection formulas.  With `U = √(π x/2) J` and `V = √(π x/2) Y`, Bessel's equation becomes `U'' = -(1 + κ/x²) U`, and the rotated pair `P`, `Q` satisfies a second-order system.  For an approximation with residuals `r₁` and `r₂`, the square root of the energy `E = (p' - q)² + (q' + p)² + (1 + κ/x²)(p² + q²)` of the errors `p` and `q` grows by at most `|r₁| + |r₂|` when `κ ≥ 0`, and a weighted energy gives `(10/9)(|r₁| + |r₂|)` when `κ < 0` and `1 + κ/x² ≥ 81/100`.  The errors therefore stay within their value at `x = 2`, from the series, plus the integral of the residuals, which the kernel bounds from polynomials it computes.  The chain starts at `2^-83` at `x = 2` and ends below `2^-80`, and Hankel's expansion takes over at 30, below which its smallest term, near `e^(-2x)`, cannot reach `2^-80`.

The comparison with fdlibm splits each piece into dyadic segments of width `c/8` to `c/11` with polynomials of degree 16 within `2^-71` of the piece's polynomial, truncates Hankel's expansion to degree 26 within `2^-72`, and writes `A - pFd` as `E/W` with polynomials of degree 28.  `ratioCheckI` bisects a segment until the coefficients of `E` and `W` at each center give `|E| ≤ ε W`, in integers, so the kernel does no rational normalization.  The first check in rational arithmetic on the degree-40 pieces filled the runner's memory limit and was stopped, and integer bisection on degree 30 ran to the 60-minute timeout, which is why the segments exist ([the journal](../../devnotes.md#2026-10-12-bessel-functions-fdlibms-p-and-q-and-the-moduli-track-log)).

### Open parts

Branch `w/log` holds the pre-rounding forms of `Trig.sin`, `Trig.cos`, and `Log.log`, the exceptional results of the four functions, and the rounded `P`, `Q`, `cos θ`, and `sin θ` terms of the path from 2, all unmerged.  Four parts remain before the decided theorems.  The first is the error budget of each path and the constant `c`: the rational approximations below 2, whose stated errors are not yet compared with the proved series, the products, the square root, and the final combination on the path from 2, which the plan asks track `log` to finish before it proves the four theorems for the Lean functions.  The second is the lower bounds on the moduli below 2, which are coarse, `M₀ ≥ 1/5` and `M₁ ≥ 2/5` against true minima of about 0.557 and 0.586 at `x = 2`, and a proof of `y0` or `y1` near 2 may need sharper ones, which the same series give on shorter intervals.  The third is the work on `jn` and `yn`, which need definitions of `J_n` and `Y_n`, their recurrences, and an analysis of the forward recurrence and of the continued fraction and backward recurrence, whose error the native check finds growing with the order.  The fourth is the byte and file theorems, once the compiler change lets `verified_compile` run.

## Tests

[The accuracy check](BesselAccuracy.lean) compares each result natively with [the Bessel references](BesselReference.lean) in units of the modulus: with `J` and `Y` the references of the order at `q` bits, `M = isqrt (J² + Y²) · 2^-q`, the unit is `2^(⌊log₂ M⌋ - 52)` without a clamp at the subnormal range, and the error is computed exactly.  It requires at most 4 units for `j0`, `j1`, `y0`, and `y1`, and at most `4 + |n|/3` for `jn` and `yn`, and it requires the special values above exactly.  The arguments of the four functions are 1,501 evenly spaced values from 0.001 to 2, 3,001 from 2 to 40, and 1,501 from 40 to 300, the seven doubles around each of the first two zeros of the function, 1,400 hashed values from `2^9` to `2^201`, from `2^201` to `2^1000`, and below 1, the inputs of `WorstCases`, with both signs for `j0` and `j1`, and nine special values: 14,859 for `j0`, 14,857 for `j1`, and 7,431 each for `y0` and `y1`.  `jn` and `yn` take the orders 2, 3, 5, 10, 20, 50, 100, -2, -3, -7, and `2^32 + 5`, with 210 arguments each: 151 evenly spaced values up to `2n + 30`, 50 hashed values from `2^9` to `2^60`, from `2^302` to `2^1000`, and below `2^-29`, and the special values.  The docstring of the check gives the upper end of the hashed ranges as `2^1024`, and the generator's exponent fields stop below `2^1000`.

The worst-case inputs are those of Tables 4 to 11 of Gladman, Innocente, Mather, Ozaki, and Zimmermann's report [8], eight for `j0`, seven for `j1`, and five each for `y0` and `y1`.  The report's Table 3 lists 4.51e14 units for `j0`, 1.10e15 for `j1`, 1.42e15 for `y0`, and 5.56e15 for `y1` in FreeBSD 15.1, in units of the result's last place.  The large figures come from cancellation next to the zeros, where the result, and with it the unit of its last place, approaches zero while the modulus does not.  The review of 2026-10-10 measured FreeBSD's own functions within 3.01 units of the modulus and glibc 2.41's within 3.14.

The references compute `J₀`, `J₁`, `Y₀`, and `Y₁` below 300 from their power series, with Euler's constant from Brent and McMillan's algorithm B1, based on modified Bessel functions [5], and from 300 up from Hankel's expansions.  `J_n` comes from its series below `max (300, n)` and from the forward recurrence above, and `Y_n` from the forward recurrence, at a precision that grows with half the exponent of `x` above 300.  The truncation errors are stated in docstrings and are not proved.

| Function | Largest error, check units | At | Bound of the check |
|---|---|---|---|
| `j0` | 2.617 | 23.48 | 4 |
| `j1` | 2.764 | 11.63 | 4 |
| `y0` | 3.171 | 187.68 | 4 |
| `y1` | 3.243 | 10.64 | 4 |
| `jn`, orders 2, 3, 5, 10, 20, 50, 100 | 2.648, 2.030, 2.490, 2.547, 3.426, 10.408, 8.755 | | `4 + \|n\|/3` |
| `jn`, orders -2, -3, -7, `2^32 + 5` | 2.648, 2.030, 3.225, 2.490 | | `4 + \|n\|/3` |
| `yn`, orders 2, 3, 5, 10, 20, 50, 100 | 2.420, 2.323, 4.137, 4.655, 8.793, 10.039, 15.380 | | `4 + \|n\|/3` |
| `yn`, orders -2, -3, -7, `2^32 + 5` | 2.420, 2.323, 4.797, 3.522 | | `4 + \|n\|/3` |

The table gives the largest errors of `opus-verified-tests-14.log`, the run of `tests/verified/run.sh` in `build/transcendentals` on the build host after the `sinh` merge.  The ports track's runs `ports-BesselAccuracy-6.log` and `ports-BesselAccuracy-7.log`, in `build/transcendentals` on the build host, give the same figures, the second with the final bounds.  `yn` of order 20 exceeds `4 + |n|/6`, the form that the first measurements suggested and that the decision of 2026-10-11 records as fitting the data, so with `a = 4` the data need `b ≥ 0.24`.  The runs use the module built without its `verified_compile` call, so they test the Lean functions, and no compiled WebAssembly.

## Limits

Every result for the six functions in `transcendentals` is a test of the Lean functions, and the decided theorems are open.  Until the compiler change is merged and `verified_compile` runs, no WebAssembly module exists, and after that the limits of [the exponential](Exp.md#limits) apply: Talos and the decoder are trusted, the file theorem trusts `binary_file%`, the theorems cover the canonical NaN argument only, and host actions between calls need their own theorem.  The ProofKit results rest on polynomials that a Python model produced, and the proofs use only the residuals and bounds that the kernel computes from them, so the model is not trusted.

The modulus bound is weaker than a relative bound: next to a zero of `J` or `Y` the result may have few or no correct digits, and a theorem of this form permits that.  The constant `c` is not yet fixed, the check's unit differs from the plan's by a factor between 1 and 2, and the form `a + b |n|` for `jn` and `yn` has no fixed constants.  The port keeps fdlibm's `-∞` for `yn` of a negative odd order at 0 and `-0` for `yn (-1) (+∞)`, where POSIX.1-2024 gives `+HUGE_VAL` and `+0`.

## References

1. FreeBSD, [`lib/msun/src/e_j0.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_j0.c), commit `20381bce4b63975494a2f4bc84257f6932e6d379`.  Copyright (C) 1993 by Sun Microsystems, Inc.
2. FreeBSD, [`lib/msun/src/e_j1.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_j1.c), same commit.
3. FreeBSD, [`lib/msun/src/e_jn.c`](https://github.com/freebsd/freebsd-src/blob/20381bce4b63975494a2f4bc84257f6932e6d379/lib/msun/src/e_jn.c), same commit.
4. F. W. J. Olver, A. B. Olde Daalhuis, D. W. Lozier, B. I. Schneider, R. F. Boisvert, C. W. Clark, B. R. Miller, B. V. Saunders, H. S. Cohl, and M. A. McClain, eds., *NIST Digital Library of Mathematical Functions*, Release 1.2.8 of 2026-09-15: [§10.2](https://dlmf.nist.gov/10.2) (10.2.1, Bessel's equation, and 10.2.2, the series of `J_ν`), [§10.5](https://dlmf.nist.gov/10.5) (10.5.2, the Wronskian), [§10.8](https://dlmf.nist.gov/10.8) (10.8.1 and 10.8.2, the series of `Y_n` and `Y₀`), and [§10.17](https://dlmf.nist.gov/10.17) (10.17.3 and 10.17.4, Hankel's expansions, and 10.17(iii), their error bounds).
5. R. P. Brent and E. M. McMillan, "Some new algorithms for high-precision computation of Euler's constant", *Mathematics of Computation* 34(149):305–312, 1980, [doi:10.2307/2006237](https://doi.org/10.2307/2006237).  Crossref and [Brent's publication page](https://maths-people.anu.edu.au/~brent/pub/pub049.html) confirm the bibliographic data, and the text was read in the scan linked there: Section 3 gives algorithm B1, which evaluates `γ` from the series `U(n)` and `V(n)` of the modified Bessel functions `I₀` and `K₀`, with an error below `π e^(-4n)` by its equation (5).
6. The Open Group, *The Open Group Base Specifications Issue 8*, IEEE Std 1003.1-2024: [`j0, j1, jn`](https://pubs.opengroup.org/onlinepubs/9799919799/functions/j0.html) and [`y0, y1, yn`](https://pubs.opengroup.org/onlinepubs/9799919799/functions/y0.html).
7. The Open Group, *The Open Group Base Specifications Issue 7*, 2018 edition, IEEE Std 1003.1-2017, [`y0, y1, yn`](https://pubs.opengroup.org/onlinepubs/9699919799/functions/y0.html).
8. B. Gladman, V. Innocente, J. Mather, K. Ozaki, and P. Zimmermann, ["Accuracy of Mathematical Functions in Single, Double, Double Extended, and Quadruple Precision"](https://members.loria.fr/PZimmermann/papers/accuracy.pdf), August 2026: Table 3 and Tables 4 to 11.
