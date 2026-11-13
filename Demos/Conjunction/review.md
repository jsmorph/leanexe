# Conjunction probability requirements: decisions and review

[The requirements](requirements.md) specify the first iteration of the conjunction demo from the
design document `conjunction-probability-design.md`.  This record gives each decision with its
reason and each difference from the design.

## Decisions agreed with the user

| Decision | Choice | Reason |
|---|---|---|
| First program | Encounter-plane form on [the interval layer](../../Library/Numerics/Interval/README.md) | It is self-contained and uses the arithmetic and the function enclosures of the layer. |
| Interval type | Status word and two endpoints, with rejection carried through every operation | It follows `Bounds.Checked`, and one test of the final status covers a chain of operations. |

## Decisions made during the work

The user asked for a recommendation, a review of it, and then action on each question.

| Question | Choice | Reason and review |
|---|---|---|
| Definition of the probability (design question 2) | The explicit integral of the density over the disk, on Mathlib's Lebesgue measure of `ℝ × ℝ` | A reader can check it against the textbook formula without Mathlib's Gaussian measures.  `Gaussian.pc_eq_multivariateGaussian` proves that it equals the measure of the disk under Mathlib's `multivariateGaussian` with the stated mean and covariance (the design's optional P4). |
| Bounds of the error-function factor on a panel (design section 5.2) | Interval evaluation of both error-function arguments over the panel | The design bounds the factor with its monotonicity in `h` and `|μ|` (P2).  Interval evaluation needs only the monotonicity of `erf`, and its width also falls in proportion to `1/n`.  The cost is a wider interval on each panel, because the two arguments take their extremes at different points.  The width test measures it. |
| Panels (design question 3) | Uniform panels, with `n` an input from 1 to 1,048,576 | The caller chooses the cost.  Adaptive refinement is left out. |
| Tails (design question 4) | `erf` only | The module then needs one table.  The cost is the loss of relative accuracy for probabilities below about `1e-16`, which the requirements state.  The verdict against a threshold such as `1e-4` is unaffected. |
| Frames (design question 1) and remediation (design question 5) | Outside this iteration | The conjunction-message form is a later iteration. |
| Bounds of the result | Both factors clamped at zero, and the result clamped to `[0, 1]` | The result's lower endpoint is never negative, and its upper endpoint is at most 1.  `Model.pc_nonneg` and `Gaussian.pc_le_one` make the clamp sound. |
| Interface | Scalar arguments and a flat record | No allocation and no array layout to specify. |

## Open items

1. Done: the conjunction-message form with `projection_sound`, in
   [the section on tails and the message form](#tails-and-the-conjunction-message-form).
2. Done: `Gaussian.pc_eq_multivariateGaussian`, `Gaussian.integral_density`, and `Gaussian.pc_le_one`.
3. Done: `erfc` in the tails, for relative accuracy at small probabilities, in the same section.
4. Reference cases from published benchmarks and from NASA's tools.
5. A browser page.

## Radius at a probability: CE and LE

[The requirements' section on the radius](requirements.md#radius-at-a-probability-ce-and-le)
specifies `circularError` and `linearError` from brief 6.5 of the space-operations candidates and
the first candidate of the plan that orders them.  The plan asks for a measurement of the
enclosure's width near probability 0.9 before the requirements, an independent review of them,
and increments that each end in a compiled module and its theorem.

### Decisions

| Question | Choice | Reason |
|---|---|---|
| Statement of the radius | `Model.RadiusIn P q lo hi`: `0 ≤ lo ≤ hi`, exactly one `R ≥ 0` has `P R = q`, and that `R` lies in `[lo, hi]` | The intermediate value theorem between a radius shown below `p` and one shown at least `p` gives existence, and strict monotonicity gives uniqueness, so no theorem about the density's total mass is needed. |
| Search | Bracketing, then two bisections that keep a lower end shown below `p` and an upper end shown at least `p` | A single bisection must stop at the first midpoint whose enclosure contains `p`.  The two reach the limit that the enclosure's width sets on each side, and each keeps a one-sided invariant. |
| Exchange of axes | Integrate over the coordinate of larger variance | The measurement shows the radius interval's relative width between `7/n` and `11/n` with this choice and growing with the aspect ratio without it.  `Model.pc_swap` proves the exchange exact. |
| Growth of the bracket | A factor of 1.25, at most 16 evaluations | Doubling the upper end moves the evaluation to radii where uniform panels are coarse: with 64 panels it gives status 2 for a bias of 3 standard deviations.  The radius at any `p` up to `1 - 2⁻⁵³` is at most 8.6 times the starting radius, so 10 steps of 1.25 pass it and the remaining 6 reach about 4 times it. |
| Statuses | 0 accepted, 1 rejected input, 2 unfinished | The plan asks for a status for an unfinished search.  `definite` tests the conditional variance before the search, so a covariance that the arithmetic cannot show positive definite gets status 1. |
| Linear evaluation | A rejection for `L < 0`, then `½ (erfI + erfI)` | Every accepted evaluation then belongs to a radius of at least zero, as `pcWith`'s test `0 < r` gives for the disk. |
| Module | A separate compilation, `accuracy` | The module of `pc` and `assess`, its bytes, and its theorems stay as they are. |
| Variance or standard deviation for the linear error | Variance | It matches the covariance entries of the circular error. |

### Review

A fresh agent reviewed the requirements against the brief and the plan, with the earlier part of
the requirements, the README, and the VKB entry on independent review, and without the author's
reasoning.  It built three oracles in `mpmath` (a quadrature in the covariance's eigenbasis,
Imhof's inversion integral, and the noncentral chi-square series), a model of `pcWith` that
reproduces the README's sample bit for bit and every row of both width tables, a model of the
search with 22 wrong variants, and an adversarial enclosure with random rejections.  The
requirements it reviewed doubled the upper end of the bracket, so its statuses and counts of
bracketing steps refer to doubling.  Its scripts are not part of the tree.

| Finding | Verification | Response |
|---|---|---|
| No test requires status 0, and no test fixes the method: six sound wrong methods change only widths, bits, or statuses, and a program that always returns status 2 satisfies both theorems. | Its model, on 165 cases derived from the tests. | Adopted in part.  The containment test requires status 0 for every input outside a stated list of unfinished inputs, and it bounds the relative width of each accepted circular interval at `p = 0.9` by `12/n` and of each linear interval by `1e-8`.  The module test compares the module with native Lean bit for bit, so the method of the module is the method of the Lean source.  A replay of the search by an independent model driven by the module's `pc` is declined: it would test the Lean source against a transcription of itself, and the width bounds detect the sound methods that return wider intervals. |
| No case detects an exchange that negates `c12`. | Its wrong program W3e misses the reference in 9 of 9 cases at `m = (-1, 2)`, `C = (16, 6, 25)` and passes every listed input. | Adopted.  The requirements state that the exchange keeps `c12`, and the inputs of both tests hold `m = (-1, 2)`, `C = (16, 6, 25)`, whose radius equals that of `m = (2, -1)`, `C = (25, 6, 16)`. |
| No test names a rejected input or an unfinished one; one or two panels give status 2 for every input. | Its model: every panel then touches `±R`, where the chord is 0, so the lower endpoint of `pc` is 0. | Adopted.  The requirements list the rejected and unfinished inputs of the tests, among them one and two panels, and state the limit on `n`. |
| The target and role, the memory cap, and the cost bound are missing. | The plan's section "What every design states". | Adopted.  The requirements name the WebAssembly ground module, its absence of allocation, the bound of `16 + 2k` evaluations, and a measured time. |
| A large bias needs more panels for status 0, and the width sentence lacks the condition of status 0. | Its model with doubling: status 0 at `p = 0.9` needs 32 panels at no bias, 128 at 3σ, 2,048 at 100σ, and 16,384 at 1,000σ, with the radius width near `9/n` once accepted. | Adopted.  The requirements state that status 2 follows when the enclosure's width near the radius exceeds about `2(1 - p)`, that this width grows with the ratio of the radius to the largest standard deviation, and that the width figures hold for status 0. |
| The linear interval narrows to a few tens of units in the last place, not a few, and much less at small `p` with a bias, where the two error-function values cancel. | Its model: 7 to 84 units at `p` from 0.5 to 0.99, about 260 at `p = 1e-6` without a bias, and a relative width of `1.3e-9` with one. | Adopted.  The requirements and the README give the measured widths of the program. |
| The sample radii belong to the decimal `p`, while the program receives the binary64 `p`. | Its oracles: differences of 0.18 to 0.94 units in the last place. | Adopted.  The samples now give the radii for the binary64 inputs, which the containment test computes from the inputs' bits. |
| The purpose claims an interval for any `p` between 0 and 1. | Status 2 cases. | Adopted.  The purpose names status 0. |
| The interface allows `n` of 1 and 2, which always give status 2. | Its model. | Adopted as a stated limit; the range stays that of `pc`. |
| Bracketing evaluations after the fifth do not help. | Its model of doubling. | Declined for the factor of 1.25, whose reasons the decisions above give.  A search that fails spends 16 evaluations, which the cost bound includes. |
| "In every case but the first the upper end doubles" is ambiguous. | Its wrong program W11 reads it the other way and matches every output. | Adopted.  The method states the step after each evaluation that does not end the bracketing. |
| The measurement rows with the smaller variance first measure `pc` without the exchange, which `circularError` never performs. | Its model reproduces every row. | Adopted.  The table labels those rows. |
| `k`, `s`, and `p` mean other things in the conjunction part of the document. | The text. | Adopted.  The section names the starting radius `R0` and states that `k` and `p` there are the halving count and the probability. |
| The rejection rules have unstated limits on the inputs' range. | Its model: `C = 1e308·I` and `m = (1e154, 0)` give status 2, and `C = 1e-300·I` gives status 1, because the outward step on `c12² = 0` yields `-5e-324`. | Adopted.  The requirements state both limits. |
| No theorem ties the model to a probability distribution. | Mathlib at the pinned revision has `gaussianReal` and `multivariateGaussian`. | Recorded as an open item.  A theorem `Model.linearProb b v L = (gaussianReal b v).real (Icc (-L) L)` would also give the radius for every `p`. |
| The earlier part of the requirements says the entries of `pc` and `assess` may trap, while the README says they return without a trap. | `compiled.pc.implements` is an `ImplementsTables false` theorem, which excludes the trap. | Adopted.  The earlier part now says "without a trap". |

The review's wrong programs that the tests do not detect are the sound ones whose results differ
only in bits or cost: a bisection whose lower end stays 0 or whose ends do not move, a single
bisection that stops at the first midpoint whose enclosure contains `p`, a different starting
radius, and an extra bracketing evaluation.  The width bound detects the first two kinds and the
missing exchange when they widen the interval past it.  The review found that every unsound
variant it tried returns an unsound accepted result on its adversarial enclosure, and the
specified search none.

### Open items

1. A theorem that `Model.linearProb` and `Model.pc` are probabilities of Mathlib's normal laws,
   which would give the radius for every `p` below 1.
2. The three-dimensional spherical error, and covariances known within bounds.

## Adaptive panels

[The requirements' section on adaptive panels](requirements.md#adaptive-panels) specifies
`pcAdaptive` and `circularErrorAdaptive`.  The request asked for an adaptive enclosure that makes the radius search finish with fewer panels for large
biases and for `p` near 1, a decision whether it replaces the equal panels inside the radius search
or is a new entry beside `pc`, an independent review, and measurements against equal panels.

### Decisions

| Question | Choice | Reason |
|---|---|---|
| Replacement or new entry | A new module, `adaptive`, with `pcAdaptive` beside `pc` and `circularErrorAdaptive` beside `circularError` | Replacing the panels of `circularError` changes the bytes and the theorems of `accuracy`, and the request allows that only when needed.  The new entries need no change to either module, and `pcAdaptive` also serves the probability of collision, whose equal panels fail the same way for a disk much larger than the standard deviations. |
| Refinement | A march over `[-r, r]` that accepts a panel at most a tolerance wide | Splitting the widest panel under a cap needs an array of panels, allocation, and an invariant over the array.  The march needs one record of state and one invariant, and it aims at panels of equal width, the partition that splitting the widest panel approaches. |
| Tolerance | Three marches: `R/64`, then the tolerances that the sums of square roots of widths predict for `n/16` panels and for 0.8 times the panels left, and the common part of the last two sums | The measurements of the requirements: a single coarse estimate ran out of panels at a bias of 1,000 standard deviations, an estimate from the count of panels left up to 96 percent of the panels unused, the factor 0.9 ran out in most inputs, and the common part bounds the width when the last march runs out. |
| Next length | `0.9 √(τ/w)` times the last length, within `[1/4, 2]` | The width of a smooth panel's interval falls as the square of its length, so the rule aims each panel at a width just below `τ`.  The measurements did not compare it alone with doubling and halving. |
| Least `n` | 16 | The first march takes `n/16` steps, so smaller `n` leaves it none. |
| Input tests of the circular error | `guarded_sound`, proved once in `AccuracySoundness.lean` for any search, and used by `circularError_sound` and `circularErrorAdaptive_sound` | The two programs have the same tests around different searches.  The statement of `circularError_sound` and the bytes of `accuracy` do not change. |
| `p` near 1 without a bias | A stated limit and an open item | The best single march was 4 to 11 percent narrower than equal panels there, so a much narrower enclosure needs a panel enclosure of higher order. |

### Review

A fresh agent reviewed the section, the program, the theorem statements, the test inputs, and the
oracle, with the request and without the author's reasoning.  It ported the library's `exp` and
`erf` into a model of the interval layer that reproduces `pc`'s sample and the results of
`circularError` bit for bit, modelled the marches from the text before it read the program, and
then built a model of the program that reproduces all 39 results of `pcAdaptive` and every radius
result it compared, up to 4,096 panels.  Its `mpmath` oracle, a quadrature in the covariance's
eigenbasis independent of the program and of the polar integral of the tests, agreed with every
sample, and every accepted result of the containment run and the sweep contains its reference.
Its scripts are not part of the tree.

| Finding | Verification | Response |
|---|---|---|
| 1. At the least panel count that the sweep reported, an adaptive interval can be several times the radius, so the sweep overstated the gain. | Its decoding of the sweep: `[10.94, 123.0]` for `m = (10, 0)` at `p = 0.9` and 64 panels, `[100.9, 572.6]` for `m = (100, 0)` at 64; every result of `circularError` there was at most 0.30 of the radius wide.  At 64 panels the lower endpoint of `pcAdaptive` for `m = (100, 0)` stays below 0.9 from radius 101.3 to 604. | Adopted.  The sweep also finds the least count at which the interval is at most a hundredth of its lower endpoint wide, and the requirements and the README give both counts and state that status 0 at small counts can carry an interval wider than the radius. |
| 2. The purpose claims narrower intervals and fewer panels without qualification, while a small bias needs more panels. | The sweep: 16 against 64 panels for `m = (3, 0)` at `p = 0.5`, 32 against 64 without a bias at 0.9; the three marches up to 16 percent wider at 4,096 panels. | Adopted.  The purpose and the README state the gain by bias and give the counts. |
| 3. The requirements lack measurements that the request names, say nothing of the linear error, and have no target width. | The request; the table had only 0.9 and 0.99. | Adopted.  The measurements give the sweep at the five probabilities, the README gives the widths at all five, the purpose states that `linearError` evaluates no panels, and a paragraph states why the design has no target width. |
| 4. The column "One march, best tolerance" was not the best march. | Its grid of `log₁₀ τ`: `7.74e-4` against the stated `8.09e-4` without a bias at `p = 0.9`, `1.05e-3` against `1.14e-3` at 0.99, `4.57e-4` against `4.86e-4` for `σ = (100, 1)`; the 1,000σ row differed. | Adopted.  The table now holds the review's values from the ported functions, at the reference radii, with the grid search, and the conclusions follow them: 4 to 11 percent without a bias, up to 29 percent for elongated and correlated covariances.  The decision about `p` near 1 keeps its choice with these figures. |
| 5. "What lies outside" gave the order of the panel enclosure as the reason for the small gain without a bias, which contradicts `w ≈ L² g`. | Its Cauchy–Schwarz ratio on 65,536 equal panels: 0.95 at `p = 0.9` and 0.89 at 0.99 without a bias. | Adopted.  The requirements and the README give the ratio as the reason. |
| 6. The text differs from the program: the order of the length rule, the last panel's rejected interval and the fallback to one sum, `max(1, K)`, the setup's rejection, integer or real quotients, "at most" for the second march's steps, and a value that is not finite. | Its text model differs from the program in the last bits on 30 of 39 results of `pcAdaptive`; with `n = 100` the two readings of `n/16` give different intervals. | Adopted.  The method states the program's rules, the integer quotients, and the exact steps, and the interface states every rejection.  The module and containment tests add `n = 100`. |
| 7. The tests miss a common part that takes a stopped march's sum, a march that drops panels accepted for their length, any rejection, and the bound of `n` panels. | Input A, `m = (-1.3e154, 0)`, `C = (2e307, 0, 2e307)`, `r = 1.3e154`, which the program rejects and the first wrong program accepts with `[0.42867, 0.42917]` around `0.430287`; input B, `m = 0`, `C = (1e-28, 0, 1)`, `r = 1`, where the second gives `hi = 1.7e-308` against `0.6827`. | Adopted.  The containment test requires status 1 on input A, on the rejected inputs of both entries, and on 0, 15, and 1,048,577 panels, and it checks input B against bounds of its probability from a strip and a rectangle, since a polar quadrature cannot resolve it.  `marches` now returns the three marches, which `pcAdaptWith` uses, and `marches_used` proves that they evaluate at most `n` panels.  The requirements state the floor that panels accepted for their length set on the width. |
| 8. The statement that the Python model reproduces `pc`'s sample implied more than it holds. | The platform `erf` differs from the library's on 10,159 of 200,021 arguments; that model reproduces 9 of 26 results of `pcAdaptive` with at most 256 panels. | Adopted.  The requirements say so and take the table from the ported functions. |
| 9. The random set of the statistics was unstated. | Its own set gave maxima within 0.01 of the stated ones and somewhat different medians and run-outs. | Adopted.  The requirements state the distributions and the seeds and give the review's figures beside them. |
| 10. Docstrings of `Adaptive.lean` and `AdaptiveCases.lean` do not match the code, and an infinite radius was listed twice. | The program text. | Adopted for the new files: the header, `March`, and `marchStep` state the program's rules, and the duplicate input gave its place to input A.  Declined for the header of `Accuracy.lean`, which says "doubling" where the factor is 1.25: an edit there rebuilds the module `accuracy` from a changed source, which this work leaves unchanged; it is an open item. |
| 11. The README's hypothesis of `guarded_sound` omits that the probability is finite and positive, the audit omits `guarded_sound`, and three ratio figures differ slightly. | The statement; its recomputed medians 0.932, 0.448, and 1.090 and maximum 1.137. | Adopted.  The README states the hypothesis and the figures, and the audit lists `guarded_sound` and `marches_used`. |

The review ran each wrong program through the checks of the requirements as they stood:
`pcAdaptive` at 16, 256, and 4,096 panels (T1), the radius results at 256 panels (T2), the
unfinished inputs (T3), and the sweep up to 1,024 panels (T4).

| Wrong program | Kind | Detected by |
|---|---|---|
| Equal panels | sound | T2, status 2 at the far inputs |
| No exchange of axes | sound | T2, by the width bound only |
| An exchange that negates `c12` | unsound | T2, at `m = (-1, 2)` |
| The raising bisection tested on `lo`, the lowering one on `hi` | unsound | T2, T4 |
| A rejected panel skipped | unsound | T1, T2, T4 |
| A rejected panel added | unsound | T1, T2, T3, T4 |
| The fifth panel skipped | unsound | T1, T2, T4 |
| The fifth panel added twice | unsound | T4 only, at `m = (2, -1)`, `p = 0.9`, 64 panels |
| The last panel dropped | unsound | T1, T2, T4 |
| A last step that ends at `t + h` | unsound | T1, T2, T4 |
| A common part from `min(hi₂, lo₃)` | unsound | T1, T2, T4 |
| The second march alone | sound | T2 |

The containment test now holds results at 32, 64, and 128 panels, among them the one that
detected the doubled panel, and inputs A and B, which detect the common part of a stopped march
and the dropped panels accepted for their length in the review's model.  The status-1 checks
detect a program that accepts fewer than 16 panels, and `marches_used` excludes a third march that
spends more than `n` panels.  No check detects the text's order of the length rule, a growth of 2
in the bracketing, or the third march alone, which are sound and change only bits, counts, or
widths within the bound, or a missing test `t ≤ b`, which no input reaches because `b ≥ t` always
holds and which only the proof uses.

### Open items

1. A panel enclosure of higher order, such as the value at the panel's midpoint with an interval
   bound on the derivative of the integrand away from `±r`, whose width falls as the square of the
   panel's length and would narrow the radius interval at `p` near 1 without a bias.
2. `pc_enclosure` and `pcBoxWith_enclosure` repeat the step that `scaled_sound` proves, and could
   use it.
3. The header of `Accuracy.lean` describes the bracketing as doubling, while the program grows the
   upper end by 1.25.
4. A target width for an evaluation, from the search, which would let evaluations far from the
   radius stop early.

## Tails and the conjunction-message form

The request asked for `erfc` where both error-function arguments are large and of the same sign
(design question 4), with the enclosure proved as before and the statement of `pc_enclosure`
kept, and for the conjunction-message form of design section 5.3 with `projection_sound` and a
composed theorem for the probability, with the parsing of message text outside the verified
program.

### Decisions

| Question | Choice | Reason |
|---|---|---|
| Programs that use `erfc` | `pc`, `assess`, and the message form, through a separate panel path from `erfSumTailI` to `pcTail`; `pcWith` and `pcBoxWith` keep `erf` alone | `pcWith` and `pcBoxWith` are compiled into the modules `accuracy`, `adaptive`, and `avoidance`.  Putting `erfc` into `erfSumI` would pass the seven tables of `erfc` through every function of those programs, change their bytes, export indices, call theorems, and documents, and add the code of `erfc` to each module.  The radius search works at probabilities far above `1e-16`, and the avoidance threshold is near `1e-4`, so none of them gains.  The proofs share `panel_of_core` and `panels_of_panel`, which state the panel and loop steps for any interval function of the integrand. |
| Test that selects the `erfc` form | Every point of the interval of `v = (μ - h)/k`, or of `y = (-μ - h)/k`, at least 1/2 | `erf v > 1/2` and `w ≥ v` then give `erfc v + erfc w < 1 < erf v + erf w`, so the difference of `erfc` has the smaller rounding error.  The test affects only the width: `erfSumTailI_sound` holds for every branch. |
| Statement of `pc_enclosure` | Unchanged; `pc` passes `pcTail` the scalar setup and the point interval of `c11` | `pcWith_enclosure` takes the former statement for `pcWith`, which `AccuracySoundness.lean` uses. |
| Definition of the plane quantities | `encounter`, an `enclosure_def` whose body follows design section 5.3: RTN axes, rotation `Q C Qᵀ` into the inertial frame, sum, `x̂` along the part of `Δr` perpendicular to `Δv`, `ŷ = ẑ × x̂`, and projection | One body gives the real definition, the interval program, and `encounter.encloses`, so the program computes the definition's formulas and `projection_sound` follows from the generated theorem.  The plane covariance equals the projection `Cp` of CARA's `Pc2D_Foster.m`, whose axes are `-x̂` and `-ŷ`, and the miss vector equals its `(|Δr|, 0)` when `Δr ⊥ Δv`. |
| Units | Positions in km and velocities in km/s, covariances in m², radius in m, as CCSDS 508.0-B-1 gives them; `Δr` scaled by 1000 inside the definition | The caller passes the message's numbers unchanged.  The scale of the velocities does not enter, since only the directions of `r × v` and `Δv` do. |
| Inputs | Scalar arguments, 24 values of the two objects in the message's order, then the radius, the threshold, and `n` | No allocation and no array layout to specify, as for `pc`. |
| Module | The entries `pcMessage` and `assessMessage` in the module `conjunction` | The message form calls `pcTail`, which the module holds for `pc`.  With `erfc`, its seven tables, and the projection, the module grows from 13,717 to 64,046 bytes. |
| Zero miss | Rejected when the interval of the length of `Δr`'s part perpendicular to `Δv` holds zero | The design's `x̂` is undefined there.  The positions' rounding is about `1e-9` m near 7,000 km, far below the miss distance of a message. |

### Open items

1. `erfc` in `pcWith`, `pcAdaptWith`, and `pcBoxWith`, if a radius, adaptive, or avoidance use
   needs probabilities below `1e-16`.  It would change the modules `accuracy`, `adaptive`, and
   `avoidance` and their call theorems.
2. An Earth-fixed frame for the message form (design question 1), which would convert the
   velocities before the RTN frames.
3. A theorem that `encounter`'s plane quantities are the marginal of the three-dimensional
   Gaussian of the relative position along `Δv` (the design's optional P5), and that
   `Model.pc` does not depend on the orthonormal axes chosen in the plane.
4. Message cases from published conjunction data messages with their probabilities.
