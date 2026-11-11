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
| Definition of the probability (design question 2) | The explicit integral of the density over the disk, on Mathlib's Lebesgue measure of `ℝ × ℝ` | A reader can check it against the textbook formula without Mathlib's Gaussian measures.  The cost is that no theorem yet relates it to `ProbabilityTheory`'s multivariate Gaussian (the design's optional P4). |
| Bounds of the error-function factor on a panel (design section 5.2) | Interval evaluation of both error-function arguments over the panel | The design bounds the factor with its monotonicity in `h` and `|μ|` (P2).  Interval evaluation needs only the monotonicity of `erf`, and its width also falls in proportion to `1/n`.  The cost is a wider interval on each panel, because the two arguments take their extremes at different points.  The width test measures it. |
| Panels (design question 3) | Uniform panels, with `n` an input from 1 to 1,048,576 | The caller chooses the cost.  Adaptive refinement is left out. |
| Tails (design question 4) | `erf` only | The module then needs one table.  The cost is the loss of relative accuracy for probabilities below about `1e-16`, which the requirements state.  The verdict against a threshold such as `1e-4` is unaffected. |
| Frames (design question 1) and remediation (design question 5) | Outside this iteration | The conjunction-message form is a later iteration. |
| Lower bound | Both factors clamped at zero | The result's lower bound is then never negative.  No clamp at 1 applies to the result, since that needs a proof that the density integrates to 1 over the plane. |
| Interface | Scalar arguments and a flat record | No allocation and no array layout to specify. |

## Open items

1. The conjunction-message form with `projection_sound`.
2. A theorem that `Model.pc` is the measure of the disk under Mathlib's multivariate Gaussian.
3. `erfc` in the tails, for relative accuracy at small probabilities.
4. Reference cases from published benchmarks and from NASA's tools.
5. A browser page.
