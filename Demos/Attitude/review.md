# Attitude determination requirements: decisions and review

[The requirements](requirements.md) specify TRIAD and the q-method from brief 6.2 of the space-operations candidates and from candidate 3 of the plan that orders them.  This record gives each decision with its reason, and the findings of an independent review with the response to each.

## Decisions

| Question | Choice | Reason |
|---|---|---|
| TRIAD's error bound | `F = 2 arcsin √h` from the decomposition of the error rotation into a rotation that carries the first observation onto its reference and a rotation about that reference | The classical bounds of Shuster and Oh are statistical.  The decomposition gives an exact identity for the half-angle, `cos(φ/2) = cos(α/2) cos(ψ/2)`, and a deterministic bound on `ψ` from the Cauchy–Schwarz inequality in the plane.  A numerical check with adversarial optimization found no error above `F`, and to first order `F` exceeds the worst error by a factor of at most `(1 + √5)/2`. |
| Form of the error hypothesis | One bound `ε_i` on `∠(R(q) b̄_i, r̄_i)` for each observation | It combines the sensor's error and the reference's error by the triangle inequality, and it is the form that `plan_premise` uses for its own premises. |
| Output of TRIAD | Intervals of the nine entries of the matrix, and a bound that covers every matrix in them | A quaternion output needs a branch on the largest diagonal entry, which interval arithmetic evaluates on both sides.  A bound that covers every matrix in the intervals lets a caller use any of them, such as the midpoint, with no further rounding analysis. |
| Arithmetic | The interval layer with `enclosure_def` for the frames, the matrix, and `h` | Each part's enclosure theorem follows from the command, and the real functions it declares are the model's formulas, related to the vector form by `triadOf_eq` and `boundOf_eq`. |
| Box term | `arcsin(η/(1 - η))` for `η ≤ 1/4` | The review notes that `arcsin η` suffices.  The term is below `1e-13` for every well-posed input, so the looser form costs nothing measurable, and its proof exists. |
| Pivots of the q-method's certificate | Intervals that enclose the exact pivots, in place of the plan's exact rationals | The normalized observations make `K` irrational, so exact rational arithmetic would apply to a matrix other than the model's.  Interval pivots enclose the exact pivots of the model's `K`, and their signs certify the inertia when no interval contains zero. |
| Order of the q-method's factorization | A symmetric permutation that puts the diagonal entry of largest magnitude first at each stage | The review constructed a well-posed attitude at which the first pivot of the unpermuted factorization is zero. |
| Cut `λc` | `λ̂2 + (λ̂1 - λ̂2)/16` from the solver's estimates | The review's model showed that the bound to the true attitude falls by about half from a cut at mid-gap to a cut near `λ2`, and a sixteenth of the gap keeps the pivots away from zero. |

## Review

A fresh agent reviewed the draft against the brief, the plan, and the slew planner's conventions, without the derivation of the bound or the author's scripts.  It built a model in Python and mpmath, recomputed every claim that admits computation, tried to falsify `F` on 295 adversarial cases, and ran wrong programs and wrong bounds against the stated theorems and tests.  It confirmed A1 to A4 on 20,000 inputs, `F` with equality attained at `ε1 = 0`, the composition form of `F`, the first-order worst case and the factor `(1 + √5)/2`, Davenport's identity in the body-to-inertial convention, `K_i² = I`, the inertia argument, the one-vector Davis–Kahan bound, and the `2(α + β)` claim.

| Finding | Verification | Response |
|---|---|---|
| 1. A5's condition `x < 1` holds for parallel references, where `x` is zero and `T` is singular | Confirmed with `r1 = r2` | The condition is `sin(ε1 + ε2) < |r̄1 × r̄2|`, as `triad_error` states it in Lean |
| 2. TRIAD's statuses overlap for a non-finite error bound with a short cross product | Confirmed | The table states the conditions of status 1 first, then those of status 2, and moves non-finite error bounds to status 2 only |
| 3. The theorems admit a program that always rejects or returns a large `err` | Confirmed | The tests require status 0 on a stated region and `err` within `1e-12` of its formula, and the requirements state that no theorem excludes such a program |
| 4. The q-method's `λc`, sweeps, and bounds are unspecified | Confirmed | The interface states eight sweeps, `λc`, and both formulas |
| 5. The solver determines `err`, against the text | Confirmed | Sentence corrected |
| 6. The q-method lacks its real-number lemmas and its looseness | Confirmed: the bound exceeds the worst error by `1/sin(θ/2)` for two observations | Q3a to Q3c added, and the looseness stated |
| 7. `knowledge_share` has no row | Confirmed | A8 added with its statement |
| 8. Mathlib has Sylvester's law for quadratic forms | Confirmed by the reviewer in `LinearAlgebra/QuadraticForm` | Sentence corrected, and the lemmas named |
| 9. Status conditions use unstated endpoints, and a zero vector fits no q-method status | Confirmed | Endpoints stated, and a vector of zero length fails the input conditions |
| 10. A2's `α` is unnamed | Confirmed | Stated |
| 11. Q2's hypothesis is imprecise | Agreed | Deferred to the design of the q-method, which states the factorization in Lean |
| 12. An unpermuted LDLᵀ fails at well-posed attitudes | Confirmed by the constructed case | Symmetric permutation adopted |
| 13. The tests miss a dropped box term, a lower endpoint as `err`, and errors in `h` at first order | Confirmed | The containment test compares `err` with its formula in both directions in high precision and includes the reviewer's cases |
| 14. The memory cap, the cost bound, and the deviation from exact rationals are unstated | Confirmed | Stated, and the deviation recorded above |
| 15. The box term is loose | Confirmed | Declined, as the decisions table explains |
| 16. Paragraphs of one sentence, an algorithm given intent, and unnamed enclosures | Confirmed | Rewritten |

The review's wrong programs, with what detects each, were TRIAD transposed (A1, A4, A6, and the containment test), one frame left-handed (A3), TRIAD anchored on the second observation (A1 and the containment test), `ε2` in place of `ε1` in `h` (A6 and the formula comparison), a dropped box term or a lower endpoint as `err` (A6 and the formula comparison), and the q-method with the conjugate `K` (Q1 and Q4).  A frame left-handed on both sides gives the same `T` and is no defect.  No case detects a program that always rejects, which the region of required status 0 now does.

## Open items

1. The q-method, whose design must fix the Lean form of Q2's factorization.
2. An onboard build on A64 or the Cortex-M7.
3. A bound with `ε1 |cos θ|` in place of `ε1` in `x`, which would reach TRIAD's first-order worst case.
