# Attitude determination requirements

## Purpose and scope

The programs compute the attitude of a spacecraft from directions measured in the body frame, such as the directions of the Sun, the magnetic field, and stars, and from the same directions in the inertial frame, which an ephemeris, a field model, or a catalog gives.  Each program returns, with the attitude, a bound on the angle between it and the true attitude in terms of bounds on the observations' angular errors.  The bound is the knowledge-error share of the input `ε` of the slew planner's `plan_premise`.  TRIAD, which takes two observations, comes first, and the q-method, which takes up to 16 weighted observations, follows.

The programs are ground programs compiled by `verified_compile` to WebAssembly, whose call theorems the compiled modules carry, and they serve as the reference for an onboard version on A64 or the Cortex-M7, which lies outside these requirements.  Both programs run a fixed number of operations for a given number of observations, with no search and no loop whose count depends on the data.  The requirements leave out the sensor models that turn raw outputs into directions, the reference models that give the inertial directions, filtering over time, statistical error bounds, and the other estimators, such as QUEST and the ESOQ methods.

## Conventions

A vector is a triple of reals and a quaternion `q = [w, x, y, z]` a quadruple, as in [the slew planner](../Slew/README.md#the-planning-problem).  The attitude `R(q)` maps body coordinates to inertial coordinates by `R(q) v = q̄ v q̄*`, where `q̄ = q/|q|`, and for a vector `v`, `v̄ = v/|v|`.  The angle `∠(a, b)` between two vectors is Mathlib's `InnerProductGeometry.angle`, the arccosine of `a · b/(|a| |b|)`, which is `π/2` when either vector is zero, and the slew planner's `plan_premise` states its hypotheses with the same angle.

A map `M` of vectors lies within `ε` of an attitude `R(q)` when `∠(M v, R(q) v) ≤ ε` for every unit vector `v`.  For a rotation `M`, the least such `ε` is the angle of the rotation `M R(q)ᵀ`.  `plan_premise` takes a flown map within `ε` of the commanded attitude, so a bound of this form on the knowledge error adds to a bound of the same form on the control error.

## Error model

An observation is a body direction `b`, the measurement, and an inertial direction `r`, the reference.  Its error bound `ε ≥ 0` states that the true attitude `R(q)` carries `b̄` within angle `ε` of `r̄`: `∠(R(q) b̄, r̄) ≤ ε`.  If the measurement lies within `δ` of the true body direction and the reference within `ρ` of the true inertial direction, then `ε = δ + ρ` satisfies this, by the triangle inequality for angles and because `R(q)` preserves angles.  The theorems take the bounds as premises, and nothing in them concerns how a sensor meets its bound.

## TRIAD

### Model

For vectors `a` and `b`, `frame(a, b)` is the triple `(ā, n, ā × n)` with `n = (a × b)/|a × b|`.  With `(t1, t2, t3) = frame(b1, b2)` from the measurements and `(s1, s2, s3) = frame(r1, r2)` from the references, TRIAD's attitude is the matrix `T = s1 t1ᵀ + s2 t2ᵀ + s3 t3ᵀ`, which maps `t_i` to `s_i`.  The entry `T_jk` in row `j` and column `k` is the inertial coordinate `j` of the image of body axis `k`.  `T` maps `b̄1` onto `r̄1` exactly, and the second observation fixes only the rotation about `r̄1`.

The error bound uses `sin θ = |r̄1 × r̄2|`, `d = ε1 + ε2`, `x = sin d / sin θ`,

`h = sin²(ε1/2) + cos²(ε1/2) · x²/(2 (1 + √(1 - x²)))`,

and `F = 2 arcsin √h`.  It requires `0 ≤ ε1`, `0 ≤ ε2`, `d < π/2`, and `sin d < sin θ`, which together say `d < θ < π - d` and exclude parallel references, for which `x` would be zero.  `F` is the angle of the product of a rotation by `ε1` and a rotation by `arcsin x` about perpendicular axes, and for small angles `F ≈ √(ε1² + d²/sin²θ)`.  The derivation decomposes the error rotation into a rotation that carries the first observation onto its reference and a rotation about the reference, and bounds the second by the tangents from `r̄1` to the cap of radius `d` about `r̄2`.  To first order, the largest error over the observations within their bounds is `√(ε1² + (ε2 + ε1 |cos θ|)²/sin²θ)`, so to first order `F` exceeds it by a factor of at most `(1 + √5)/2 ≈ 1.618`, at `θ = 90°` and `ε2 = 0.618 ε1`, and by at most 2 percent when `ε2 ≥ 50 ε1`.

### Interface

| Entry | Arguments | Result |
|---|---|---|
| `triad` | `b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2 : Float` | `Estimate`: status, nine intervals `m11` to `m33`, `err` |

The arguments are the two measurements, the two references, and the error bounds `ε1` and `ε2` in radians.  The vectors need not have unit length.  An interval is the interval layer's record of a status word and two endpoints.  `err` is a float.

| Status | Meaning |
|---|---|
| 0 | The intervals contain the entries of `T`, and every matrix whose entries lie in them is within `err` of every true attitude that the error bounds admit. |
| 1 | No result: an interval operation that computes the lengths of `b1`, `b1 × b2`, `r1`, and `r1 × r2` or the entries of `T` rejects, which a non-finite vector component, a zero or nearly zero vector or cross product, or an overflow causes, or the lower endpoint of one of the four lengths is not positive. |
| 2 | The intervals contain the entries of `T`, and the program gives no bound: an error bound is negative or not finite, the upper endpoint of the interval of `ε1 + ε2` exceeds 1.5, the upper endpoint of the interval of `x` is not below 1, the upper endpoint of the interval of `η` exceeds 1/4, or an operation of the bound rejects. |

The program tests the conditions of status 1 first and those of status 2 next.  For status 1 the intervals are rejected and `err` is zero, and for status 2 `err` is zero.  For status 0, `err` is the upper endpoint of an accepted interval, so it is finite.

### Method

The program evaluates `frame` and `T` with the interval operations on the point intervals of the inputs.  It computes `sin θ` as `|r1 × r2|/(|r1| |r2|)`, `x`, `h`, and `F` with `enclosure_def`, whose `sinI` and `cosI` enclose the library's `sin` and `cos`, and it encloses `arcsin` with the library's `asin` through the interval layer's `increasing`.  The box term covers the choice of a matrix in the intervals: with `η` the square root of the sum of the squared widths of the nine intervals, every matrix `M` in them satisfies `|M v - T v| ≤ η` for a unit `v`, and `|T v| = 1`, so `∠(M v, T v) ≤ arcsin(η/(1 - η))` for `η ≤ 1/4`.  `err` is the upper endpoint of an interval that contains `F + arcsin(η/(1 - η))`.

### Theorems

The real values of the inputs define `b1`, `b2`, `r1`, `r2`, `ε1`, and `ε2`, and `T` is the model's matrix of them.

| Code | Theorem | Statement |
|---|---|---|
| A1 | `triad_first` | For nonzero `b1` and `r1` and nonzero `b1 × b2` and `r1 × r2`, `T b̄1 = r̄1`. |
| A2 | `triad_second` | Under A1's hypotheses, `T b̄2 = α r̄1 + β r̄2` with `β = \|b̄1 × b̄2\|/\|r̄1 × r̄2\| > 0` and `α = b̄1 · b̄2 - β r̄1 · r̄2`. |
| A3 | `triad_rotation` | Under A1's hypotheses, `T` preserves dot and cross products. |
| A4 | `triad_exact` | Under A1's hypotheses, if `R(q) b̄1 = r̄1` and `R(q) b̄2 = r̄2` for a nonzero `q`, then `T v = R(q) v` for every `v`. |
| A5 | `triad_error` | For nonzero `b1`, `b2`, `r1`, and `r2`, `0 ≤ ε1`, `0 ≤ ε2`, `ε1 + ε2 < π/2`, `sin (ε1 + ε2) < \|r̄1 × r̄2\|`, and a nonzero `q` with `∠(R(q) b̄1, r̄1) ≤ ε1` and `∠(R(q) b̄2, r̄2) ≤ ε2`, `T` is within `F` of `R(q)`. |
| A6 | `triad_sound`, `triad_bound` | If `triad` returns status 0 or 2, `b1`, `r1`, `b1 × b2`, and `r1 × r2` are not zero, and each interval contains its entry of `T`.  If it returns status 0, the conditions of A5 hold, and for every nonzero `q` with the error bounds of A5 and every matrix `M` whose entries lie between the endpoints of the intervals, `M` is within `err` of `R(q)`. |
| A8 | `knowledge_share` | If `triad` returns status 0, `M` lies in its intervals, a map `C` satisfies `∠(M v, C v) ≤ ε_c` for every unit `v`, and a nonzero `q` meets the error bounds of A5, then `∠(R(q) v, C v) ≤ ε_c + err` for every unit `v`, the hypothesis of `plan_premise` on its flown map. |
| A7 | `compiled.triad.implements`, `compiled.bytes`, `triad_file` | The module's `triad` export returns the words of `triad`, or traps at `unreachable`, and the written file holds the module. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  The program allocates no memory that depends on its inputs and runs a fixed sequence of operations, whose only data-dependent loops are those of the library's `sin`, `cos`, and `asin`, which have fixed bounds.

## The q-method

### Model

The observations `(b_i, r_i)` have weights `a_i > 0` and error bounds `ε_i`.  Wahba's loss of an attitude `R(q)` is `L(q) = ½ Σ a_i |r̄_i - R(q) b̄_i|²`.  Davenport's matrix `K` is the symmetric 4×4 matrix with `qᵀ K q = Σ a_i r̄_i · (q b̄_i q*)` for every quaternion `q = [w, x, y, z]`: with `B = Σ a_i r̄_i b̄_iᵀ`, `σ = tr B`, `S = B + Bᵀ`, and `z = Σ a_i b̄_i × r̄_i`, `K = [[σ, zᵀ], [z, S - σ I]]`, so `L(q) = Σ a_i - qᵀ K q` for a unit `q`.  A unit quaternion that maximizes `qᵀ K q` on the unit sphere exists by compactness, minimizes `L`, and is an eigenvector of `K` for its largest eigenvalue `λ1 = eᵀ K e`.  The theorems name such a maximizer `e`.

A cut `c` separates `λ1` from the rest of the spectrum when every unit `q` perpendicular to `e` has `qᵀ K q < c < λ1`.  The certificate is the symmetric factorization of `K - c I` that at each stage exchanges the first remaining index with a chosen one and eliminates it, so that its pivots `d1` to `d4` are the first diagonal entries of `K - c I` and of its successive Schur complements after the exchanges.  For any choice of exchanges, if the pivots with those exchanges are one positive and three negative, then the quadratic form of `K - c I` is positive at some vector and negative at every nonzero vector of some hyperplane.  The proof is an induction over the stages with two properties of a symmetric matrix: negative definiteness, and a positive form at some vector together with a negative form at every nonzero vector of some hyperplane.  A negative pivot carries either property of the Schur complement to the matrix, and a positive pivot turns a negative definite Schur complement into the second property.  A plane spanned by `e` and a unit `q ⊥ e` with `qᵀ K q ≥ c` would meet that hyperplane in a nonzero vector at which the form is not negative, so the property gives the cut.  The proof uses this hyperplane argument and not Sylvester's law as Mathlib states it (`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`), because the factorization gives the hyperplane and the positive vector directly.

The Davis–Kahan bound for one vector states that for a unit `v`, a real `μ > c`, and the residual `ρ = |K v - μ v|`, the component of `v` perpendicular to `e` has length at most `ρ/(μ - c)`.  The proof splits `v = (v · e) e + w` with `w ⊥ e`, notes that the part of `K v - μ v` perpendicular to `e` is `(K - μ I) w`, and bounds `wᵀ (K - μ I) w ≤ (c - μ) |w|²` with the cut.  Mathlib has no bound of this kind.

The true attitude's quaternion has a small residual for `K`.  The matrix `K_i` of one observation of vectors `b` and `r` satisfies `K_i² = |b|² |r|² I`, so for unit vectors and a unit `q` the residual `|K_i q - c_i q|` with `c_i = qᵀ K_i q` is `√(1 - c_i²)`, the sine of `∠(R(q) b̄_i, r̄_i)`.  A true attitude `q_t` with error bounds in `[0, π/2]` therefore has `q_tᵀ K q_t ≥ μ_t = Σ a_i cos ε_i` and a residual at most `ρ_t = Σ a_i sin ε_i`.  For unit quaternions `p` and `q` within angles `α` and `β` in `[0, π/2]` of the line of `e`, `|p · e| ≥ cos α` and `|q · e| ≥ cos β`, `R(p)` lies within `2 (α + β)` of `R(q)`: when `α + β < π/2`, `|p · q| ≥ cos(α + β)` and the rotation `R(p) R(q)ᵀ` has the angle `2 arccos |p · q|`, and otherwise `2 (α + β) ≥ π`.

### Interface

| Entry | Arguments | Result |
|---|---|---|
| `qmethod` | `xs : Array Float`: `n`, then `n` records `bx by bz rx ry rz a ε` | `Array Float`: status, `w`, `x`, `y`, `z`, `errOpt`, `err`, `c` |

`n` is a whole number from 2 to 16, the input has `1 + 8n` values, every value is finite, each `a` is positive, and each `ε` lies in `[0, 1.5]`.  The vectors need not have unit length, and the program requires the lower endpoint of the interval of each length above zero.  The program encloses each observation's term `a K(b̄, r̄)` as `k K(b, r)` with `k = a/(|b| |r|)`, which has the same value and divides no vector, and sums the terms, `Σ a sin ε`, and `Σ a cos ε` with the interval operations.  It runs eight cyclic Jacobi sweeps, an unproved solver, on the midpoints of the intervals of `K`, takes as `q̂` the column of the largest diagonal estimate `λ̂1`, scaled in binary64 to unit length with `w ≥ 0`, and as `λ̂2` the largest of the other three, and computes `c = λ̂2 + (λ̂1 - λ̂2)/16` in binary64.  The tests check the unit length and the sign of `q̂`, and no theorem states them, since the attitude `R(q̂)` normalizes `q̂` and does not depend on its sign.

The program encloses the pivots of the factorization of `K - c I` that at each stage moves the remaining diagonal interval whose endpoints have the largest magnitude to the front.  It encloses `|q̂|²`, the Rayleigh quotient `μ̂ = q̂ᵀ K q̂/|q̂|²`, and `ρ̂ = |K q̂ - μ̂ q̂|/|q̂|`, clamping the interval of `ρ̂²` at zero before its square root, since outward rounding extends the interval of a residual near zero below zero, where the square root rejects.  With `ρ_t = Σ a_i sin ε_i` and `μ_t = Σ a_i cos ε_i`, it returns the upper endpoints of the intervals of

`errOpt = 2 arcsin (ρ̂/(μ̂ - c))` and `err = 2 (arcsin (ρ̂/(μ̂ - c)) + arcsin (ρ_t/(μ_t - c)))`,

and `c`, so that a caller and the tests can compare the certificate's claim `λ2 < c < λ1` with an independent eigendecomposition.  For two observations of equal weight and equal bounds `ε` with exact data, the largest error that the bounds admit is `ε/sin(m/2)` with `m = min(θ, π - θ)`, and `err` with `c = λ2` exceeds it by the factor `1/sin(m/2)`.  The program's cut adds about 16/15, for a factor of 1.51 at `θ = 90°` and 6.14 at 20° and 160°, and measurements displaced within their bounds raise the factor.  Except within about 2° of `θ = 90°`, `err` exceeds TRIAD's `F` for two observations, so the q-method serves more than two.

| Status | Meaning |
|---|---|
| 0 | The pivots certify the cut `c`, `R(q̂)` lies within `errOpt` of `R(e)` for every maximizer `e`, and within `err` of every true attitude that the error bounds admit. |
| 1 | The input fails the conditions above, an interval operation that encloses `K`, a length, or one of the two sums rejects, or the lower endpoint of a length is not positive. |
| 2 | The input is valid, and the certificate failed: a pivot interval is rejected or contains zero, the pivots' signs are not one positive and three negative, the lower endpoint of the interval of `\|q̂\|²`, of `μ̂ - c`, or of `μ_t - c` is not positive, the interval of an arcsine's argument does not lie in `[-1, 1]`, or an operation of the bounds rejects. |

For status 1 and 2 the other seven values are zero.

### Theorems

`K` is Davenport's matrix of the real values of the inputs, and `c` the real value of the output cut.

| Code | Theorem | Statement |
|---|---|---|
| Q1 | `wahba_eq` | For observations with nonzero vectors and a unit `q`, `L(q) = Σ a_i - qᵀ K q`. |
| Q2 | `onePos_of_pivots`, `inertia_cut` | For any choice of exchanges, if the four pivots of the factorization of a symmetric 4×4 matrix `A` with those exchanges are one positive and three negative, then `A` has a vector with a positive form and a hyperplane on which the form is negative at every nonzero vector.  If `K - c I` has this property, then every maximizer `e` has `c < λ1 = eᵀ K e`, and every unit `q ⊥ e` has `qᵀ K q < c`. |
| Q2a | `exists_isMax`, `IsMax.apply_eq`, `isMax_unique` | A maximizer exists, it is an eigenvector of `K` for `λ1`, and under the hypothesis of Q2 it is unique up to sign. |
| Q3 | `davis_kahan` | Under Q2's conclusion, for a unit `v` and `μ > c`, `√(1 - (v · e)²) ≤ \|K v - μ v\|/(μ - c)`. |
| Q3a | `apply_apply_obsK`, `resid_obsK` | `K_i² = \|b\|² \|r\|² I`, and for unit `b`, `r`, and `q`, `\|K_i q - c_i q\|² = 1 - c_i²` with `c_i = qᵀ K_i q = r · R(q) b`. |
| Q3b | `true_near` | Under Q2's conclusion, for observations with nonzero vectors, weights at least zero, error bounds in `[0, π/2]`, and `c < μ_t`, every nonzero `q` with the error bounds has `1 - (q̄ · e)² ≤ (ρ_t/(μ_t - c))²`: its line lies within the angle `arcsin (ρ_t/(μ_t - c))` of the line of `e`. |
| Q3c | `rotation_near` | For unit `p`, `q`, and `e` with `\|p · e\| ≥ cos α` and `\|q · e\| ≥ cos β`, `α` and `β` in `[0, π/2]`, `R(p)` lies within `2 (α + β)` of `R(q)`. |
| Q4 | `valid_cases`, `qmethod_sound` | If `qmethod` returns status 0, the input meets its conditions (`InputOk`): the first value is the whole number `n` of observations from 2 to 16, the input has `1 + 8n` values, read as a word count, those values are finite, and the weights are positive and the error bounds in `[0, 1.5]`; the observations' vectors are not zero; `q̂`, `errOpt`, `err`, and `c` are finite; `K - c I` has the property of Q2; a maximizer exists and is unique up to sign; every maximizer `e` has `c < eᵀ K e` and `qᵀ K q < c` for every unit `q ⊥ e`; the real `q̂` of outputs 1 to 4 is not zero; `R(q̂)` lies within `errOpt` of `R(e)` for every maximizer `e`; and for every nonzero `q` with `∠(R(q) b̄_i, r̄_i) ≤ ε_i` for every `i`, `R(q̂)` lies within `err` of `R(q)`. |
| Q4a | `qmethod_status_two` | If `qmethod` returns status 2, the input meets its conditions (`InputOk`). |
| Q5 | `compiled.qmethod.implements`, `qmethod_bound`, `qmethod_call`, `qmethod_file` | The module's `qmethod` export returns the words of `qmethod`, a call raises the allocator's `top` by at most 712 bytes, the charge of the array literal of its eight result values, and from a ready store with room for them the export returns `qmethod xs` without a trap.  The written file holds the module. |
| Q6 | `qmethod_knowledge` | If `qmethod` returns status 0, a map `C` lies within `ε_c` of `R(q̂)`, and a nonzero `q` meets the error bounds, then `∠(R(q) v, C v) ≤ ε_c + err` for every unit `v`, the hypothesis of `plan_premise` on its flown map. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  The program allocates only its result, an array literal of eight values, and the number of its operations depends only on `n` and on the loops of the library's `sin`, `cos`, and `asin`, which have fixed bounds.

## The slew planner's ε

`plan_premise` takes a flown map `F` within `ε` of the commanded attitude.  When an attitude estimator's estimate `M` is within `ε_k` of the true attitude and the controller keeps `M` within `ε_c` of the commanded attitude, the true attitude is within `ε_c + ε_k` of the commanded attitude, by the triangle inequality for angles.  The theorem `knowledge_share` states this for TRIAD's `err` with `M` any matrix in its intervals, and `qmethod_knowledge` for the q-method's `err` with `M = R(q̂)`, and each gives `plan_premise`'s hypothesis with `ε = ε_c + err`.  The control error `ε_c` and the time between estimates remain the caller's.

## Tests

The oracle is an implementation in Python, run with `uv run`, that computes TRIAD and its bound with mpmath at 50 digits from the real values of the inputs, written apart from the program.  For each generated input, the containment test requires the oracle's matrix in the program's intervals, `err` at or above the oracle's `F + arcsin(η/(1 - η))` with `η` from the returned intervals, and `err` below that value plus `1e-12`.  It requires status 0 on the region of well-posed inputs, `θ` from 10° to 170°, vector lengths from `1e-3` to `1e3`, and `ε1 + ε2` at most 0.9 times `min(θ, π - θ)`, and it checks the stated status on parallel and nearly parallel vectors, zero vectors, non-finite values, negative error bounds, `ε1 + ε2` above 1.5, and `x` near 1.  The cases include `ε1 ≠ ε2`, `ε2 = 0` with `ε1 = 0.1`, `θ` of 30° and 150°, and random true attitudes.  A second test draws true attitudes and observations within their error bounds, at random and in the direction of the first-order worst case, and requires the angle between the image of the midpoint matrix and the true image of a unit vector below `err` for the vectors that maximize it.  The adversarial optimization of the errors' directions belongs to the derivation's numerical check and to the review's model, which run apart from the program.  The module test compares the module's `triad` export with native Lean bit for bit on the same inputs.

The q-method's oracle computes Davenport's matrix in the form `B`, `σ`, `S`, `z` of the model at 50 digits and its eigendecomposition with mpmath.  For every result of status 0 it requires `λ2 < c < λ1`, the angle `2 arccos |q̄ · e|` between the attitudes of `q̂` and of the eigenvector `e` of `λ1` at most `errOpt`, `μ̂ > c`, `μ_t > c`, the sines `ρ̂/(μ̂ - c)` and `ρ_t/(μ_t - c)` at most 1, and `errOpt` and `err` at or above their formulas, with `μ̂` and `ρ̂` computed from the exact `K` and the returned `q̂`, with the returned `c`, and less than `1e-12` above them.  It requires `q̂` of unit length within `1e-15` with `w ≥ 0`.  It requires status 0 on a generated sample of inputs: from 2 to 16 observations with references in random directions, two references at an angle from 20° to 160° when there are two, weights from 0.5 to 2, error bounds up to `3e-2`, vector lengths from `1e-3` to `1e3`, and measurements displaced within their bounds in random directions and in directions perpendicular to the plane of each reference and one common axis.  The region that this sample draws from also holds inputs for which no cut gives a bound: three references within 10° of each other, with weights 1 and bounds `3e-2`, have `ρ_t/(μ_t - λ2) = 1.13`, so status 2 is the only correct result there.  A second set applies `certify` to the program's quaternion turned by `1e-6`, `1e-4`, and `1e-2` toward the second eigenvector estimate, so that `errOpt` is large enough to compare with its formula.  For every input with a recorded true attitude it checks that the true attitude meets the error bounds and lies within `err` of `R(q̂)`.  It checks status 1 for a count that is not whole or lies outside `[2, 16]`, each also with an input whose length fits the count or its whole part, an input of the wrong length, non-finite values, weights that are zero or negative, error bounds outside `[0, 1.5]`, zero vectors, and overflow, and status 2 for observations that leave the largest eigenvalue double and for error bounds whose sine bound exceeds 1.  It checks status 0 for an input at which the first diagonal entry of `K - c I` is zero, so that only the pivoting factorization succeeds.  The module test compares the module's `qmethod` export with native Lean bit for bit on the inputs of `qmethod`.

## What lies outside the theorems

The theorems concern the stated model: rigid rotations, directions without parallax or aberration, and error bounds that hold.  A sensor that violates its bound violates the premise, and nothing in the theorems detects it.  TRIAD's bound can exceed the largest error by the factor of the model section, and the theorems bound no interval's width.  The q-method's `errOpt` concerns the maximizer of Davenport's matrix of the real values of the inputs, while `err` concerns the true attitude through the error bounds.  The solver determines `q̂`, `c`, `errOpt`, `err`, and whether the certificate succeeds, and Q4 holds whatever it returns.  No theorem excludes a program that always rejects or returns a larger bound than its formula, so the tests require status 0 on TRIAD's stated region of well-posed inputs and on the q-method's generated sample, and compare the bounds with their formulas.
