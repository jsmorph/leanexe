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
| A2 | `triad_second` | Under A1's hypotheses, `T b̄2 = α r̄1 + β r̄2` with `β = |b̄1 × b̄2|/|r̄1 × r̄2| > 0` and `α = b̄1 · b̄2 - β r̄1 · r̄2`. |
| A3 | `triad_rotation` | Under A1's hypotheses, `T` preserves dot and cross products. |
| A4 | `triad_exact` | Under A1's hypotheses, if `R(q) b̄1 = r̄1` and `R(q) b̄2 = r̄2` for a nonzero `q`, then `T v = R(q) v` for every `v`. |
| A5 | `triad_error` | For nonzero `b1`, `b2`, `r1`, and `r2`, `0 ≤ ε1`, `0 ≤ ε2`, `ε1 + ε2 < π/2`, `sin (ε1 + ε2) < |r̄1 × r̄2|`, and a nonzero `q` with `∠(R(q) b̄1, r̄1) ≤ ε1` and `∠(R(q) b̄2, r̄2) ≤ ε2`, `T` is within `F` of `R(q)`. |
| A6 | `triad_sound`, `triad_bound` | If `triad` returns status 0 or 2, `b1`, `r1`, `b1 × b2`, and `r1 × r2` are not zero, and each interval contains its entry of `T`.  If it returns status 0, the conditions of A5 hold, and for every nonzero `q` with the error bounds of A5 and every matrix `M` whose entries lie between the endpoints of the intervals, `M` is within `err` of `R(q)`. |
| A8 | `knowledge_share` | If `triad` returns status 0, `M` lies in its intervals, a map `C` satisfies `∠(M v, C v) ≤ ε_c` for every unit `v`, and a nonzero `q` meets the error bounds of A5, then `∠(R(q) v, C v) ≤ ε_c + err` for every unit `v`, the hypothesis of `plan_premise` on its flown map. |
| A7 | `compiled.triad.implements`, `compiled.bytes`, `triad_file` | The module's `triad` export returns the words of `triad`, or traps at `unreachable`, and the written file holds the module. |

Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.  The program allocates no memory that depends on its inputs and runs a fixed sequence of operations, whose only data-dependent loops are those of the library's `sin`, `cos`, and `asin`, which have fixed bounds.

## The q-method

### Model

The observations `(b_i, r_i)` have weights `a_i > 0` and error bounds `ε_i`.  Wahba's loss of an attitude `R(q)` is `L(q) = ½ Σ a_i |r̄_i - R(q) b̄_i|²`.  Davenport's matrix `K` is the symmetric 4×4 matrix with `qᵀ K q = Σ a_i r̄_i · (q b̄_i q*)` for every quaternion `q`, so `L(q) = Σ a_i - qᵀ K q` for a unit `q`.  A unit quaternion that maximizes `qᵀ K q` on the unit sphere, which exists by compactness, minimizes `L` and is an eigenvector of `K` for its largest eigenvalue `λ1`.  The theorems name one such maximizer `e`.

A cut `λc` separates `λ1` from the rest of the spectrum when every unit `q` perpendicular to `e` has `qᵀ K q < λc < λ1`.  An LDLᵀ factorization of `K - λc I` in exact arithmetic with pivots `d1` to `d4` and exactly one positive pivot `d_k`, the others negative, establishes this: the quadratic form of `K - λc I` is `Σ d_i y_i²` with `y = Lᵀ q`, so it is negative on the hyperplane `y_k = 0`, and a plane spanned by `e` and a unit `q ⊥ e` with `qᵀ K q ≥ λc` would meet that hyperplane in a vector where the form is not negative.  Sylvester's law of inertia states the same count of eigenvalues below `λc`, and the proof needs only the hyperplane.  Mathlib states Sylvester's law for quadratic forms (`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared` and the signature lemmas of `LinearAlgebra/QuadraticForm/Signature.lean`), and the design of this increment decides whether the proof uses them or the hyperplane argument directly.

The Davis–Kahan bound for one vector states that for a unit `v`, a real `μ > λc`, and the residual `ρ = |K v - μ v|`, the component of `v` perpendicular to `e` has length at most `ρ/(μ - λc)`.  The proof splits `v = c e + w` with `w ⊥ e`, notes that the part of `K v - μ v` perpendicular to `e` is `(K - μ I) w`, and bounds `wᵀ (K - μ I) w ≤ (λc - μ) |w|²`.  Mathlib has no bound of this kind.

The true attitude's quaternion has a small residual for `K`.  Each observation's matrix `K_i` satisfies `K_i² = I`, so for a unit `q` its residual `|K_i q - c_i q|` with `c_i = qᵀ K_i q` is `√(1 - c_i²)`, the sine of `∠(R(q) b̄_i, r̄_i)`.  The true attitude `q_t` therefore has `μ_t = q_tᵀ K q_t ≥ Σ a_i cos ε_i` and a residual at most `Σ a_i sin ε_i`.  For unit quaternions `p` and `q` within angles `α` and `β` of the line of `e`, with `α + β ≤ π/2`, `R(p)` lies within `2 (α + β)` of `R(q)`.

### Interface

| Entry | Arguments | Result |
|---|---|---|
| `qmethod` | `xs : Array Float`: `n`, then `n` records `bx by bz rx ry rz a ε` | `Array Float`: status, `w`, `x`, `y`, `z`, `errOpt`, `err` |

`n` is a whole number from 2 to 16, the input has `1 + 8n` values, every value is finite, each vector has a positive length, which need not be 1, each `a` is positive, and each `ε` lies in `[0, 1.5]`.  The program finds an eigenpair of the computed `K` with an unproved solver, eight cyclic Jacobi sweeps, whose two largest eigenvalue estimates are `λ̂1 ≥ λ̂2`, and takes `λc = λ̂2 + (λ̂1 - λ̂2)/16`.  It encloses `K` with the interval operations and encloses the pivots of the LDLᵀ factorization of `K - λc I` after a symmetric permutation that puts the diagonal entry of largest magnitude first at each stage, which leaves the inertia unchanged.  It encloses the Rayleigh quotient `μ̂` and the residual `ρ̂` of the normalized computed eigenvector `q̂`.  With `ρ_t = Σ a_i sin ε_i` and `μ_t = Σ a_i cos ε_i`, it returns the upper endpoints of the intervals of

`errOpt = 2 arcsin (ρ̂/(μ̂ - λc))` and `err = 2 (arcsin (ρ̂/(μ̂ - λc)) + arcsin (ρ_t/(μ_t - λc)))`.

Each arcsine requires the lower endpoint of its denominator above zero and the upper endpoint of its argument at most 1.  For two observations at angle `θ` with `λc = λ2`, the review's model found that `err` exceeds the largest error by the factor `1/sin(θ/2)`, so the q-method's bound is looser than TRIAD's `F` for two observations and serves the case of more than two.

| Status | Meaning |
|---|---|
| 0 | `R(q̂)` lies within `errOpt` of `R(e)` for every maximizer `e`, and within `err` of every true attitude that the error bounds admit. |
| 1 | The input fails the conditions above, or an operation that encloses `K` rejects. |
| 2 | The input is valid, and the certificate failed: a pivot interval contains zero, the pivots' signs are not three negative and one positive, or a denominator or an argument of an arcsine fails its test. |

For status 1 and 2 the other six values are zero.

### Theorems

| Code | Theorem | Statement |
|---|---|---|
| Q1 | `wahba_eq` | For a unit `q`, `L(q) = Σ a_i - qᵀ K q`. |
| Q2 | `inertia_cut` | If `K - λc I` has an LDLᵀ factorization with one positive pivot and three negative pivots, then `λc < λ1` and every unit `q ⊥ e` has `qᵀ K q < λc`, for every maximizer `e`. |
| Q3 | `davis_kahan` | Under Q2's conclusion, for a unit `v` and `μ > λc`, `√(1 - (v · e)²) ≤ |K v - μ v|/(μ - λc)`. |
| Q3a | `residual_obs` | For unit `b`, `r`, and `q`, `K_i² = I`, and `|K_i q - c_i q| = √(1 - c_i²)` with `c_i = r · R(q) b = cos ∠(R(q) b, r)`. |
| Q3b | `true_near` | Under Q2's conclusion and `Σ a_i cos ε_i > λc`, every unit `q` with the error bounds lies within the line angle `arcsin (ρ_t/(μ_t - λc))` of `e`. |
| Q3c | `rotation_near` | For unit quaternions `p` and `q` within line angles `α` and `β` of a unit `e`, `R(p)` lies within `2 (α + β)` of `R(q)`. |
| Q4 | `qmethod_sound` | If `qmethod` returns status 0, the real `q̂` of outputs 1 to 4 is not zero, `errOpt` and `err` are finite, the maximizer is unique up to sign, the exact pivots of `K - λc I` lie in the program's intervals, `R(q̂)` lies within `errOpt` of `R(e)`, and for every nonzero `q` with `∠(R(q) b̄_i, r̄_i) ≤ ε_i` for every `i`, `R(q̂)` lies within `err` of `R(q)`. |
| Q5 | `compiled.qmethod.implements`, `compiled.qmethod.trapFree`, `qmethod_file` | The module's export returns the words of `qmethod`, without a trap from a store with room for a stated number of bytes, and the written file holds the module. |

## The slew planner's ε

`plan_premise` takes a flown map `F` within `ε` of the commanded attitude.  When an attitude estimator's estimate `M` is within `ε_k` of the true attitude and the controller keeps `M` within `ε_c` of the commanded attitude, the true attitude is within `ε_c + ε_k` of the commanded attitude, by the triangle inequality for angles.  The theorem `knowledge_share` states this for TRIAD's `err` with `M` any matrix in its intervals and gives `plan_premise`'s hypothesis with `ε = ε_c + err`.  The control error `ε_c` and the time between estimates remain the caller's.

## Tests

The oracle is an implementation in Python, run with `uv run`, that computes TRIAD and its bound with mpmath at 50 digits from the real values of the inputs, written apart from the program.  For each generated input, the containment test requires the oracle's matrix in the program's intervals, `err` at or above the oracle's `F + arcsin(η/(1 - η))` with `η` from the returned intervals, and `err` below that value plus `1e-12`.  It requires status 0 on the region of well-posed inputs, `θ` from 10° to 170°, vector lengths from `1e-3` to `1e3`, and `ε1 + ε2` at most 0.9 times `min(θ, π - θ)`, and it checks the stated status on parallel and nearly parallel vectors, zero vectors, non-finite values, negative error bounds, `ε1 + ε2` above 1.5, and `x` near 1.  The cases include `ε1 ≠ ε2`, `ε2 = 0` with `ε1 = 0.1`, `θ` of 30° and 150°, and random true attitudes.  A second test draws true attitudes and observations within their error bounds, at random and in the direction of the first-order worst case, and requires the angle between the image of the midpoint matrix and the true image of a unit vector below `err` for the vectors that maximize it.  The adversarial optimization of the errors' directions belongs to the derivation's numerical check and to the review's model, which run apart from the program.  The module test compares the module's `triad` export with native Lean bit for bit on the same inputs.

## What lies outside the theorems

The theorems concern the stated model: rigid rotations, directions without parallax or aberration, and error bounds that hold.  A sensor that violates its bound violates the premise, and nothing in the theorems detects it.  TRIAD's bound can exceed the largest error by the factor of the model section, and the theorems bound no interval's width.  The q-method's `errOpt` concerns the maximizer of the computed `K`, while `err` concerns the true attitude through the error bounds.  The solver determines `q̂`, `λc`, `errOpt`, `err`, and whether the certificate succeeds, and Q4 holds whatever it returns.  No theorem excludes a program that always rejects or returns a larger bound than its formula, so the tests require status 0 on a stated region of well-posed inputs and compare `err` with its formula.
