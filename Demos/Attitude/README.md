# Attitude: TRIAD and the q-method with proved error bounds

[TRIAD's program](Program.lean) computes the attitude of a spacecraft from two directions measured in the body frame, such as those of the Sun and the magnetic field, and the same two directions in the inertial frame.  It returns intervals that contain the nine entries of TRIAD's matrix and a bound `err` on the angle between the attitude of any matrix in those intervals and the true attitude, for bounds on the observations' angular errors.  [The theorems](#theorems) state that TRIAD maps the first measurement onto the first reference and the second into the plane of the references, that its matrix is a rotation, that the intervals contain its exact entries, and that `err` bounds the error.  The bound supplies the knowledge-error share of the input `ε` of [the slew planner's](../Slew/README.md) `plan_premise`, and `knowledge_share` states that link.

[The q-method's program](QProgram.lean) takes from 2 to 16 weighted observations, each a measurement, a reference, a weight, and an error bound.  An unproved solver, eight cyclic Jacobi sweeps, proposes an eigenvector `q̂` of Davenport's matrix `K`, and the program certifies it: an interval factorization of `K - c I` shows that its cut `c` separates the largest eigenvalue of `K` from the others, and a Davis–Kahan bound turns the residual of `q̂` into a bound `errOpt` on the angle between the attitude of `q̂` and the attitude that minimizes Wahba's loss.  The same cut turns the error bounds into a bound `err` on the angle between the attitude of `q̂` and every true attitude that they admit.  [The theorems](#theorems-of-the-q-method) state Davenport's reduction, the certificate, the Davis–Kahan bound, and both bounds for every result of status 0, and `qmethod_knowledge` gives `plan_premise`'s hypothesis from `err`.

`verified_compile` compiles TRIAD, with the library's `sin`, `cos`, and `asin`, into a module of 21,227 bytes, and the q-method into a module of 37,310 bytes.  In Wasmtime, the modules' exports agree with native Lean, bit for bit, on 202 and 253 generated inputs.  [The reference tests](#tests) compute the exact quantities in mpmath at 50 digits.  They find TRIAD's matrix inside its intervals and `err` within `1e-12` above its formula, and for the q-method the cut between the two largest eigenvalues of `K`, the attitude of `q̂` within `errOpt` of the optimum and within `err` of the true attitude, and both bounds within `1e-12` above their formulas, also for quaternions turned off the optimum by up to `1e-2`.

## TRIAD's model

An attitude maps body coordinates to inertial coordinates, as the slew planner's `R(q) v = q̄ v q̄*` does.  For vectors `a` and `b`, TRIAD's frame is `(ā, n, ā × n)` with `ā = a/|a|` and `n = (a × b)/|a × b|`.  With `(t1, t2, t3)` the frame of the measurements `b1`, `b2` and `(s1, s2, s3)` the frame of the references `r1`, `r2`, TRIAD's matrix is `T = s1 t1ᵀ + s2 t2ᵀ + s3 t3ᵀ`, which maps `t_i` to `s_i`.  [The model](Model.lean) states it as `triadMap`, and [the matrix file](Box.lean) as `triadMat`, whose entry `jk` is the inertial coordinate `j` of the image of body axis `k`.

An observation's error bound `ε_i` states that the true attitude `R(q)` carries `b̄_i` within angle `ε_i` of `r̄_i`.  A sensor error of at most `δ_i` and an error of the reference direction of at most `ρ_i` give `ε_i = δ_i + ρ_i`.  Angles are Mathlib's `InnerProductGeometry.angle`, as in `plan_premise`, and a map `M` lies within `ε` of `R(q)` when `∠(M v, R(q) v) ≤ ε` for every unit `v`.

## TRIAD's error bound

With `sin θ = |r̄1 × r̄2|`, `d = ε1 + ε2`, and `x = sin d / sin θ`, let

`h = sin²(ε1/2) + cos²(ε1/2) · x²/(2 (1 + √(1 - x²)))`.

If `0 ≤ ε1`, `0 ≤ ε2`, `d < π/2`, and `sin d < sin θ`, then `T` lies within `F = 2 arcsin √h` of every true attitude that the error bounds admit.  The proof, in [the bound file](Bound.lean), moves the problem to the inertial frame, where TRIAD's error is the rotation `E` from the frame of `u_i = R(q) b̄_i` to the frame of the references.  It writes `E` as the action of the product of two quaternions: `(1 + u1 · r1, u1 × r1)`, which rotates `u1` onto `r1` by `α ≤ ε1`, and `(1 + a · s2, a × s2)`, which rotates about `r1` by an angle `ψ`.  The vector parts are perpendicular, so the scalar part of the product is the product of the scalar parts and `cos(φ/2) = cos(α/2) cos(ψ/2)` for the angle `φ` of `E`.  The rotation by `α` moves `u2` by at most `ε1`, so its image lies within `d` of `r2`, and the Cauchy–Schwarz inequality in the plane gives `cos ψ ≥ √(1 - x²)`: the largest angle about `r̄1` of a point within `d` of `r̄2` is `arcsin x`, at the tangents from `r̄1` to that cap.

The bound is deterministic, and the classical results of Shuster and Oh are statistical.  For small errors the largest error over the observations within their bounds is `√(ε1² + (ε2 + ε1 |cos θ|)²/sin²θ)`, and `F ≈ √(ε1² + d²/sin²θ)`, so to first order `F` exceeds the largest error by a factor of at most `(1 + √5)/2 ≈ 1.618`, at `θ = 90°` and `ε2 = 0.618 ε1`, and by at most 2 percent when `ε2 ≥ 50 ε1`.  TRIAD takes the more accurate observation first, so the second case is the usual one: a Sun sensor of 0.02° and a magnetometer of 1° give a bound within 2 percent of the largest error.

## TRIAD's interface

```text
triad  b1x b1y b1z b2x b2y b2z r1x r1y r1z r2x r2y r2z e1 e2 : Float
         ->  status, m11 m12 m13 m21 m22 m23 m31 m32 m33 : Interval, err : Float

b1, b2      measurements in the body frame, of any positive length
r1, r2      references in the inertial frame, of any positive length
e1, e2      error bounds ε1 and ε2 in radians

status   0   the intervals contain T's entries, and err bounds the error of every matrix in them
         1   no result: an interval operation that computes the four lengths |b1|, |b1 × b2|,
             |r1|, |r1 × r2| or T's entries rejects, or a length's lower endpoint is not positive
         2   the intervals contain T's entries, and no bound: an error bound negative or not
             finite, the interval of ε1 + ε2 above 1.5, the interval of x not below 1, the
             interval of η above 1/4, or a rejection in the bound
```

The program evaluates the frames and `T` on the point intervals of the inputs with the operations of [the interval layer](../../Library/Numerics/Interval/README.md), through `enclosure_def` in [the specification](Spec.lean).  It tests the conditions of status 1 first and those of status 2 next.  `err` is the upper endpoint of the interval of `F + arcsin(η/(1 - η))`, where `η` is the root of the sum of the squared widths of the nine intervals: every matrix `M` in them satisfies `|M v - T v| ≤ η` for a unit `v`, so `∠(M v, T v) ≤ arcsin(η/(1 - η))`.  The program clamps the interval of `h` to `[0, 1]`, where the real `h` lies, before its square root, since outward rounding extends the interval of `h = 0` below zero, where `sqrt` rejects.  For status 1 the intervals are rejected and `err` is zero, and for status 2 `err` is zero.

## The q-method

[The model](Davenport.lean) states Davenport's matrix of one observation as `obsK b r`, whose quadratic form at `q` is `r · (q b q*)` (`form_obsK`), and `K` as the weighted sum `davK` of these matrices for the normalized vectors.  For a unit `q`, Wahba's loss `½ Σ a_i |r̄_i - R(q) b̄_i|²` equals `Σ a_i - qᵀ K q` (`wahba_eq`), so a unit quaternion `e` that maximizes `qᵀ K q` gives an attitude of least loss.  Such a maximizer exists by compactness (`exists_isMax`), and it is an eigenvector of `K` for the largest eigenvalue `λ1 = eᵀ K e` (`IsMax.apply_eq`).

[The certificate](Inertia.lean) is the symmetric factorization of `K - c I` that at each stage moves a chosen diagonal entry to the front and eliminates it.  For any choice of the entries, if the four pivots are one positive and three negative, the form of `K - c I` is positive at some vector and negative at every nonzero vector of some hyperplane (`onePos_of_pivots`).  [The bounds file](Eigen.lean) derives from this property that `c < λ1` and that every unit `q ⊥ e` has `qᵀ K q < c` (`inertia_cut`), since the plane of `e` and such a `q` would meet the hyperplane in a vector at which the form is not negative.  The maximizer is then unique up to sign (`isMax_unique`), and for a unit `v` and `μ > c` the Davis–Kahan bound `√(1 - (v · e)²) ≤ |K v - μ v|/(μ - c)` holds (`davis_kahan`).

Two unit quaternions whose lines lie within the angles `α` and `β` of the line of `e` have attitudes within `2 (α + β)` of each other (`rotation_near`).  The program's `q̂` lies within `arcsin (ρ̂/(μ̂ - c))` of that line, where `μ̂` is its Rayleigh quotient and `ρ̂` its relative residual.  The matrix of one observation satisfies `K_i² = |b|² |r|² I` (`apply_apply_obsK`), so a unit `q` has the residual `√(1 - c_i²)` for it, with `c_i` the cosine of `∠(R(q) b̄_i, r̄_i)` (`resid_obsK`).  A true attitude with error bounds `ε_i` in `[0, π/2]` therefore has a Rayleigh quotient of at least `μ_t = Σ a_i cos ε_i` and a residual of at most `ρ_t = Σ a_i sin ε_i` (`true_form`, `true_resid`), and it lies within `arcsin (ρ_t/(μ_t - c))` of the line when `c < μ_t` (`true_near`).  The two bounds are

`errOpt = 2 arcsin (ρ̂/(μ̂ - c))` and `err = 2 (arcsin (ρ̂/(μ̂ - c)) + arcsin (ρ_t/(μ_t - c)))`.

```text
qmethod  xs : Array Float  ->  status, w, x, y, z, errOpt, err, c : Array Float

xs[0]              n, a whole number from 2 to 16
xs[1+8i .. 8+8i]   observation i: bx by bz rx ry rz a ε, with a > 0 and ε in [0, 1.5]

status   0   the pivots certify c, R(q̂) lies within errOpt of R(e) for every maximizer e, and
             within err of every true attitude that the error bounds admit
         1   the input fails its conditions, an interval of K, of a length, or of a sum
             rejects, or the lower endpoint of a length is not positive
         2   the certificate failed: a pivot rejected, containing zero, or of the wrong sign,
             a lower endpoint of |q̂|², μ̂ - c, or μt - c not above zero, or an arcsine's
             argument outside [-1, 1]
```

The program encloses each observation's term as `k K(b, r)` with `k = a/(|b| |r|)`, which equals `a K(b̄, r̄)`, through `enclosure_def` in [the q-method's specification](QSpec.lean).  It runs eight cyclic Jacobi sweeps, which no theorem concerns, on the midpoints of the intervals of `K`, and takes `q̂` from the column of the largest estimate `λ̂1`, scaled to unit length with `w ≥ 0`, and `c = λ̂2 + (λ̂1 - λ̂2)/16` from the two largest estimates.  The program chooses each pivot as the remaining diagonal interval whose endpoints have the largest magnitude.  The tests check the unit length and the sign of `q̂`, which no theorem states, since `R(q̂)` normalizes `q̂` and does not depend on its sign.  The residual of a good eigenvector lies within the width of the interval of `K q̂`, where outward rounding extends the interval of `ρ̂²` below zero, so the program clamps that interval at zero before its square root.  For status 1 and 2 the other seven values are zero, and for status 0 the program returns `c` so that a caller can compare it with the spectrum.  For two observations of equal weight and equal bounds with exact data, `err` exceeds the largest error that the bounds admit by about `16/15 · 1/sin(m/2)` with `m = min(θ, π - θ)`, 1.51 at `θ = 90°` and 6.14 at 20° and 160°, and it exceeds TRIAD's `F` except within about 2° of `θ = 90°`, so the q-method serves more than two observations.

## Theorems

Every theorem in the two tables depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which the axiom audits of [TRIAD](../../tests/attitude/Axioms.lean) and of [the q-method](../../tests/attitude/QAxioms.lean) and the file checks confirm.  `vec3 x y z` is the real vector of three floats, and `b1`, `b2`, `r1`, and `r2` stand for the real vectors of TRIAD's inputs.

### Theorems of TRIAD

| Theorem | File | Statement |
|---|---|---|
| `triad_first` | [Model](Model.lean) | For nonzero `b1` and `b1 × b2`, `T b̄1 = r̄1`. |
| `triad_second` | [Model](Model.lean) | For nonzero `b1`, `b2`, `r1`, `r2`, `b1 × b2`, and `r1 × r2`, `T b̄2 = α r̄1 + β r̄2` with `β = \|b̄1 × b̄2\|/\|r̄1 × r̄2\| > 0` and `α = b̄1 · b̄2 - β r̄1 · r̄2`. |
| `triad_dot`, `triad_cross` | [Model](Model.lean) | For nonzero `b1`, `r1`, `b1 × b2`, and `r1 × r2`, `T` preserves dot and cross products, so it is a rotation. |
| `triad_exact` | [Bound](Bound.lean) | For nonzero vectors and cross products, if `R(q) b̄1 = r̄1` and `R(q) b̄2 = r̄2`, then `T v = R(q) v` for every `v`. |
| `triad_error` | [Bound](Bound.lean) | For nonzero vectors, `0 ≤ ε1`, `0 ≤ ε2`, `ε1 + ε2 < π/2`, `sin(ε1 + ε2) < \|r̄1 × r̄2\|`, and a nonzero `q` with `∠(R(q) b̄i, r̄i) ≤ εi`, `∠(T v, R(q) v) ≤ 2 arcsin √h` for every unit `v`. |
| `triad_sound` | [Soundness](Soundness.lean) | If `triad` returns status 0 or 2, `b1`, `r1`, `b1 × b2`, and `r1 × r2` are not zero, and each interval contains its entry of `T`. |
| `triad_bound` | [Soundness](Soundness.lean) | If `triad` returns status 0, the conditions of `triad_error` hold for the real values of `e1` and `e2`, and for every nonzero `q` with the error bounds, every matrix `M` whose entries lie between the endpoints of the intervals, and every unit `v`, `∠(M v, R(q) v) ≤ err`. |
| `knowledge_share` | [Knowledge](Knowledge.lean) | If `triad` returns status 0, `M` lies in its intervals, a map `C` satisfies `∠(M v, C v) ≤ εc` for every unit `v`, and a nonzero `q` meets the error bounds, then `∠(R(q) v, C v) ≤ εc + err` for every unit `v`, which is the hypothesis of `plan_premise` on its flown map with `ε = εc + err`. |
| `compiled.triad.implements` | [Compilation](Verified.lean) | The module's `triad` export returns the words of `triad`, or traps at `unreachable`. |
| `compiled.bytes` | [Compilation](Verified.lean) | `encode compiled.module` succeeds with bytes that decode to `compiled.module`. |
| `attitude_file`, `attitude_file_decode` | [File theorems](File.lean) | `build/verified/attitude.wasm` holds `encode compiled.module` and decodes to it. |

### Theorems of the q-method

`K` is Davenport's matrix of the real values of the input (`kOf xs`), `c` the real value of the output cut, `q̂` the real quaternion of outputs 1 to 4, and `e` a maximizer of `qᵀ K q` on the unit sphere.

| Theorem | File | Statement |
|---|---|---|
| `wahba_eq` | [Davenport](Davenport.lean) | For observations with nonzero vectors and a unit `q`, Wahba's loss equals `Σ a_i - qᵀ K q`. |
| `apply_apply_obsK`, `resid_obsK` | [Davenport](Davenport.lean) | One observation's matrix satisfies `K_i² = \|b\|² \|r\|² I`, and for unit `b`, `r`, and `q` the residual of `q` has squared length `1 - c_i²` with `c_i = qᵀ K_i q = r · R(q) b`. |
| `onePos_of_pivots` | [Inertia](Inertia.lean) | For any choice of exchanges, pivots of one positive and three negative signs with those exchanges give a vector at which the form is positive and a hyperplane on which it is negative at every nonzero vector. |
| `exists_isMax`, `IsMax.apply_eq`, `isMax_unique` | [Eigen](Eigen.lean) | A maximizer exists and is an eigenvector of `K` for `λ1 = eᵀ K e`, and under the certificate it is unique up to sign. |
| `inertia_cut` | [Eigen](Eigen.lean) | Under the certificate of `K - c I`, `c < λ1`, and every unit `q ⊥ e` has `qᵀ K q < c`. |
| `davis_kahan` | [Eigen](Eigen.lean) | Under the cut, `√(1 - (v · e)²) ≤ \|K v - μ v\|/(μ - c)` for a unit `v` and `μ > c`. |
| `true_near` | [Eigen](Eigen.lean) | Under the cut, for observations with nonzero vectors, weights at least zero, error bounds in `[0, π/2]`, and `c < μ_t`, every nonzero `q` that meets the error bounds has `1 - (q̄ · e)² ≤ (ρ_t/(μ_t - c))²`. |
| `rotation_near` | [Eigen](Eigen.lean) | Unit `p` and `q` with `\|p · e\| ≥ cos α` and `\|q · e\| ≥ cos β`, for `α` and `β` in `[0, π/2]`, have attitudes within `2 (α + β)` of each other. |
| `valid_cases` | [Soundness](QSoundness.lean) | A valid input meets `InputOk`: its first value is the whole number `n` of observations from 2 to 16, it has `1 + 8n` values, read as a word count, those values are finite, and its weights are positive and its error bounds in `[0, 1.5]`. |
| `qmethod_sound` | [Soundness](QSoundness.lean) | If `qmethod` returns status 0, the input meets `InputOk` and its vectors are not zero, `q̂`, `errOpt`, `err`, and `c` are finite, `K - c I` has the certificate's property, a maximizer exists and is unique up to sign, every maximizer has the cut, `q̂` is not zero, `R(q̂)` lies within `errOpt` of `R(e)` for every maximizer `e`, and `R(q̂)` lies within `err` of `R(q)` for every nonzero `q` with `∠(R(q) b̄_i, r̄_i) ≤ ε_i` for every `i`. |
| `qmethod_status_two` | [Soundness](QSoundness.lean) | If `qmethod` returns status 2, the input meets `InputOk`. |
| `qmethod_knowledge` | [Knowledge](Knowledge.lean) | If `qmethod` returns status 0, a map `C` lies within `εc` of `R(q̂)`, and a nonzero `q` meets the error bounds, then `∠(R(q) v, C v) ≤ εc + err` for every unit `v`, the hypothesis of `plan_premise` on its flown map with `ε = εc + err`. |
| `compiled.qmethod.implements` | [Compilation](QVerified.lean) | The module's `qmethod` export returns the words of `qmethod`, or traps at `unreachable`. |
| `qmethod_bound`, `qmethod_call` | [Call](QCall.lean) | A call raises the allocator's `top` by at most 712 bytes, the charge of the array literal of its result, and from a ready store with room for them the export `qmethod` returns a new array that holds the bit patterns of `qmethod xs`, without a trap. |
| `qmethod_file`, `qmethod_file_decode` | [File theorems](QFile.lean) | `build/verified/qmethod.wasm` holds `encode compiled.module` and decodes to it. |

## Limits of the theorems

The theorems concern rigid rotations and directions without parallax or aberration, and they take the error bounds as premises: a sensor that exceeds its bound violates the premise, and nothing in the programs detects it.  They bound no interval's width, and no theorem excludes a program that always rejects or returns a bound larger than its formula, so the reference tests require status 0 on stated inputs and compare the bounds with their formulas.  TRIAD's bound can exceed the largest error by the factor of [TRIAD's error bound](#triads-error-bound), and the q-method's `err` by the factors of [its section](#the-q-method) for two observations.  The q-method's `errOpt` concerns the maximizer of Davenport's matrix of the real values of the input, and `err` concerns the true attitude through the error bounds.  The Jacobi solver determines `q̂`, `c`, both bounds, and whether the certificate succeeds, and `qmethod_sound` holds whatever it returns.  `knowledge_share` and `qmethod_knowledge` leave the control error `εc` and the time between estimates to the caller.  The theorems depend on the verified compiler's [trusted base](../../docs/verified-manual.md#trusted-base), and the soundness theorems concern `triad` and `qmethod` in Lean, which `compiled.triad.implements` and `qmethod_call` transfer to the modules' exports.

## Building and testing

The commands run from the repository root, with the tools of [the repository's commands](../../README.md#commands).

```sh
tools/leanrun --timeout 60m lake build Demos.Attitude.Knowledge Demos.Attitude.Verified
tools/leanrun --timeout 90m lake build Demos.Attitude.QCall
tests/verified/run.sh --cases attitude
tests/verified/run.sh --cases qmethod
tests/attitude/run.sh
tests/attitude/qrun.sh
```

`tests/verified/run.sh --cases attitude` writes and validates `build/verified/attitude.wasm`, compares the module with native Lean on the generated cases, runs [the axiom audit](../../tests/attitude/Axioms.lean), and checks [the file theorems](File.lean), and `--cases qmethod` does the same for `build/verified/qmethod.wasm` with [the q-method's audit](../../tests/attitude/QAxioms.lean) and [file theorems](QFile.lean).  `tests/attitude/run.sh` and `tests/attitude/qrun.sh` print the results of native Lean and check them with [TRIAD's reference](../../tests/attitude/reference.py) and [the q-method's reference](../../tests/attitude/qreference.py).

## Tests

[The generator](../../tests/TestSupport/Attitude/Cases.lean) draws 180 inputs from SplitMix64 with fixed seeds and adds 22 inputs at the edges, 202 in all.  An input of class `good` has references at an angle from 10° to 170°, vector lengths from `1e-3` to `1e3`, error bounds whose sum is at most 0.9 times the smaller of `θ` and `π - θ`, and measurements that a random true attitude gives from the references moved by up to 0.99 of their bounds in random directions.  An input of class `worst` moves the two observations by 0.999 of their bounds toward opposite sides of the plane of the references, the direction of the first-order worst case.  The edges include a zero vector, parallel and nearly parallel vectors, non-finite components and error bounds, negative error bounds, `ε1 + ε2` above 1.5, `x` above 1, and error bounds of zero.

[The reference](../../tests/attitude/reference.py) reads the bits of each input and result and computes TRIAD and its bound in mpmath at 50 digits from the real values of the inputs.  It requires status 0 for every `good` and `worst` input, status 1 or 2 for each edge that the requirements assign to it, TRIAD's exact entries inside the intervals of every result of status 0 or 2, and `err` at or above `F + arcsin(η/(1 - η))` and less than `1e-12` above it.  For the `good` and `worst` inputs it checks that the true attitude meets the error bounds and that the midpoint matrix of the intervals moves no tested unit vector farther than `err` from its true image, testing the vectors perpendicular to the axis of the error rotation and 64 random vectors.

| Class | Inputs | Status 0 | Status 1 | Status 2 |
|---|---:|---:|---:|---:|
| `good` | 124 | 124 | 0 | 0 |
| `worst` | 60 | 60 | 0 | 0 |
| `bad1` | 9 | 0 | 9 | 0 |
| `bad2` | 7 | 0 | 0 | 7 |
| `any` | 2 | 2 | 0 | 0 |

Every check passed.  `err` exceeded its formula by at most `1.5e-14`.  The largest error found was 0.795 of `err` among the `good` inputs and 0.984 of `err` among the `worst` inputs, whose second observation usually carries the larger bound, the case in which `F` lies within a few percent of the largest error.  The module test compares the module's `triad` export with native Lean, bit for bit, on the same 202 inputs.

[The q-method's generator](../../tests/TestSupport/Attitude/QCases.lean) draws 225 inputs and adds 28 at the edges, 253 in all, and applies the certificate to 30 more.  An input of class `good` has from 2 to 16 observations with references in random directions, two references at an angle from 20° to 160° when there are two, weights from 0.5 to 2, error bounds from 0.1 to 1 times a largest bound of `1e-4`, `1e-3`, `1e-2`, or `3e-2`, and vector lengths from `1e-3` to `1e3`, with measurements that a random true attitude gives from the references moved by up to 0.99 of their bounds in random directions.  An input of class `bias` moves every reference by 0.999 of its bound perpendicular to the plane of the reference and one common axis.  The edges include a count that is not whole or lies outside `[2, 16]`, each also with an input whose length fits the count or its whole part, an input of the wrong length, non-finite values, zero and negative weights, error bounds outside `[0, 1.5]`, zero vectors, overflow, observations that leave the largest eigenvalue double, error bounds of 1.2 and 1.4, exact observations, and three exact observations rotated so that the first diagonal entry of `K - c I` is zero, which only the pivoting factorization certifies.  An input of class `turned` is an input of class `good` for which the test applies `certify` to the program's quaternion turned by `1e-6`, `1e-4`, or `1e-2` toward the second eigenvector estimate, so that `errOpt` is large enough to compare with its formula.  The requirement of status 0 applies to the `good` and `bias` inputs of this sample.  The region they are drawn from also holds inputs for which no cut gives a bound, such as three references within 10° of each other with bounds `3e-2`.

[The q-method's reference](../../tests/attitude/qreference.py) computes `K` in the form of [the requirements](requirements.md#model-1) and its eigendecomposition in mpmath at 50 digits.  For every result of status 0 it requires `q̂` of unit length within `1e-15` with `w ≥ 0`, `λ2 < c < λ1`, the angle `2 arccos |q̄ · e|` between the attitudes of `q̂` and of the eigenvector `e` of `λ1` at most `errOpt`, positive gaps `μ̂ - c` and `μ_t - c`, sines at most 1, and `errOpt` and `err` at or above their formulas and less than `1e-12` above them, with `μ̂` and `ρ̂` computed from the exact `K` and the returned `q̂`, with the returned `c`.  For every input with a recorded true attitude it checks that the true attitude meets the error bounds and that the angle between its attitude and that of `q̂` is at most `err`.

| Class | Inputs | Status 0 | Status 1 | Status 2 |
|---|---:|---:|---:|---:|
| `good` | 180 | 180 | 0 | 0 |
| `bias` | 45 | 45 | 0 | 0 |
| `edge` | 6 | 6 | 0 | 0 |
| `turned` | 30 | 30 | 0 | 0 |
| `bad1` | 18 | 0 | 18 | 0 |
| `bad2` | 4 | 0 | 0 | 4 |

Every check passed.  `errOpt` and `err` exceeded their formulas by at most `3.7e-13`, and for the `turned` inputs `errOpt` was 1.067 times the angle to the optimum.  The largest true error was 0.366 of `err` among the `good` inputs, 0.655 among the `bias` inputs, and 0.933 among the `turned` inputs.  The module test compares the module's `qmethod` export with native Lean, bit for bit, on the 253 inputs of `qmethod`.

## Files

| File | Contents |
|---|---|
| [Requirements](requirements.md) | Requirements of TRIAD and the q-method |
| [Review](review.md) | Decisions and the independent reviews |
| [Model](Model.lean) | Frames, TRIAD's map, and `triad_first`, `triad_second`, `triad_dot`, `triad_cross` |
| [Bound](Bound.lean) | Quaternion lemmas, the core inequality, `triad_error`, and `triad_exact` |
| [Matrices](Box.lean) | `Mat`, `triadMat`, and the angle of a matrix near a rotation |
| [Specification](Spec.lean) | `frameOf`, `matrixOf`, `boundOf`, and `triadOf` with their interval programs |
| [Program](Program.lean) | `triad` in the dialect |
| [Representations](Flat.lean) | `Flat` instance of `Estimate` |
| [Soundness](Soundness.lean) | `triad_sound` and `triad_bound` |
| [Knowledge](Knowledge.lean) | `knowledge_share` and `qmethod_knowledge` |
| [Compilation](Verified.lean) | `verified_compile compiled := [..., triad]` |
| [File theorems](File.lean) | `attitude_file` and `attitude_file_decode` |
| [Davenport](Davenport.lean) | `Sym4`, `obsK`, `davK`, Wahba's loss, `wahba_eq`, `resid_obsK`, `true_form`, `true_resid` |
| [Inertia](Inertia.lean) | `Sym3`, `Sym2`, Schur complements, exchanges, `OnePos`, `pivots`, `onePos_of_pivots` |
| [Eigen](Eigen.lean) | `IsMax`, `Within`, `exists_isMax`, `inertia_cut`, `isMax_unique`, `davis_kahan`, `true_near`, `rotation_near` |
| [q-method specification](QSpec.lean) | The observation terms, Schur complements, `K p`, the residual, and the bounds with their interval programs |
| [q-method program](QProgram.lean) | `qmethod` in the dialect |
| [q-method representations](QFlat.lean) | `Flat` instances of `M4`, `M3`, `M2`, `Acc`, `Q4`, and `Jac` |
| [q-method soundness](QSoundness.lean) | `InputOk`, `valid_cases`, `accumulate_enc`, `pivots_enc`, `certify_sound`, `qmethod_sound`, and `qmethod_status_two` |
| [q-method compilation](QVerified.lean) | `verified_compile compiled := [..., qmethod]` in `Demos.Attitude.QMethod` |
| [q-method call](QCall.lean) | `qmethod_bound`, `qmethod_callSpec`, and `qmethod_call` |
| [q-method file theorems](QFile.lean) | `qmethod_file` and `qmethod_file_decode` |
