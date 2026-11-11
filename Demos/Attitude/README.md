# Attitude: TRIAD with a proved error bound

[The program](Program.lean) computes the attitude of a spacecraft from two directions measured in the body frame, such as those of the Sun and the magnetic field, and the same two directions in the inertial frame, with TRIAD.  It returns intervals that contain the nine entries of TRIAD's matrix and a bound `err` on the angle between the attitude of any matrix in those intervals and the true attitude, for bounds on the observations' angular errors.  [The theorems](#theorems) state that TRIAD maps the first measurement onto the first reference and the second into the plane of the references, that its matrix is a rotation, that the intervals contain its exact entries, and that `err` bounds the error.  The bound supplies the knowledge-error share of the input `ε` of [the slew planner's](../Slew/README.md) `plan_premise`, and `knowledge_share` states that link.

`verified_compile` compiles the program, with the library's `sin`, `cos`, and `asin`, into a module of 21,227 bytes.  In Wasmtime, the module's `triad` export agrees with native Lean, bit for bit, on 202 generated inputs, and [the reference test](#tests) finds, for every result of status 0 or 2, TRIAD's exact matrix inside the intervals, and for every result of status 0, `err` within `1e-12` above its formula, both computed in mpmath at 50 digits.  The q-method of [the requirements](requirements.md), with an inertia certificate and a Davis–Kahan bound, remains to be built.

## The model

An attitude maps body coordinates to inertial coordinates, as the slew planner's `R(q) v = q̄ v q̄*` does.  For vectors `a` and `b`, TRIAD's frame is `(ā, n, ā × n)` with `ā = a/|a|` and `n = (a × b)/|a × b|`.  With `(t1, t2, t3)` the frame of the measurements `b1`, `b2` and `(s1, s2, s3)` the frame of the references `r1`, `r2`, TRIAD's matrix is `T = s1 t1ᵀ + s2 t2ᵀ + s3 t3ᵀ`, which maps `t_i` to `s_i`.  [The model](Model.lean) states it as `triadMap`, and [the matrix file](Box.lean) as `triadMat`, whose entry `jk` is the inertial coordinate `j` of the image of body axis `k`.

An observation's error bound `ε_i` states that the true attitude `R(q)` carries `b̄_i` within angle `ε_i` of `r̄_i`.  A sensor error of at most `δ_i` and an error of the reference direction of at most `ρ_i` give `ε_i = δ_i + ρ_i`.  Angles are Mathlib's `InnerProductGeometry.angle`, as in `plan_premise`, and a map `M` lies within `ε` of `R(q)` when `∠(M v, R(q) v) ≤ ε` for every unit `v`.

## The error bound

With `sin θ = |r̄1 × r̄2|`, `d = ε1 + ε2`, and `x = sin d / sin θ`, let

`h = sin²(ε1/2) + cos²(ε1/2) · x²/(2 (1 + √(1 - x²)))`.

If `0 ≤ ε1`, `0 ≤ ε2`, `d < π/2`, and `sin d < sin θ`, then `T` lies within `F = 2 arcsin √h` of every true attitude that the error bounds admit.  The proof, in [the bound file](Bound.lean), moves the problem to the inertial frame, where TRIAD's error is the rotation `E` from the frame of `u_i = R(q) b̄_i` to the frame of the references.  It writes `E` as the action of the product of two quaternions: `(1 + u1 · r1, u1 × r1)`, which rotates `u1` onto `r1` by `α ≤ ε1`, and `(1 + a · s2, a × s2)`, which rotates about `r1` by an angle `ψ`.  The vector parts are perpendicular, so the scalar part of the product is the product of the scalar parts and `cos(φ/2) = cos(α/2) cos(ψ/2)` for the angle `φ` of `E`.  The rotation by `α` moves `u2` by at most `ε1`, so its image lies within `d` of `r2`, and the Cauchy–Schwarz inequality in the plane gives `cos ψ ≥ √(1 - x²)`: the largest angle about `r̄1` of a point within `d` of `r̄2` is `arcsin x`, at the tangents from `r̄1` to that cap.

The bound is deterministic, and the classical results of Shuster and Oh are statistical.  For small errors the largest error over the observations within their bounds is `√(ε1² + (ε2 + ε1 |cos θ|)²/sin²θ)`, and `F ≈ √(ε1² + d²/sin²θ)`, so to first order `F` exceeds the largest error by a factor of at most `(1 + √5)/2 ≈ 1.618`, at `θ = 90°` and `ε2 = 0.618 ε1`, and by at most 2 percent when `ε2 ≥ 50 ε1`.  TRIAD takes the more accurate observation first, so the second case is the usual one: a Sun sensor of 0.02° and a magnetometer of 1° give a bound within 2 percent of the largest error.

## Interface

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

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/attitude/Axioms.lean) and the file check confirm.  `vec3 x y z` is the real vector of three floats, and `b1`, `b2`, `r1`, and `r2` stand for the real vectors of the inputs.

| Theorem | File | Statement |
|---|---|---|
| `triad_first` | [Model](Model.lean) | For nonzero `b1` and `b1 × b2`, `T b̄1 = r̄1`. |
| `triad_second` | [Model](Model.lean) | For nonzero `b1`, `b2`, `r1`, `r2`, `b1 × b2`, and `r1 × r2`, `T b̄2 = α r̄1 + β r̄2` with `β = |b̄1 × b̄2|/|r̄1 × r̄2| > 0` and `α = b̄1 · b̄2 - β r̄1 · r̄2`. |
| `triad_dot`, `triad_cross` | [Model](Model.lean) | For nonzero `b1`, `r1`, `b1 × b2`, and `r1 × r2`, `T` preserves dot and cross products, so it is a rotation. |
| `triad_exact` | [Bound](Bound.lean) | For nonzero vectors and cross products, if `R(q) b̄1 = r̄1` and `R(q) b̄2 = r̄2`, then `T v = R(q) v` for every `v`. |
| `triad_error` | [Bound](Bound.lean) | For nonzero vectors, `0 ≤ ε1`, `0 ≤ ε2`, `ε1 + ε2 < π/2`, `sin(ε1 + ε2) < |r̄1 × r̄2|`, and a nonzero `q` with `∠(R(q) b̄i, r̄i) ≤ εi`, `∠(T v, R(q) v) ≤ 2 arcsin √h` for every unit `v`. |
| `triad_sound` | [Soundness](Soundness.lean) | If `triad` returns status 0 or 2, `b1`, `r1`, `b1 × b2`, and `r1 × r2` are not zero, and each interval contains its entry of `T`. |
| `triad_bound` | [Soundness](Soundness.lean) | If `triad` returns status 0, the conditions of `triad_error` hold for the real values of `e1` and `e2`, and for every nonzero `q` with the error bounds, every matrix `M` whose entries lie between the endpoints of the intervals, and every unit `v`, `∠(M v, R(q) v) ≤ err`. |
| `knowledge_share` | [Knowledge](Knowledge.lean) | If `triad` returns status 0, `M` lies in its intervals, a map `C` satisfies `∠(M v, C v) ≤ εc` for every unit `v`, and a nonzero `q` meets the error bounds, then `∠(R(q) v, C v) ≤ εc + err` for every unit `v`, which is the hypothesis of `plan_premise` on its flown map with `ε = εc + err`. |
| `compiled.triad.implements` | [Compilation](Verified.lean) | The module's `triad` export returns the words of `triad`, or traps at `unreachable`. |
| `compiled.bytes` | [Compilation](Verified.lean) | `encode compiled.module` succeeds with bytes that decode to `compiled.module`. |
| `attitude_file`, `attitude_file_decode` | [File theorems](File.lean) | `build/verified/attitude.wasm` holds `encode compiled.module` and decodes to it. |

## Limits of the theorems

The theorems concern rigid rotations and directions without parallax or aberration, and they take the error bounds as premises: a sensor that exceeds its bound violates the premise, and nothing in the program detects it.  They bound no interval's width, and no theorem excludes a program that always rejects or returns a bound larger than its formula, so the reference test requires status 0 on a region of well-posed inputs and compares `err` with its formula.  The bound can exceed the largest error by the factor of [the error bound](#the-error-bound), and `knowledge_share` leaves the control error `εc` and the time between estimates to the caller.  The theorems depend on the verified compiler's [trusted base](../../docs/verified-manual.md#trusted-base), and `triad_sound`, `triad_bound`, and `knowledge_share` concern `triad` in Lean, which `compiled.triad.implements` transfers to the module's export.

## Building and testing

The commands run from the repository root, with the tools of [the repository's commands](../../README.md#commands).

```sh
tools/leanrun --timeout 60m lake build Demos.Attitude.Knowledge Demos.Attitude.Verified
tests/verified/run.sh --cases attitude
tests/attitude/run.sh
```

`tests/verified/run.sh --cases attitude` writes and validates `build/verified/attitude.wasm`, compares the module with native Lean on the generated cases, runs [the axiom audit](../../tests/attitude/Axioms.lean), and checks [the file theorems](File.lean).  `tests/attitude/run.sh` prints the results of native Lean and checks them with [the reference](../../tests/attitude/reference.py).

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

## Files

| File | Contents |
|---|---|
| [Requirements](requirements.md) | Requirements of TRIAD and the q-method |
| [Review](review.md) | Decisions and the independent review |
| [Model](Model.lean) | Frames, TRIAD's map, and `triad_first`, `triad_second`, `triad_dot`, `triad_cross` |
| [Bound](Bound.lean) | Quaternion lemmas, the core inequality, `triad_error`, and `triad_exact` |
| [Matrices](Box.lean) | `Mat`, `triadMat`, and the angle of a matrix near a rotation |
| [Specification](Spec.lean) | `frameOf`, `matrixOf`, `boundOf`, and `triadOf` with their interval programs |
| [Program](Program.lean) | `triad` in the dialect |
| [Representations](Flat.lean) | `Flat` instance of `Estimate` |
| [Soundness](Soundness.lean) | `triad_sound` and `triad_bound` |
| [Knowledge](Knowledge.lean) | `knowledge_share` |
| [Compilation](Verified.lean) | `verified_compile compiled := [..., triad]` |
| [File theorems](File.lean) | `attitude_file` and `attitude_file_decode` |
