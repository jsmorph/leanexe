# Initial orbit determination: requirements

## Purpose and scope

The demo computes the velocity of a two-body orbit from position data by two classical methods and returns boxes that contain the model's result for every input in the measurement boxes.  Gibbs' method takes three position vectors and returns the velocity at the second.  Lambert's problem takes two position vectors, a time of flight, and a direction of motion, and the demo solves it for less than one revolution in the formulation of Izzo (2015), returning the velocities at both positions.  Angles-only methods such as those of Gauss and Laplace, Lambert solutions with one or more full revolutions, the Herrick–Gibbs method for closely spaced positions, and the conversion of measurements such as range and angles into position boxes lie outside the demo.

Both programs are ground programs, compiled by `verified_compile` to WebAssembly modules with call theorems, in the forms WASM, SPEC, and WASMF of [the algorithm index](../../index.md).  Program values are `UInt64` words and binary64 numbers, and the computation of each export is a fixed sequence of interval operations, except the two bisections of Lambert's program, each bounded by 256 steps.  Neither program allocates an array, and the only tables are the two tables of the library's logarithm, which Lambert's program reads.  The demo defines its own two-body model, described below, and takes no orbital elements.

## Units, inputs, and measurement boxes

Every length uses one unit and every time another, such as km and s, with the gravitational parameter `μ` in the cube of the length unit per square of the time unit.  The positions are in an inertial frame with its origin at the attracting center.  The programs take each input quantity as an interval of binary64 endpoints, and the theorems concern every real number between the endpoints' values.

Measurement error enters as boxes.  A position is given as three intervals, one for each axis, chosen by the caller to contain the true position: for example, a measured position with a bound on the error of each coordinate.  The gravitational parameter is an interval, so that its uncertainty is bounded too, and the time of flight of Lambert's problem is an interval that covers the error of the two epochs.  A result is a box: an interval for each component of each velocity, and for Lambert's problem also an interval of the free parameter `x`.  The conversion of other measurements into boxes, the frame of the positions, and the choice of the bounds are the caller's.

## The two-body model

For a gravitational parameter `μ > 0`, an orbit is a pair of vectors `(h, e)` with `h ≠ 0`: the angular momentum per unit mass and the eccentricity vector.  Its path is the set of positions `r ≠ 0` with `r · h = 0` and `|r| + e · r = |h|²/μ`, the polar equation of a conic with a focus at the origin, and its velocity at a position `r` of the path is `v(r) = (μ/|h|²) h × (e + r/|r|)`.  A component of `e` along `h` changes neither the path nor `v`, so the shape of the path depends on the component `e⊥` normal to `h`: the path is the whole ellipse for `|e⊥| < 1` and the branch of the parabola or hyperbola around the focus otherwise.  Rectilinear motion, `h = 0`, lies outside the model.

A state `(r, v)` with `r ≠ 0` and `r × v ≠ 0` has the orbit `h = r × v`, `e = v × h/μ - r/|r|`, and the lemma `orbitOf_spec` states that its position lies on that orbit's path with velocity `v`.  Newton's equation `r'' = -μ r/|r|³` is the two-body problem, and `newton_conserves` states that `h` and `e` are constant along a solution that stays away from the origin.  The positions of such a solution therefore lie on the path of one orbit, and its velocity at each of them is `v(r)`.  This model covers ellipses, parabolas, and hyperbolas alike.

Along every conic, the motion from a state `(r, v)` with `r × v ≠ 0` follows the universal form of Kepler's equation.  Let `β = 2μ/|r| - |v|²` (`conicBeta`), which is `μ/a` for the semimajor axis `a` of an ellipse.  The eccentricity vector of the state's orbit satisfies `e · h = 0` and `|e|² = 1 - β |h|²/μ²` (`orbitOf_ecc`), so `β` is positive, zero, or negative as the orbit is an ellipse, a parabola, or a hyperbola.  The universal variable `χ` advances at the rate `dχ/dt = 1/|r|`, and the universal functions `U0`, `U1`, `U2`, and `U3` of `β` and `χ` are `cos(√β χ)`, `sin(√β χ)/√β`, `(1 - cos(√β χ))/β`, and `(χ - sin(√β χ)/√β)/β` for an ellipse, the same with `cosh` and `sinh` of `√(-β) χ` for a hyperbola, and `1`, `χ`, `χ²/2`, and `χ³/6` for a parabola.  When the universal variable has advanced by `χ`, the position `conicPos` is `f r + g v` with Lagrange's coefficients `f = 1 - μ U2/|r|` and `g = |r| U1 + (r · v) U2`, its distance from the origin is `R = |r| U0 + (r · v) U1 + μ U2`, and the time `conicTime` is `|r| U1 + (r · v) U2 + μ U3`.  The time equation is Kepler's equation for an ellipse, where `√β χ` is the advance of the eccentric anomaly, its hyperbolic form for a hyperbola, and Barker's equation for a parabola.  These quantities need no perifocal axes, so a circular orbit is no special case.  The motion first reaches a position `r'` after the time `t`, `ConicTransfer μ r v r' t`, when `r × v ≠ 0` and some advance `χ > 0` reaches `r'` in the time `t` while no smaller positive advance reaches `r'`.

**C1** (`orbitOf_ecc`, `conicPos_onPath`, `conicPos_norm`, `conicPos_inj`, `conicTime_strictMono`, `conicTime_surjective`, `conic_newton`).  For `μ > 0` and a state with `r × v ≠ 0`, `e · h = 0` and `|e|² = 1 - β |h|²/μ²`, every position `conicPos χ` lies on the path of the state's orbit at the distance `R > 0`, the positions at two advances `χ1 ≠ χ2` are distinct when `β ≤ 0` or when `√β |χ1 - χ2| < 2π`, and the time increases strictly with `χ` and takes every real value.  With `conicAdvance` the inverse of `conicTime` and the velocity `conicVel`, the rate of `conicPos` over the rate `R` of `conicTime`, the position and the velocity at `conicAdvance τ` solve Newton's equation and are `(r, v)` at the time 0.

**N1** (`newton_unique`).  Two solutions of Newton's equation on an open interval of times, or on any open preconnected set of times (`NewtonOn`), with the same position and velocity at one of its times, are equal at every time of it.  The proof writes a solution as a curve in the product of two Euclidean spaces of three coordinates, where Newton's field `(r, v) ↦ (v, -μ r/|r|³)` is continuously differentiable for `r ≠ 0` and so Lipschitz near each state, and applies Mathlib's local uniqueness theorem `ODE_solution_unique_of_eventually`.  The set of times at which two solutions agree is then open in the interval, it is closed in the interval by continuity, and the interval is connected.  A two-body transfer from `(r1, v1)` to `(r2, v2)` in the time `t`, `NewtonTransfer`, is a solution of Newton's equation on an open interval of times that contains `[0, t]`, which starts at `(r1, v1)`, is at `(r2, v2)` at `t`, and is not at `r2` at any earlier positive time.  The interval admits a transfer that begins with a manoeuvre at `r1`, before which the motion follows another orbit.

Three positions `r1`, `r2`, `r3` of a path lie in the order of motion, within less than one revolution, when `D · h > 0` for `D = r1 × r2 + r2 × r3 + r3 × r1`, the normal `(r2 - r1) × (r3 - r1)` of their triangle.  For an ellipse with semimajor axis `a`, semiminor axis `b`, and eccentric anomalies `E1`, `E2`, `E3`, this product is `4ab |h| sin((E2 - E1)/2) sin((E3 - E2)/2) sin((E3 - E1)/2)`, positive exactly when the three points are distinct and in the cyclic order of motion, that is, when `E1 < E2 < E3 < E1 + 2π` after adding multiples of `2π` to `E2` and `E3`.  Observations at increasing times satisfy the condition, within one period for an ellipse, and positions in the reverse cyclic order give `D · h < 0`.  `D` is unchanged by a cyclic permutation of the three positions, so the condition fixes their cyclic order only, and the velocity that Gibbs' method returns is the one at its second argument.

## Gibbs' method

### The formula

For positions `r1`, `r2`, `r3` with lengths `n1`, `n2`, `n3`, Gibbs' method forms

| Vector | Definition |
|---|---|
| `D` | `r1 × r2 + r2 × r3 + r3 × r1` |
| `N` | `n1 (r2 × r3) + n2 (r3 × r1) + n3 (r1 × r2)` |
| `S` | `(n2 - n3) r1 + (n3 - n1) r2 + (n1 - n2) r3` |

and returns `gibbs(r1, r2, r3, μ) = √(μ/(N · D)) (D × r2/n2 + S)`, the formula of Curtis (Algorithm 5.1) and of Vallado (Algorithm 54) with the product of the lengths `|N| |D|` written as the dot product `N · D`.  On a path the two products agree, because `N = p D` with `p = |h|²/μ`, and the dot product needs no square root.

### Real-number theorem

**G1** (`gibbs_velocity`).  For `μ > 0`, an orbit `(h, e)`, and positions `r1`, `r2`, `r3` on its path with `D · h > 0`, the product `N · D` is positive and `gibbs(r1, r2, r3, μ) = v(r2)`.

The proof uses `N = p D`, `S = D × e`, and `D = (D · h/|h|²) h`, which hold because the positions lie in the plane normal to `h` and satisfy the polar equation.  The corollary `gibbs_newton` states G1 for a solution of Newton's equation: for three times whose positions satisfy `D · h > 0`, Gibbs' formula at the three positions is the solution's velocity at the second time.  If the positions satisfy `D · h < 0`, the formula returns `-v(r2)`, the velocity of the reversed motion, and G1 makes no claim.

### Program

| Entry | Arguments | Result |
|---|---|---|
| `gibbsBox` | nine intervals of the coordinates of `r1`, `r2`, `r3`, and an interval of `μ` | status and three intervals of the velocity at `r2` |
| `gibbsBounds` | the eighteen endpoints of the coordinates and the two endpoints of `μ`, all binary64 | the same, with each interval built from its endpoints |

The program first checks the inputs.  It then evaluates, with the outward-rounded operations of [the interval layer](../../Library/Numerics/Interval/README.md), the triple product `r1 · (r2 × r3)`, which is zero for any three positions of a path.  If the triple product's interval lies above or below zero, no orbit passes through the boxes.  Otherwise the program evaluates the formula in interval arithmetic and returns its three intervals.  A division rejects a divisor whose interval holds zero, and the square root of `μ/(N · D)` rejects an interval that reaches below zero, so an accepted result shows `n2 > 0` and `N · D > 0` for every point of the boxes.

| Status | Meaning |
|---|---|
| 0 | The three intervals contain `v(r2)` of every orbit through the boxes in the order of the positions. |
| 1 | The interval of the triple product lies above or below zero, so no orbit has positions in all three boxes. |
| 2 | An interval operation rejected: the box of `r2` reaches the origin, the interval of `N · D` holds zero or lies below it because the boxes are too wide, too close to collinear, or out of order, or an endpoint overflowed. |
| 3 | Invalid input: an endpoint that is not finite, a lower endpoint above its upper endpoint, or an interval of `μ` that does not lie above zero. |

### Program theorems

**G2** (`gibbsBox_sound`, `gibbsBounds_sound`).  If the program returns status 0, then for every `μ` in its interval, every orbit `(h, e)`, and every three positions `r1`, `r2`, `r3` on its path, each in its box, with `D · h > 0`, the three intervals contain the components of `v(r2)`.

**G3** (`gibbsBox_no_orbit`).  If the program returns status 1, then no orbit has a position in each of the three boxes.

**G4** (`gibbsCompiled.gibbsBox.implements`, `gibbsCompiled.gibbsBounds.implements`).  The module's exports return the words of `gibbsBox` and `gibbsBounds` for argument words that represent their arguments.

### Excluded geometries and widths

| Geometry | Effect |
|---|---|
| Collinear positions, including two equal positions | `D = 0`, outside G1 and G2.  The arithmetic gives status 2 near this geometry. |
| Positions out of the cyclic order of motion, or an ellipse's positions spanning a revolution or more | `D · h < 0`, outside G1 and G2.  The formula returns the velocity of the reversed motion. |
| A box of `r2` that reaches the origin | Status 2. |
| Closely spaced positions | The result widens in proportion to the box width over the cube of the angular separation, up to status 2. |
| Boxes that admit no three positions in one plane through the origin | Status 1 when the triple product's interval shows it. |

Interval evaluation of the formula overestimates the spread of `v(r2)` over the orbits through the boxes, because each coordinate occurs many times.  The review measured factors from 8 at separations of 60° to about 500 at 1°.  The tests bound the width of the result by a constant times the relative box width over the cube of the separation in radians.

## Lambert's problem

### Izzo's formulation

For positions `r1` and `r2` with lengths `n1` and `n2`, the chord is `c = |r2 - r1|` and the semiperimeter is `s = (n1 + n2 + c)/2`.  The direction of motion is given by an axis `k`: the motion has an angular momentum `h` with `h · k > 0`.  The transfer angle `θ` from `r1` to `r2`, measured in the direction of motion, lies in `(0, 2π)`, and `θ < π` exactly when `(r1 × r2) · k > 0`.  Izzo's parameter is `λ = √(n1 n2) cos(θ/2)/s`, equal to `√(1 - c/s)` for `θ < π` and to `-√(1 - c/s)` for `θ > π`, and the nondimensional time is `T = √(2μ/s³) t` for the time of flight `t`.

The free parameter is `x > -1`, with `y = √(1 - λ²(1 - x²))`.  Izzo's equation (18), the form of Lambert's time of flight that Lancaster and Blanchard derived, defines the time of flight for zero revolutions:

| Range | `ψ` | `T(x)` |
|---|---|---|
| `-1 < x < 1` | `arccos(x y + λ(1 - x²))` | `(ψ/√(1 - x²) - x + λ y)/(1 - x²)` |
| `x = 1` |  | `(2/3)(1 - λ³)` |
| `x > 1` | `arcosh(x y - λ(x² - 1))` | `(ψ/√(x² - 1) - x + λ y)/(1 - x²)` |

From a solution `x`, Izzo's algorithm forms `γ = √(μ s/2)`, `ρ = (n1 - n2)/c`, and `σ = √(1 - ρ²)`, the radial components

`vr1 = γ ((λ y - x) - ρ (λ y + x))/n1`,  `vr2 = -γ ((λ y - x) + ρ (λ y + x))/n2`,

and the transverse components `vt1 = γ σ (y + λ x)/n1` and `vt2 = γ σ (y + λ x)/n2`.  With `ĥ = ±(r1 × r2)/|r1 × r2|`, the sign chosen so that `ĥ · k > 0`, the velocities are `v1 = vr1 r1/n1 + vt1 ĥ × r1/n1` and `v2 = vr2 r2/n2 + vt2 ĥ × r2/n2`.

### Real-number theorems

**L1** (`tof_pos_eq`, `tof_neg_eq`).  For `-1 < λ < 1` and `x > 0`, `T(x) = 2 ∫ from λ to 1 of σ²/√(1 - (1 - x²) σ²) dσ`, and for `-1 < x < 0`, `T(x) = π/(1 - x²)^(3/2) - 2 ∫ from -λ to 1 of σ²/√(1 - (1 - x²) σ²) dσ`.  The integrand increases with `1 - x²` at every `σ ≠ 0`, which gives the monotonicity of L2 without derivatives.

**L2** (`tof_strictAntiOn`, `tof_continuousOn`).  For `-1 < λ < 1`, `T` is continuous and strictly decreasing on `(-1, ∞)`.  Lancaster and Blanchard state this monotonicity for less than one revolution without a proof, and L1 gives one.  The limits `+∞` at `-1` and `0` at `+∞` enter as the bounds `exists_lt_tof` and `tof_le_of_gt`.

**L3** (`exists_unique_root`).  For `-1 < λ < 1` and every `T* > 0`, exactly one `x > -1` satisfies `T(x) = T*`.  The sign of `λ` is the sign of `cos(θ/2)`, which the direction of motion fixes, so L3 is the existence and uniqueness of the solution of Izzo's equation for a given direction of motion.  The real-number layer defines that solution, `Lambert.root`, and the velocities `v1` and `v2` of the formulas above as functions of the real inputs.

### Lambert's theorem

Lambert's theorem, in Lancaster and Blanchard's form that Izzo writes in the variables `x` and `λ`, relates Izzo's equation to the two-body problem in two directions, for `μ > 0`, `t > 0`, and `(r1 × r2) · k ≠ 0`.  In one direction, for every `x > -1` the states `(r1, v1(x))` and `(r2, v2(x))` lie on one orbit whose angular momentum `h` has `h · k > 0`, and the motion along it from `r1` first reaches `r2` in the time `√(s³/(2μ)) T(x)`.  In the other, every two-body motion from `r1` in the direction of `k` that first reaches `r2` in the time `t` starts with the velocity `v1(x)` for some `x` with `T(x) = T*`.  Together with L3 the two directions give exactly one such motion, and its initial velocity is `v1(x*)`.  The real-number layer defines `v1(x)` and `v2(x)` as `izzoV1` and `izzoV2`, from the formulas above with the sign of `λ` given by `k`, and `x*` as `izzoRoot`.

**L6** (`izzo_orbit`, `izzo_energy`, `orbit_izzo`).  For `μ > 0`, `(r1 × r2) · k ≠ 0`, and every real `x`, the states `(r1, v1(x))` and `(r2, v2(x))` have one orbit: both positions lie on its path, its velocities there are `v1(x)` and `v2(x)`, and its angular momentum `h` has `h · k > 0`.  Its energy satisfies `2/|r1| - |v1(x)|²/μ = 2 (1 - x²)/s`, so by `orbitOf_ecc` the orbit is an ellipse with `1 - x² = s/(2a)` exactly when `|x| < 1`, a parabola when `|x| = 1`, and a hyperbola when `|x| > 1`.  Conversely, every orbit whose path holds `r1` and `r2` and whose `h` has `h · k > 0` has the velocities `v1(x)` and `v2(x)` there for some `x`.  The identities hold for every `x`, since `y + λ x > 0` whenever `λ² < 1`, and the domain `x > -1` enters with the time.

**L7** (`izzo_target`, `izzo_arrival`, `izzo_no_arrival`).  For `μ > 0`, `(r1 × r2) · k ≠ 0`, and every `x`, the state `(r1, v1(x))` has `β = 4γ² (1 - x²)/s²`, and its motion reaches `r2` at the advance `χ` exactly when `U2 = 2 c1²` and `U1 = 2 c0 c1`, with `c0 = x y + λ (1 - x²)` and `c1 = (y - λ x) s/(2γ)`.  For `x > -1` the motion first reaches `r2` at the advance `χ = 2ψ/√β` with `ψ = arccos c0` in `(0, π)` along an ellipse (`x < 1`), at `χ = 2 c1` along a parabola (`x = 1`), or at `χ = 2ψ/√(-β)` with `ψ = arcosh c0 > 0` along a hyperbola (`x > 1`), and the time of that advance is `√(s³/(2μ)) T(x)`.  For `x ≤ -1`, `β ≤ 0`, so the orbit is a parabola or a hyperbola, and `c0 < 0`, and its motion reaches `r2` at no positive advance: `U1` is positive for `χ > 0` when `β ≤ 0`, while `2 c0 c1` is negative.

**L8** (`lambert_transfer`, `lambert_newton`).  For `μ > 0`, `t > 0`, `(r1 × r2) · k ≠ 0`, and every velocity `v` at `r1`, `ConicTransfer μ r1 v r2 t` with `(r1 × v) · k > 0` holds exactly when `v = v1(x*)`.  For every velocity `v'` at `r2` as well, `NewtonTransfer μ r1 v r2 v' t` with `(r1 × v) · k > 0` holds exactly when `v = v1(x*)` and `v' = v2(x*)`.  By N1, on its interval every solution of Newton's equation through `(r1, v)` is the motion of C1, and conversely the motion of C1 from `(r1, v1(x*))` is such a solution on every interval.

L6, L7, and L8 state both directions of Lambert's theorem for transfers along every conic, with the motion along an orbit given by the universal form of Kepler's equation, and for the solutions of Newton's equation.  By L7 and `orbitOf_ecc`, the conic of the transfer is an ellipse, a parabola, or a hyperbola as `x*` lies below, at, or above 1.  The tests check both directions numerically as well: the first at the solution `x*` of each of the 450 grid inputs with `T* ≤ 20`, by propagating the 50-digit solution from `r1` for the time `t` and comparing both the position and the velocity with `r2` and `v2(x*)`, and the second by the round trip, which propagates random states of every conic for less than one revolution and checks that Izzo's solution recovers the initial velocity.

### Program

| Entry | Arguments | Result |
|---|---|---|
| `lambertBox` | six intervals of the coordinates of `r1` and `r2`, intervals of `t` and `μ`, and the three binary64 components of `k` | status, an interval of `x`, and three intervals for each of `v1` and `v2` |
| `lambertBounds` | the endpoints of the eight intervals and the components of `k`, all binary64 | the same |

The program checks the inputs and computes intervals of `n1`, `n2`, `c`, `s`, `(r1 × r2) · k`, `λ`, and `T*`.  It requires the interval of `(r1 × r2) · k` to lie above or below zero, which fixes the sign of `λ` over the boxes and excludes the transfer angles 0 and π.  For a binary64 `m > -1`, the interval function `tofI` encloses `T(m)` for every `λ` in its interval, from the library's `acos` and `log`, each within one step of the nearest-even rounding, widened by two steps: `ψ = arccos(g)` below 1, with `g` clamped to `[-1, 1]`, and `ψ = log(g + √(max(g² - 1, 0))) = arcosh(g)` above 1.  It forms `1 - m²` as `(1 - m)(1 + m)`.  The radicands of `λ`, `y`, and `σ` are taken as `max(·, 0)`, which leaves each real value unchanged, since the square root of a negative number is 0 in the model.

The search starts from `a0 = -1 + 2^-52`, where `T` exceeds `3·10²³`, and `b0 = 1 + 4/T*`, computed from the lower endpoint of `T*`, where `tof_le_of_gt` gives `T(b0) ≤ 2(1 - λ)/√(b0² - 1) < T*`.  It requires `tofI` to show `T(a0) > T*` and `T(b0) < T*` for every point of the intervals, and it returns status 3 when `tofI` cannot, including when `b0` overflows.  When `tofI` shows `T(1) > T*` the searches start from `[1, b0]`, when it shows `T(1) < T*` from `[a0, 1]`, and otherwise from `[a0, b0]`: at exactly 1 the branch `(2/3)(1 - λ³)` is accurate, while near 1 the closed forms lose their precision over a region up to about `3·10⁻⁵` wide, and a probe there that decided neither side would move a point past the root.  Two bisections then run, each for at most 256 steps.  The first keeps a lower point `a` with `T(a) > T*` shown by `tofI` and moves it up; the second keeps an upper point `b` with `T(b) < T*` and moves it down.  A step evaluates `tofI` at the binary64 midpoint `m`, keeps `m` when `tofI` shows the property and discards the other half otherwise, and a bisection finishes when the midpoint is not finite or does not lie strictly between its two points.  Because `T` is strictly decreasing, `a < x* < b` for every input in the boxes, and the program evaluates the velocity formulas in interval arithmetic with `x` in `[a, b]`.

| Status | Meaning |
|---|---|
| 0 | The interval of `x` contains `x*`, and the six intervals contain the components of `v1` and `v2`, for every input in the boxes. |
| 1 | Invalid input: an endpoint that is not finite, a lower endpoint above its upper endpoint, an interval of `t` or `μ` that does not lie above zero, or a component of `k` that is not finite. |
| 2 | The interval of `(r1 × r2) · k` contains zero, or another interval operation rejected. |
| 3 | `tofI` does not show `T(a0) > T*` and `T(b0) < T*`. |
| 4 | A bisection reached 256 steps without finishing. |

### Program theorems

**L4** (`lambertBox_sound`, `lambertBounds_sound`).  If the program returns status 0, then for every input in the boxes, `-1 < λ < 1`, `T* > 0`, the solution `x*` of L3 lies in the interval of `x`, and the intervals of `v1` and `v2` contain the components of the velocities of Izzo's formulas at `x*`.

**L5** (`lambertCompiled.lambertBox.implements`, `lambertCompiled.lambertBounds.implements`).  The module's exports return the words of `lambertBox` and `lambertBounds` for argument words that represent their arguments.

**L9** (`lambertBox_transfer`, `lambertBounds_transfer`, with `lambertBox_accepts`).  If the program returns status 0, then for every input in the boxes `t > 0`, `μ > 0`, and `(r1 × r2) · k ≠ 0`, exactly one pair of velocities `(v, v')` satisfies `NewtonTransfer μ r1 v r2 v' t` with `(r1 × v) · k > 0`, and the six intervals of the velocities contain the components of `v` and `v'`.  By L8 the pair is `(v1(x*), v2(x*))`, and by L4 the interval of `x` contains `x*`.

### Excluded geometries and widths

| Geometry | Effect |
|---|---|
| Transfer angle 0 or π: `r1` and `r2` on one line through the origin | `r1 × r2 = 0`, the plane of the transfer is undefined, and the status is 2. |
| A plane of the transfer that contains `k` | `(r1 × r2) · k = 0`, the direction of motion does not determine the transfer angle, and the status is 2.  A caller chooses `k` away from the plane. |
| Boxes that reach either geometry, or the origin | Status 2. |
| One or more full revolutions | Outside the demo. |
| Near-parabolic transfers, `x` near 1 | `arccos` and `arcosh` near 1 and the division by `1 - x²` lose relative accuracy over a region up to about `3·10⁻⁵` wide, so the interval of `x` widens to that size when `x*` lies within it.  The program does not use Izzo's series near 1. |
| `λ` near ±1, a chord much shorter than the radii | `y` and `σ` lose precision, and the intervals widen. |
| `T*` above `T(a0)`, about `3·10²³`, or so small that `4/T*` overflows | Status 3. |

## Tests

The tests use oracles written apart from the programs, in Python with PEP 723 metadata, run with `uv run`, and the existing dependency `mpmath==1.3.0`.  Every comparison of an interval with a 50-digit value is exact.

| Test | Oracle | Requirement |
|---|---|---|
| Gibbs containment | Elliptic, circular, equatorial, parabolic, and hyperbolic orbits propagated by the universal-variable form of Kepler's equation at 50 digits, with boxes around three positions at nominal separations of 1°, 5°, 20°, and 60°, the angle that a circular orbit of radius `|r1|` sweeps in the time step, of relative half-width 0 and from `10⁻¹²` to `10⁻³` | Every true velocity lies in the box of status 0, and every other status is 2, for half-widths of `10⁻⁶` and more, or `10⁻⁹` at 1° |
| Gibbs widths | The same | The relative half-width of the result is at most 300 times the relative half-width of the boxes, or `2^-52` for exact positions, over the cube of the nominal separation in radians, an envelope of the measured constant 254 |
| Gibbs statuses | Positions in reverse order, a position off the plane by much more than the box width, wide boxes off the plane by less than their width, and collinear positions | Status 0 with a box that contains `-v(r2)`, status 1, a status other than 1, and status 2 |
| Lambert containment | Izzo's equation solved at 50 digits for transfer angles from 5° to 355°, ratios of radii from 1 to 3, `T*` from 0.05 to 1000, axes `k` along `z`, tilted, and with a `z` component of the opposite sign, and box half-widths 0, `10⁻⁹`, and `10⁻⁶`, which give `|λ|` up to about 0.96 | `x*`, `v1`, and `v2` at the center and at sampled corners of the boxes lie in the intervals of status 0; exact inputs give status 0, and boxes give status 0 except at transfer angles within 5° of 180° and at 5° and 355°, or at `T* = 1000` |
| Lambert widths | The same, and an equal-radius transfer of 1.15°, where `λ` is about 0.99, at `T*` near 2, where the first midpoint lies within `10⁻⁷` of 1 | For `x*` at least `0.01` from 1, the interval of `x` is at most `10⁻¹¹`, `10⁻⁵`, and `10⁻²` wide relative to `max(1, |x*|)` for box half-widths 0, `10⁻⁹`, and `10⁻⁶`, limits that a search moving past the root exceeds; the transfer of 1.15° gives intervals at most `10⁻¹⁰` wide |
| Lambert against Izzo's algorithm | A transcription of Izzo's own binary64 implementation for zero revolutions, with its initial guess, Householder iterations, and its Battin, Lagrange, and Lancaster forms | For exact inputs, the axis `z`, and transfer angles more than 5° from 180°, each of Izzo's velocity components lies within `10⁻⁸ |v1|` of its interval |
| Lambert's theorem, first direction | Propagation of `(r1, v1(x*))` for the time `t` at 50 digits, for the grid inputs with `T* ≤ 20` | The end lies within `10⁻³⁰` of `r2` and `v2(x*)` relative to their lengths, and `h · k > 0` |
| Lambert round trip | Random states of every conic, propagated for less than one revolution | Izzo's solution recovers the initial and final velocities within `10⁻³⁰` relative |
| Lambert near-parabolic transfers | Izzo's equation at 50 digits, with Battin's form near `x = 1`, for `T*` within `10⁻³`, `10⁻⁶`, and `10⁻⁹` of the parabolic time | Status 0, containment of `x*`, `v1`, and `v2`, and an interval of `x` at most `10⁻⁶` wide at `10⁻³` and `10⁻⁴` wide closer |
| Lambert statuses | Transfer angle π, a plane that contains `k`, `T* = 4·10²³`, and a negative time | Statuses 2, 2, 3, and 1 |
| Modules | `tests/verified/run.sh --cases gibbs` and `--cases lambert` | Each export agrees with native Lean bit for bit, the axiom audit passes, and the file theorems check |

## What lies outside the theorems

The theorems concern the model.  The agreement of the two-body model with the motion of a satellite under perturbations, the measurement boxes, the frame, and the choice of `μ` are the caller's.  The theorems bound no width: a wide box is sound.  Every theorem depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## References

- R. H. Battin, An Introduction to the Mathematics and Methods of Astrodynamics, revised edition, AIAA, 1999.
- H. D. Curtis, Orbital Mechanics for Engineering Students, fourth edition, Butterworth-Heinemann, 2020, Algorithm 5.1.
- D. Izzo, Revisiting Lambert's problem, Celestial Mechanics and Dynamical Astronomy 121, 2015, 1–15.  https://doi.org/10.1007/s10569-014-9587-y
- E. R. Lancaster and R. C. Blanchard, A unified form of Lambert's theorem, NASA TN D-5368, 1969.  https://ntrs.nasa.gov/citations/19690027552
- D. A. Vallado, Fundamentals of Astrodynamics and Applications, fourth edition, Microcosm Press, 2013, Algorithm 54.
- [The interval layer](../../Library/Numerics/Interval/README.md)
- [The SGP4 demo](../Sgp4/README.md)
