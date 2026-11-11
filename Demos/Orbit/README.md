# Initial orbit determination

This demo computes the velocity of a two-body orbit from positions by two classical methods and returns boxes that contain the model's result for every input in the measurement boxes.  [Gibbs' method](GibbsBox.lean) takes boxes of three positions and returns a box of the velocity at the second.  [Lambert's program](LambertBox.lean) takes boxes of two positions, an interval of the time of flight, and an axis of the direction of motion, solves Izzo's equation for zero revolutions by bisection, and returns boxes of the velocities at both positions.  Both programs are written in the verified compiler's dialect on [the interval layer](../../Library/Numerics/Interval/README.md) and compile to WebAssembly modules with call theorems.  For Lambert's problem the theorems also prove Lambert's theorem: exactly one solution of Newton's equation moves from the first position in the given direction of motion and first reaches the second after the given time, along an ellipse, a parabola, or a hyperbola, and its velocities at the two positions are Izzo's at the root.  [The requirements](requirements.md) define every quantity, and [the review](review.md) records the decisions, the independent reviews, and the open items.

## Example

Curtis's Examples 5.1 and 5.2 give positions in km with `μ = 398600` km³/s².  For Example 5.1, with boxes of half-width 0.1 km around the three printed positions, `gibbsBounds` returns status 0 and the intervals below, which contain Curtis's `v2 = (-6.2174, -4.0122, 1.5990)` km/s.  With the printed positions as exact points it returns status 1: rounded to 0.1 km, the three points do not lie in one plane through the origin, so no orbit passes through them.

| Component | Lower endpoint | Upper endpoint |
|---|---|---|
| `vx` (km/s) | −6.381701 | −6.057409 |
| `vy` (km/s) | −4.187753 | −3.841238 |
| `vz` (km/s) | 1.452555 | 1.749444 |

The intervals are about 0.3 km/s wide for boxes of 0.1 km at separations near 10°.  Interval evaluation overestimates the spread of the velocity over the orbits through the boxes, because each coordinate occurs many times in the formula, and the section on tests measures the width.

For Example 5.2, with `r1 = (5000, 10000, 2100)` km, `r2 = (-14600, 2500, 7000)` km, `t = 3600` s, and the axis `k = (0, 0, 1)`, `lambertBounds` returns status 0 with `x` in an interval at 0.619452 and intervals of the velocities at `v1 = (-5.992495, 1.925363, 3.245637)` and `v2 = (-3.312460, -4.196617, -0.385288)` km/s to the printed digits, which agree with Curtis's values to the digits he prints.

## The model

An orbit is a pair `(h, e)` of the angular momentum per unit mass and the eccentricity vector, with `h ≠ 0`.  Its path is the set of positions `r` with `r · h = 0` and `|r| + e · r = |h|²/μ`, and its velocity at `r` is `(μ/|h|²) h × (e + r/|r|)`, in [`TwoBody.lean`](TwoBody.lean).  The model covers ellipses, parabolas, and hyperbolas alike, and [`Newton.lean`](Newton.lean) proves that Newton's equation conserves `h` and `e`, so the positions and velocities of its solutions are those of one orbit.  Three positions lie in the order of motion, within less than one revolution, when `D · h > 0` for the normal `D = (r2 - r1) × (r3 - r1)` of their triangle.

Along every conic, [`Universal.lean`](Universal.lean) gives the motion from a state `(r, v)` with `r × v ≠ 0` by the universal form of Kepler's equation.  With `β = 2μ/|r| - |v|²`, which is `μ/a` for an ellipse of semimajor axis `a` and, since `|e|² = 1 - β |h|²/μ²`, positive, zero, or negative as the orbit is an ellipse, a parabola, or a hyperbola, the universal variable `χ` advances at the rate `dχ/dt = 1/|r|`, and the universal functions `U0` to `U3` are `cos(√β χ)`, `sin(√β χ)/√β`, `(1 - cos(√β χ))/β`, and `(χ - sin(√β χ)/√β)/β`, their hyperbolic forms for `β < 0`, and `1`, `χ`, `χ²/2`, and `χ³/6` for `β = 0`.  The position is `f r + g v` with Lagrange's coefficients `f = 1 - μ U2/|r|` and `g = |r| U1 + (r · v) U2`, and the time is `|r| U1 + (r · v) U2 + μ U3`, which is Kepler's equation for an ellipse, its hyperbolic form for a hyperbola, and Barker's equation for a parabola.  These quantities need no perifocal axes, so a circular orbit is no special case.  The positions lie on the orbit's path, and inverting the time gives a solution of Newton's equation through `(r, v)`.  A motion first reaches a position `r'` after the time `t` (`ConicTransfer`) when an advance `χ > 0` takes it to `r'` in the time `t` and no smaller positive advance does.  [`NewtonUnique.lean`](NewtonUnique.lean) proves that a solution of Newton's equation on an open interval of times is determined by its state at one time of the interval, so on its interval every solution through `(r, v)` is this motion.

For Lambert's problem the model is Izzo's time-of-flight equation `T(x) = T*`, with `T*` the nondimensional time, `λ` the parameter of the geometry whose sign is fixed by the direction of motion, and Izzo's velocity formulas at the root.  The theorems relate the equation to the two-body model for `μ > 0` and `(r1 × r2) · k ≠ 0`.  For every `x`, Izzo's velocities at `r1` and `r2` are those of one orbit whose angular momentum has a positive component along `k`, with `2/|r1| - |v1|²/μ = 2 (1 - x²)/s`, so that by the identity for `|e|²` the orbit is an ellipse with `1 - x² = s/(2a)` exactly when `|x| < 1`, a parabola when `|x| = 1`, and a hyperbola otherwise.  Every orbit through both positions in that direction is Izzo's for some `x`.  For `x > -1` the motion along the orbit first reaches `r2` after the time `√(s³/(2μ)) T(x)`, and for `x ≤ -1` it does not reach `r2` after leaving `r1`.  With the uniqueness of the root, exactly one motion along a conic in the direction of `k`, and exactly one solution of Newton's equation, first reaches `r2` after the time `t`: the one that starts with Izzo's velocity at the root `x*`.

## Programs

| Export | Arguments | Result |
|---|---|---|
| `gibbsBox`, `gibbsBounds` | Nine intervals of three positions and one of `μ`, or their twenty endpoints | Status and three intervals of the velocity at the second position |
| `lambertBox`, `lambertBounds` | Six intervals of two positions, intervals of `t` and `μ`, and the axis `k`, or the endpoints and `k` | Status, an interval of `x`, and six intervals of the velocities at both positions |

| Status | Gibbs | Lambert |
|---|---|---|
| 0 | The intervals contain the velocity at the second position of every orbit through the boxes in the order of motion. | The intervals contain the root of Izzo's equation and Izzo's velocities at it for every input in the boxes. |
| 1 | No orbit passes through the three boxes: their triple product's interval excludes zero. | Invalid input. |
| 2 | An interval operation rejected: boxes too wide, too close to collinear, out of order, or reaching the origin. | The interval of `(r1 × r2) · k` holds zero, which includes the transfer angles 0 and π, or an interval operation rejected. |
| 3 | Invalid input. | The interval evaluation of `T` does not show the brackets `T(-1 + 2^-52) > T*` and `T(1 + 4/T*) < T*`. |
| 4 | | A bisection reached 256 steps without finishing. |

Gibbs' program evaluates the formula of Curtis and Vallado, `√(μ/(N · D)) (D × r2/|r2| + S)`, in interval arithmetic, after a test of the triple product `r1 · (r2 × r3)`, which is zero for the positions of any orbit.  Lambert's program computes intervals of `λ` and `T*`, encloses `T` at binary64 points from the library's `acos` and `log`, and runs two bisections: one raises a point where the enclosure shows `T > T*`, and one lowers a point where it shows `T < T*`.  Both start from `[a0, 1]` or `[1, b0]` when the enclosure at exactly 1, where `T = (2/3)(1 - λ³)` is accurate, decides the side of 1, since near 1 the closed forms lose their precision over a region up to about `3·10⁻⁵` wide.  Since `T` is strictly decreasing, the root lies between the two points, and the program evaluates Izzo's velocity formulas with `x` in that interval.

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`, which [the axiom audit](../../tests/orbit/Axioms.lean) reports.

| Theorem | File | Statement |
|---|---|---|
| `orbitOf_spec` | [`TwoBody.lean`](TwoBody.lean) | A state `(r, v)` with `r × v ≠ 0` lies on the path of its orbit `(r × v, v × (r × v)/μ - r/|r|)`, with velocity `v`. |
| `newton_conserves` | [`Newton.lean`](Newton.lean) | Along a solution of `r'' = -μ r/|r|³` that stays away from the origin, the orbit of the state is the same at every time. |
| `gibbs_velocity` (G1) | [`Gibbs.lean`](Gibbs.lean) | For three positions on the path of an orbit with `D · h > 0`, `N · D > 0` and Gibbs' formula gives the orbit's velocity at the second position. |
| `gibbs_newton` | [`Newton.lean`](Newton.lean) | For three positions of a solution of Newton's equation with `D · h > 0`, Gibbs' formula gives the solution's velocity at the second time. |
| `gibbsBox_sound`, `gibbsBounds_sound` (G2) | [`GibbsSound.lean`](GibbsSound.lean) | For a result with status 0, every `μ` in its interval, and every orbit with positions in the three boxes and `D · h > 0`, the intervals contain the velocity at the second position. |
| `gibbsBox_no_orbit` (G3) | [`GibbsSound.lean`](GibbsSound.lean) | For a result with status 1, no orbit has a position in each of the three boxes. |
| `tof_pos_eq`, `tof_neg_eq` (L1) | [`Lambert.lean`](Lambert.lean) | For `x > 0`, `T(x) = 2 ∫ from λ to 1 of σ²/√(1 - (1 - x²) σ²) dσ`, and for `-1 < x < 0`, `T(x)` is `π/(1 - x²)^(3/2)` less the same integral from `-λ` to 1. |
| `tof_strictAntiOn`, `tof_continuousOn` (L2) | [`LambertRoot.lean`](LambertRoot.lean) | For `-1 < λ < 1`, `T` is continuous and strictly decreasing on `(-1, ∞)`. |
| `exists_unique_root` (L3) | [`LambertRoot.lean`](LambertRoot.lean) | For `-1 < λ < 1` and `T* > 0`, exactly one `x > -1` has `T(x) = T*`. |
| `lambertBox_sound`, `lambertBounds_sound` (L4) | [`LambertSound.lean`](LambertSound.lean) | For a result with status 0 and every input in the boxes, `-1 < λ < 1`, `T* > 0`, and the intervals contain the root and Izzo's velocities at it. |
| `izzo_orbit`, `izzo_energy`, `orbit_izzo` (L6) | [`LambertOrbit.lean`](LambertOrbit.lean) | For `μ > 0`, `(r1 × r2) · k ≠ 0`, and every `x`, the states `(r1, v1(x))` and `(r2, v2(x))` have one orbit, whose angular momentum `h` has `h · k > 0`, and `2/|r1| - |v1|²/μ = 2 (1 - x²)/s`.  Every orbit whose path holds `r1` and `r2`, with `h · k > 0`, has Izzo's velocities there for some `x`. |
| `orbitOf_ecc`, `conicPos_onPath`, `conicPos_norm`, `conicPos_inj`, `conicTime_strictMono`, `conicTime_surjective`, `conic_newton` (C1) | [`Universal.lean`](Universal.lean) | For `μ > 0` and a state with `r × v ≠ 0`, the orbit has `e · h = 0` and `|e|² = 1 - β |h|²/μ²`, the positions of the universal form of Kepler's equation lie on the orbit's path at the distance `R > 0`, are distinct for distinct advances when `β ≤ 0` and within one revolution when `β > 0`, and are reached at increasing times that take every real value, and the motion solves Newton's equation and is at `(r, v)` at the time 0. |
| `newton_unique` (N1) | [`NewtonUnique.lean`](NewtonUnique.lean) | Two solutions of Newton's equation on an open interval of times with the same position and velocity at one time of the interval are equal on the interval. |
| `izzo_target`, `izzo_arrival`, `izzo_no_arrival` (L7) | [`LambertTime.lean`](LambertTime.lean) | For `μ > 0` and `(r1 × r2) · k ≠ 0`, the motion from `(r1, v1(x))` first reaches `r2` at a positive advance whose time is `√(s³/(2μ)) T(x)` when `x > -1`, and reaches `r2` at no positive advance when `x ≤ -1`. |
| `lambert_transfer`, `lambert_newton` (L8) | [`LambertTime.lean`](LambertTime.lean) | For `μ > 0`, `t > 0`, and `(r1 × r2) · k ≠ 0`, a velocity `v` at `r1` starts a motion along a conic in the direction of `k` that first reaches `r2` after the time `t` exactly when `v = v1(x*)`.  A solution of Newton's equation on an open interval of times that contains `[0, t]`, from `(r1, v)` in the direction of `k`, first reaches `r2` at the time `t` with the velocity `v'` exactly when `v = v1(x*)` and `v' = v2(x*)`. |
| `lambertBox_accepts`, `lambertBox_transfer`, `lambertBounds_transfer` (L9) | [`LambertTransfer.lean`](LambertTransfer.lean) | For a result with status 0 and every input in the boxes, `t > 0`, `μ > 0`, and `(r1 × r2) · k ≠ 0`, exactly one pair of velocities at `r1` and `r2` belongs to a solution of Newton's equation, on an open interval of times that contains `[0, t]`, that starts at `r1` in the direction of `k` and first reaches `r2` at the time `t`, and the intervals of the velocities contain that pair. |
| `gibbsCompiled.gibbsBox.implements`, `lambertCompiled.lambertBox.implements`, and their siblings (G4, L5) | [`GibbsVerified.lean`](GibbsVerified.lean), [`LambertVerified.lean`](LambertVerified.lean) | The WebAssembly modules return the values of the Lean functions. |

L1 gives the monotonicity of L2 without derivatives: the integrand increases with `1 - x²` at every `σ ≠ 0`.  Lancaster and Blanchard state the monotonicity for less than one revolution without a proof.  The proof of L4 rests on `tofI_encloses`, the enclosure of `T` at a binary64 point by the one-step accuracy theorems of `acos` and `log`, and on `raise_spec` and `lower_spec`, the invariants of the two bisections.

The proof of L6 writes Izzo's velocities in the basis `r1`, `r2` (`izzo_basis`), as `v1 = α1 r1 + κ r2` and `v2 = -κ r1 + α2 r2`, so that both states have the angular momentum `κ (r1 × r2)`, and the eccentricity vectors agree by the scalar identities `core_one` and `core_two`.  The proofs of L6 and L7 substitute `x = (q² - (1 - λ²))/(2 λ q)` and `y = (q² + 1 - λ²)/(2 q)` with `q = y + λ x`, which removes the relation `y² = 1 - λ² + λ² x²`, so that each identity is one of rational functions.

The proof of C1 uses only the derivatives of `U0` to `U3` and the identities `U0 + β U2 = 1` and `U1² = U2 (1 + U0)`, which hold for every conic, except for the injectivity, which uses the monotonicity of `U1` for `β ≤ 0` and the period of `cos` and `sin` for `β > 0`.  The distance `R` is positive because `|f r + g v|² = R²` and `R + e · (f r + g v) = |h|²/μ`, and it is at least `|h|²/(μ (1 + |e|))`, so the time takes every real value.  L7 follows Lagrange's time equation: the motion reaches `r2` where `U1 = 2 c0 c1` and `U2 = 2 c1²`, with `c0 = x y + λ (1 - x²)` and `c1 = (y - λ x) s/(2γ)`, which is the advance `χ = 2ψ/√|β|` with `ψ = arccos c0` or `arcosh c0`, or `χ = 2 c1` for a parabola, and the time `|r1| U1 + (r1 · v1) U2 + μ U3` reduces to `√(s³/(2μ)) T(x)` by one identity of rational functions for the ellipse and the hyperbola.  For `x ≤ -1`, `c0 < 0`, while `U1 > 0` at every positive advance along a parabola or a hyperbola.  The uniqueness of L8 combines the converse of L6, L7, and L3, and N1 carries it to every solution of Newton's equation on an open interval of times that contains `[0, t]`.  N1 applies Mathlib's local uniqueness theorem for a locally Lipschitz field, `ODE_solution_unique_of_eventually`, to Newton's field on the product of two Euclidean spaces of three coordinates, where the field is continuously differentiable away from `r = 0`.

## Tests

`tests/orbit/run.sh` builds the case executable and runs [the reference test](../../tests/orbit/reference.py), which compares `gibbsBounds` and `lambertBounds` in native Lean with oracles written apart from the programs: a two-body propagator by the universal-variable form of Kepler's equation at 50 digits, Izzo's equation and velocity formulas at 50 digits with Battin's form near `x = 1`, and a transcription of Izzo's own binary64 implementation for zero revolutions.  Every comparison of an interval with a 50-digit value is exact.  The script takes the command that runs the case executable, so that Lean and Python can run on different hosts.

For Gibbs' method, the test propagates four orbits of each kind (elliptic, circular, equatorial, parabolic, and hyperbolic), takes three positions at separations of 1°, 5°, 20°, and 60°, and builds boxes of relative half-width `w` around them, the rounding to binary64 alone for `w = 0`.  Every velocity lies in its box of status 0.  The table gives the median relative half-width of the result, and status 2 where the arithmetic cannot show `N · D > 0`.

| Separation | `w = 0` | `w = 10⁻¹²` | `w = 10⁻⁹` | `w = 10⁻⁶` | `w = 10⁻³` |
|---|---|---|---|---|---|
| 1° | `3.3·10⁻¹⁰` | `2.0·10⁻⁶` | `2.0·10⁻³` | status 2 in 18 of 20 | status 2 |
| 5° | `2.9·10⁻¹²` | `1.6·10⁻⁸` | `1.6·10⁻⁵` | `1.6·10⁻²` | status 2 |
| 20° | `7.0·10⁻¹⁴` | `3.9·10⁻¹⁰` | `3.9·10⁻⁷` | `3.9·10⁻⁴` | `0.41` |
| 60° | `1.2·10⁻¹⁴` | `5.3·10⁻¹¹` | `5.3·10⁻⁸` | `5.3·10⁻⁵` | `5.3·10⁻²` |

The half-width is at most 254 times `max(w, 2⁻⁵²)` over the cube of the separation in radians, against a test bound of 300.  Boxes of positions in reverse order give status 0 and intervals that contain the velocity of the reversed motion, a position 100 km off the plane of the other two gives status 1, boxes of half-width `10⁻³` of the radius whose centers lie 1 km off the plane give status 0, and collinear positions give status 2.

For Lambert's problem, the test covers transfer angles from 5° to 355°, ratios of radii of 1, 1.6, and 3, nondimensional times `T*` from 0.05 to 1000, and axes `k` along `z`, tilted from the pole of the orbit, and with a `z` component of the opposite sign, each with boxes of relative half-width 0, `10⁻⁹`, and `10⁻⁶`.  All 540 inputs give status 0, and the 50-digit root and Izzo's velocities at the center and at four corners of each box lie in the intervals.  For exact inputs and the axis `z`, every velocity component of Izzo's binary64 code lies inside its interval.  Propagating the 50-digit solution from `r1` for the time `t` reaches `r2` and `v2` within `1.0·10⁻⁴³` relative, with `h · k > 0`, and 60 round trips from states of every conic, propagated for less than one revolution, recover the initial and final velocities within `5.8·10⁻⁴⁷`.  The transfer angle π, a transfer plane that contains `k`, `T* = 4·10²³`, and a negative time give statuses 2, 2, 3, and 1.

| Measure | Result |
|---|---|
| Width of the interval of `x` for exact inputs, `x*` at least 0.01 from 1, relative to `max(1, \|x*\|)` | At most `2.1·10⁻¹²` |
| The same for boxes of relative half-width `10⁻⁹` | At most `3.3·10⁻⁶` |
| The same for boxes of relative half-width `10⁻⁶` | At most `2.5·10⁻³`, at a transfer angle of 5° where `∂x/∂λ` is near 38 |
| Width for `x*` about `1.5·10⁻³` from 1 | `2.1·10⁻¹⁰` to `1.4·10⁻⁹` |
| Width for `x*` within `2·10⁻⁶` of 1 | `6.2·10⁻⁶` to `1.2·10⁻⁵` |
| Width for a transfer of 1.15° with `λ` near 0.99 and a first midpoint within `10⁻⁷` of 1 | At most `4.1·10⁻¹⁵` |

The first run of the test found intervals of `x` up to 0.63 wide for exact inputs at `T* = 1.2`: a bisection probed a point within one unit in the last place of 1, where the closed forms of `T` decide nothing, and moved its other point past the root.  The starting bracket at 1 removes the cause, with no change to the invariants of the searches.

`tests/verified/run.sh --cases gibbs` and `--cases lambert` compare each module with native Lean bit for bit on the cases of [the case file](../../tests/TestSupport/Orbit/Cases.lean), run [the axiom audit](../../tests/orbit/Axioms.lean), and check the file theorems.

| Module | Size | Calls compared | Compilation |
|---|---|---|---|
| `gibbs` | 10,013 bytes | 9 | 239 s |
| `lambert` | 24,911 bytes | 8 | 915 s |

## Limits

The theorems concern the model.  They state Lambert's theorem along every conic and for every solution of Newton's equation, so that for every input in the boxes of a result with status 0 the intervals contain the velocities of the one two-body transfer in the given direction of motion that first reaches the second position at the given time.  Transfers that pass the second position before they reach it at the given time, those of one or more full revolutions, lie outside the demo.  The theorems bound no width: interval evaluation of Gibbs' formula overestimates the spread of the velocity by a factor that grows as the positions come closer, and near-parabolic transfers give intervals of `x` near `10⁻⁵` wide.  The agreement of the two-body model with the motion of a satellite, the measurement boxes, the frame, and the value of `μ` are the caller's, and [the review](review.md#open-items) lists the open items.

## References

- [Initial orbit determination requirements](requirements.md)
- H. D. Curtis, Orbital Mechanics for Engineering Students, fourth edition, Butterworth-Heinemann, 2020, Algorithms 5.1 and 5.2.
- D. Izzo, [Revisiting Lambert's problem](https://doi.org/10.1007/s10569-014-9587-y), Celestial Mechanics and Dynamical Astronomy 121, 2015, 1–15.
- E. R. Lancaster and R. C. Blanchard, [A unified form of Lambert's theorem](https://ntrs.nasa.gov/citations/19690027552), NASA TN D-5368, 1969.
- D. A. Vallado, Fundamentals of Astrodynamics and Applications, fourth edition, Microcosm Press, 2013, Algorithm 54.
