# Initial orbit determination: decisions and review

[The requirements](requirements.md) specify Gibbs' method over position boxes and Lambert's problem for zero revolutions in Izzo's formulation.  This record gives each decision with its reason, the findings of the independent review of the requirements with the response to each, and the open items.

## Decisions

| Question | Choice | Reason |
|---|---|---|
| Model of a two-body orbit | The pair `(h, e)` with the polar equation of its path, a lemma that a state lies on its own orbit, and a lemma that Newton's equation conserves `h` and `e` | It covers ellipses, parabolas, and hyperbolas, needs no orbital elements, and connects to Newton's equation without a theorem on the time along an orbit.  The SGP4 demo's Kepler orbit covers ellipses only and is parametrized by elements, which are undefined for circular and equatorial orbits. |
| Meaning of "three positions on one orbit" | Positions on the path with `D · h > 0` | For positions on a path with `D ≠ 0`, `D · h > 0` is necessary and sufficient for Gibbs' formula to give `v(r2)`; the review confirmed this on 200 orbits of every kind. |
| `N · D` in place of `\|N\| \|D\|` | The dot product | The two agree on a path, and the dot product needs no square root.  G1 and G2 hold for the program as written. |
| Monotonicity of Izzo's time of flight | Integral representations of `T` (L1), whose integrand increases with `1 - x²` | They prove the decrease without derivatives.  A proof from Izzo's derivative `dT/dx` needs a sign argument that fails for `x > 0` with `λ < 0`. |
| Direction of motion | An axis `k` with `h · k > 0` | Izzo's code uses the `z` axis, which leaves every transfer plane that contains `z` undecided.  The axis `k` is Izzo's convention when `k` is the `z` axis. |
| Search | Two bisections of at most 256 steps, one raising the point where `T > T*` is shown and one lowering the point where `T < T*` is shown | Each keeps one invariant.  When the points where the arithmetic cannot decide form one interval around the root, the two end at its edges, so the interval of `x` is as narrow as the arithmetic allows; the starting bracket below keeps that condition.  A single bisection that stops at the first undecided midpoint returned intervals up to 690 times wider in the first review's model (finding 7). |
| Starting bracket | `[1, b0]` when `tofI` shows `T(1) > T*`, `[a0, 1]` when it shows `T(1) < T*`, and `[a0, b0]` otherwise | The first test run found intervals of `x` up to 0.63 wide at `T* = 1.2`: from the bracket `[1/3, 5/3]` the midpoint is 1 within one unit in the last place, where `tofI` decides nothing, and the search that lowers `b` treated it as not below and moved its other point past the root.  A probe that avoided `1 ± 2^-20` was the first fix; the follow-up review found its upper constant wrong (`1 + 2^-24`) and the undecided region near 1 up to `3·10⁻⁵` wide, and proposed this bracket, which the branch `(2/3)(1 - λ³)` at exactly 1 makes accurate.  The proofs need only `bracket_spec`. |
| Status of an unfinished search | Status 4, without intervals | It follows the plan's rule that a theorem covers the accepting status only.  The review's model never needed more than 60 steps. |
| Interval inputs | Every input is an interval: positions, `μ`, and the time of flight | Measurement error enters as boxes, and the theorems quantify over every point of them. |
| Table parameters of the formulas | `enclosure_def` with empty tables for Gibbs' formula and Izzo's velocities | The formulas read no table, and the enclosure theorems hold for the tables `Trig.invPi` and `Trig.halfPi`, to which the empty tables are equal in the interval functions by `rfl`. |
| Lambert's wrapper | `lambertBoundsWith` takes the logarithm's tables, and `lambertBounds` is the wrapper | `verified_compile` admits a wrapper of tables as an entry and never as a callee. |

## Review

A fresh agent reviewed the requirements against the brief 6.1 of the space-operations candidates and the plan's sections on the starting point, what every design states, and candidate 4.  It built its own model at 50 digits from the request, Izzo's text, Lancaster and Blanchard's report, and standard two-body relations, with an interval layer of exact directed rounding, and it ran wrong programs on the planned tests.  It ran no Lean code.

| Finding | Verification | Response |
|---|---|---|
| 1. L3 is the existence and uniqueness of the root of Izzo's equation; the request asks for those of the transfer.  The premise names "the conic of `x`" without defining it, states one direction of Lambert's theorem only, and enters no theorem. | 120 round trips from propagated states, 61 hyperbolic and 30 with `θ > π`, recover the initial velocity to `2.5·10⁻⁴⁹`; for 360 values of `x` the two states of Izzo's formulas have one `h` and one `e` to `1.8·10⁻⁴⁹`. | Partly adopted.  The requirements state that L3 concerns Izzo's equation and that the existence and uniqueness of the transfer rest on Lambert's theorem in both directions, which they state as the model's premise.  The tests check the existence side by propagating the 50-digit solution and the uniqueness side by the round trip.  The theorem that every `x` gives one orbit `(h, e)` through both positions with `h · k > 0` and `1 - x² = s/(2a)`, and the theorem of existence and uniqueness of the transfer from the two directions of Lambert's theorem, are open items 1 and 2. |
| 2. Izzo's text does not state the monotonicity for zero revolutions; Lancaster and Blanchard do.  The reference to their report is a link to an unrelated record, and equation (18) is their form of the time of flight. | The reviewer read both texts. | Adopted: the requirements credit the monotonicity to Lancaster and Blanchard, with L1 and L2 as its proof, name equation (18) as their form, and link `NTRS 19690027552`. |
| 3. The table of `T`, L1, L2, and the brackets hold. | 300 samples of L1 agree to `1.7·10⁻²⁵`; `T(-1 + 2^-52) ≥ 3.36·10²³`; `T(1 + 4/T*)/T* ≤ 1/2` for `T*` from `10⁻³⁰⁰` to `10²⁹³`. | Confirmed.  The Lean proof of L1 for `x > 0` and `x < 0` joins the two sides at `0` by continuity. |
| 4. `tofI` needs clamps that the requirements do not state: the interval of `g` can leave `[-1, 1]` at `a0`. | Without the clamp of `g`, the reviewer's model returned status 3 in 61 of 240 runs. | Adopted.  `acosI` clamps its argument to `[-1, 1]`, `arcoshI` takes `max(g² - 1, 0)`, and the radicands of `λ`, `y`, and `σ` are taken as `max(·, 0)`, which leaves each real value unchanged since `√(max u 0) = √u`.  The requirements state them. |
| 5. Near `x = 1` the interval of `x` stays about `10⁻⁵` wide. | Widths of `1.4·10⁻⁵` at `x* = 1 + 10⁻⁶`. | Recorded: the tests measure the width near `x = 1`, and the requirements state it.  The sine forms of `ψ` or Izzo's series near 1 are open item 3. |
| 6. The propagation test has no workable criterion, and it misses a program that takes the direction from `z`, a wrong `v2`, and unsound bisections. | Propagating the midpoint of the box fails a fixed tolerance near `θ = π`; the wrong programs pass it. | Adopted: the tests propagate the 50-digit solution and compare position and velocity, check `h · k > 0`, check exact containment of `x`, `v1`, and `v2` at the center and at sampled corners of the boxes, and use axes whose sign differs from that of `z`. |
| 7. No width criterion, so sound but wide programs pass. | A single bisection stopping when undecided passes every check with intervals up to 690 times wider. | Adopted: the tests bound the width of `x` for point inputs away from `x = 1` and the width of Gibbs' result in proportion to the box width over the cube of the angular separation. |
| 8. The Gibbs model and the order condition state what "three positions on one orbit" must mean.  `D` is invariant under cyclic permutation, so "middle" means the second argument; a component of `e` along `h` changes nothing. | 200 orbits of every kind; G1 to `3.3·10⁻⁴⁸`; the reversed order gives `-v(r2)`. | Confirmed, and the two points are in the requirements. |
| 9. A program that decides status 1 from the triple product at the box centers with a tolerance passes every planned test; the status tests should expect `-v(r2)` for reversed boxes and cover parabolas and hyperbolas. | The reviewer's model of that program. | Adopted: a case of wide boxes whose centers lie off the plane by less than the box width expects a status other than 1, reversed boxes expect `-v(r2)`, and the Gibbs oracle propagates by universal variables, which covers every conic. |
| 10. Gibbs' interval result is wider than the spread of the velocities by factors of 8 at 60° to 510 at 1°. | Linearized spread against the interval width. | Recorded in the requirements and the README with the demo's own measurements. |
| 11. The signs, the brackets, and the step bound hold; the rounding of `b0`, the status when `tofI` rejects at a bracket, and the start of the second bisection are unspecified. | 120 round trips; the most steps in a bisection was 60. | Adopted: `b0 = 1 + 4/T*` from the lower endpoint of `T*`, status 3 when `tofI` rejects at `a0` or `b0`, and both bisections start from `[a0, b0]`.  A case with `T* = 4·10²³` expects status 3. |
| 12. Wording: the sign of `λ`; `div` rejects a divisor that holds zero; status 2 of Gibbs; `h = 0` lies outside the model; boxes that reach the origin; `λ` near ±1; the test transcription follows Izzo's code; the SGP4 corollary needs `μ = radius³ (xke/60)²`. | Reading. | Adopted in each place. |

The review ran wrong programs on the planned tests.  The table gives those that the revised tests or the theorems detect and how.

| Wrong program | Detected by |
|---|---|
| Gibbs: positions reversed, `r2 × D` for `D × r2`, `S` negated, division by `n1` | Containment of `v(r2)` on non-circular orbits, and G2 |
| Gibbs: no triple-product test | The off-plane status case |
| Gibbs: triple product at the box centers with a tolerance below 1 km or above 100 km | The near-plane or the off-plane status case, and G3 |
| Lambert: `λ` always positive, transverse vector negated, `ρ` negated, wrong branch of `ψ` above 1 | Containment, with transfers above π and hyperbolic transfers |
| Lambert: direction from `z` | Containment with axes whose sign differs from that of `z` |
| Lambert: sign of `vr2` flipped | Containment of `v2` |
| Lambert: single bisection deciding by the midpoint of `tofI`, velocities at `a` only | Containment at 50 digits, and L4 |
| Lambert: no bracket check | The case `T* = 4·10²³` |

Four classes stay undetected by tests alone.  A Gibbs program that uses `|N| |D|` returns the same result on every path, so it is correct for the model and no test separates it.  A Gibbs program that decides status 1 from the triple product at the box centers with a tolerance between 1 km and 100 km passes both status cases, and only G3 excludes it.  A Lambert program that stops a single bisection at the first undecided midpoint is sound, and in the follow-up review's model its widest interval for exact grid inputs, `5.6·10⁻¹²`, lies below the limit of `10⁻¹¹`, although its median width is three times the program's.  A Lambert program that skips the bisection and returns `[a0, b0]` is sound, and only the width criterion rejects it.

## Follow-up review

A second fresh agent reviewed the revised requirements, this record, and the reference test, with an interval model in Python that follows the library's rounding and reproduced the demo's first test run line for line.  It ran no Lean code.  It reported one breach of the rules given to it: one command installed `gmpy2` into a temporary uv environment, and no result depends on it.

| Finding | Response |
|---|---|
| Responses 1 to 4, 6, 8, 11, and 12 resolve their findings or record honestly what stays open; response 10 cited a README that did not exist yet. | The README now gives the demo's own measurements. |
| N1. The constant `aboveOne` of the probe encoded `1 + 2^-24`, not `1 + 2^-20`. | The probe is gone (N2). |
| N2. The region near 1 where `tofI` cannot decide reaches up to `3·10⁻⁵`, far beyond `2^-20`, so 44 of 2,880 near-parabolic inputs and five grid inputs with boxes gave intervals 10 to 10⁴ times wider than needed.  Proposed fix: start from `[a0, 1]` or `[1, b0]` after `tofI` at exactly 1. | Adopted as the starting bracket, with `bracket_spec`.  The tests add the review's case of `λ` near 0.99 with a first midpoint within `10⁻⁷` of 1, and width limits for boxes and near-parabolic transfers. |
| N3. The record claimed that the two bisections always end at the edges of the undecided region and that the width check detects a single bisection stopping when undecided. | Corrected in the decision on the search and in the classes that no test detects. |
| N4. The section on Lambert's theorem omitted the hypotheses and the timing of the first direction, and called the theorem a premise, while no theorem takes it as a hypothesis; the tests check the first direction only at `x*` and for `T* ≤ 20`. | Adopted: the section is now "Lambert's theorem, an assumption outside the theorems", with the hypotheses `μ > 0`, `t > 0`, `(r1 × r2) · k ≠ 0` and the first arrival after sweeping `θ`, and states the scope of the tests.  A Lean proposition over `Newton` solutions with a corollary of L4 under it is part of open items 1 and 2. |
| N5. The Gibbs separations are nominal, and the limit of 300 is a measured envelope. | Stated in the test table. |
| N6. "The whole ellipse for `|e| < 1`" is wrong once `e` has a component along `h`. | The requirements state the shape with the component `e⊥` normal to `h`. |
| N7. `tof_le_of_gt` proves `T(b0) < T*`, not `T*/2`. | The requirements cite the bound that is proved. |
| N8. The test accepted any status other than 0 where the table said 2, skipped Izzo's comparison near 180° and allowed other statuses for some boxes without saying so, and repeated one failure through a running maximum. | The test now requires status 2, the table states the exceptions, and the comparison checks each case. |
| N9. The limit of `10⁻¹¹` holds for the grid, whose `|λ|` reaches about 0.96, and fails near `|λ| = 0.99`. | The table states the range of `λ`. |
| N10. The round trip's parabolic states needed the threshold on `α`. | Already resolved. |

## Open items

1. A theorem that for every `x > -1` the states `(r1, v1(x))` and `(r2, v2(x))` have one orbit `(h, e)` with `h · k > 0` and `1 - x² = s/(2a)`.  `LambertOrbit.lean` proves the two scalar identities on which it rests, `core_one` and `core_two`; the vector step and the geometric facts, among them `sg |r1 × r2| = λ σ c s`, remain.
2. Lambert's theorem in both directions for the model of Newton's equation, which needs the time along an orbit: Kepler's equation for ellipses, as the SGP4 demo states it, and its hyperbolic and parabolic forms.
3. The sine forms of `ψ` or Izzo's series near `x = 1`, for near-parabolic transfers.
4. A centered form of Gibbs' formula, to narrow its result for wide boxes and close positions.
5. The Gibbs corollary for three positions of the SGP4 demo's Kepler orbit, with `μ = radius³ (xke/60)²`.
