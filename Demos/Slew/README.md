# Slew: constraint-checked attitude slews

[The program](Program.lean) plans a slew of a spacecraft from a start attitude to a goal attitude
as a sequence of rest-to-rest eigenaxis rotations through a set of waypoint attitudes.  It checks
every rotation it returns against cones that keep body vectors out of or inside given directions,
and it returns the path of least total duration, in whole milliseconds, among the paths of its
graph.  The program is written in the verified compiler's dialect, takes one array of
binary64 values, and returns one, and [the development
journal](../../devnotes.md#2026-10-26-the-slew-planner-program-theorems-and-tests) holds the plan
for its compilation, its tests, and its theorems.

`verified_compile` compiles the program into a module of 26,362 bytes, whose `plan` export agrees
with native Lean, bit for bit, on all 852 generated plans and 1,225 `atan2` calls in Wasmtime.
The compiler's generated theorems state that the module computes `plan`.  [The safety
section](#safety) states the theorem that every plan of status 1 keeps every cone along its
commanded rotations, which rests on the soundness of the edge check and the static check
([the soundness section](#soundness-of-the-checks)), and [the NaN-freedom
section](#nan-freedom) states that every floating-point value that the planner computes from a
validated input is finite.  [The test section](#tests) describes the cases, and [the theorem
section](#theorems-to-prove) lists the theorems that remain.

| File | Contents |
|---|---|
| [The program](Program.lean) | The planner in the dialect |
| [The representations](Flat.lean) | `Flat` instances for `V3`, `Q4`, `Dims`, and `Search` |
| [The compilation](Verified.lean) | `verified_compile compiled := [atan, atan2, …, plan]` |
| [The specification](Spec.lean) | Real vectors and quaternions, Rodrigues' rotation, the rotation angle, and the cone predicate |
| [The arc lemmas](Arc.lean) | The sinusoid form of the cosine along a rotation, the endpoint lemma, and vector inequalities |
| [The binary64 facts](Rounding.lean) | Real values of floats, comparisons, the program's constants, and the bounded approximation `Bnd` |
| [The vector errors](Error.lean) | Rounding errors of dot and cross products and of the rotation formula |
| [The axis and angle](Axis.lean) | Rounding errors of `s`, the axis `v/s`, `w² - s²`, and `2ws` |
| [The normalization](Normalize.lean) | The difference between the cosines of the normalized and the given inputs |
| [The cone values](Cone.lean) | Rounding errors of `f₀`, `A`, `B`, `C`, `f₁`, and `f′(θ)` |
| [The amplitude](Hypot.lean) | The rounding error of `√(A² + B²)` |
| [The decisions](Decide.lean) | Comparisons, NaN propagation, and the bounds that a decision gives over the rotation |
| [The soundness](Check.lean) | `edgeOk_sound` and `attitudeOk_sound` |
| [The rotations](Rotation.lean) | Quaternion products and actions, their composition and distances, and Rodrigues' rotation as an action |
| [The relative quaternion](Relative.lean) | `GoodRel` for `relative` and the distance of its rotation from the exact one |
| [The input](Valid.lean) | `GoodQ` for every node and `ConeGood` for every cone of a validated input |
| [The search](Search.lean) | The invariant of `search` and the segments of a plan as accepted edges |
| [The output](Angle.lean) | The output's axis and angle against those of the relative quaternion |
| [The safety theorem](Safety.lean) | `plan_safe` |
| [NaN-freedom](NanFree.lean) | `plan_finite` |
| [The premise theorem](Premise.lean) | `plan_premise` |
| [The allocation bound](Bound.lean) | `plan_bound` and `slew_trapFree` |

The program imports only the dialect modules and `Library.Numerics.Float64.Atan.Program`, which
build from Lean's core library.  The representations need `LeanExe.Pipeline`, which depends on
Talos's CodeLib, and the compilation and the proofs need Mathlib.  `Demos.lean` imports the
program, the representations, and the proofs, and `Demos/Verified.lean` imports the compilation
and the allocation bound.

## The planning problem

An attitude is a quaternion `q = [w, x, y, z]` that maps body coordinates to inertial coordinates.
A cone names a body vector `b`, an inertial axis `u`, the cosine `c` of its half-angle, and a kind.
A keep-out cone requires `u · R(q) b ≤ c`, and a keep-in cone requires `u · R(q) b ≥ c`.

A segment is a rest-to-rest rotation about a fixed inertial axis `n` by an angle `θ` in `[0, π]`,
with a rate limit `ω` and an acceleration limit `a`.  It lasts `θ/ω + ω/a` when `θ ≥ ω²/a` and
`2 √(θ/a)` otherwise, followed by a settling time, and the attitudes it visits do not depend on its
time profile.  The graph's nodes are the start, the goal, and the waypoints, and an edge joins two
nodes when the rotation between them is at most `maxEdge`, or joins the start to the goal, and
the edge check accepts it.

## Interface

```text
input   header (8):  version = 2, nBody, nCone, nWay, rate limit (rad/s), acceleration limit (rad/s²),
                     settling time (s), maxEdge (rad)
        q0 (4), q1 (4)          start and goal attitudes
        body vectors (3 each)   body frame
        cones (6 each)          body index, axis x, y, z, cosine of the half-angle, kind (0 keep-out, 1 keep-in)
        waypoints (4 each)

output  header (4):  status, k (segments), total cost (ms), nodes finalized
        segments (11 each): start quaternion (4), axis (3), angle (rad), cost (ms), from node, to node
        goal quaternion (4)

status   1 plan found
         0 no path in the graph
        -1 start attitude violates a cone
        -2 goal attitude violates a cone
        -3 invalid input
```

Only status 1 has segments and the goal quaternion.  Each segment's start quaternion is the input's
start or waypoint quaternion, bit for bit, and its axis and angle are the rotation that the plan
commands.  Costs are whole numbers of milliseconds held as binary64 values, which are exact below
`2^53`.

## Program structure

The program follows the drone planner: flat arrays, counted loops through `LeanExe.loop`,
`LeanExe.build`, and `LeanExe.repeatWhile`, ties to the lowest index, and replacement only on
strict improvement.  It works in five stages.

1. `validInput` rejects anything outside the interface, with status -3.  It requires:
   - version 2, and counts that are whole numbers within bounds (1 to 8 bodies, up to 16 cones,
     up to 1,024 waypoints) and that match the length;
   - finite values, a rate limit in `[1e-5, 1]`, an acceleration limit in `[1e-7, 1]`, a settling
     time in `[0, 3600]`, and `maxEdge` in `[0, 4]`;
   - a squared norm within `1e-12` of 1 for every vector and quaternion;
   - cone body indices in range, cosines in `[-1, 1]`, and kinds 0 or 1.
2. `attitudeOk` checks one attitude against every cone.  The start and goal get status -1 or -2
   on failure, and failing waypoints are left out of the graph.
3. `search` runs array Dijkstra over the start, the goal, and the waypoints.  `relax` computes
   each candidate edge's relative quaternion (`relative`), its angle (`angleOf`, with the
   library's `atan2`), and its cost (`slewTicks`).  It calls `edgeOk` only when the candidate
   would strictly improve the target's cost, in an `if` of its own, since the compiled code
   evaluates both operands of `&&`.
4. `edgeOk` is the closed-form check described below.
5. `output` follows the parent chain and writes the segments.

During a rotation by `φ` about the unit axis `n`, the cosine between a body vector `v₀` and a cone
axis `u` is `f(φ) = A cos φ + B sin φ + C`, with `A = u·v₀ - (n·u)(n·v₀)`, `B = u·(n × v₀)`, and
`C = (n·u)(n·v₀)`.  On `[0, θ]` with `θ ≤ π`, `f` has an interior maximum only when `B > 0` and
`f′(θ) = B cos θ - A sin θ < 0`, of value `C + √(A² + B²)`, and an interior minimum only when
`B < 0` and `f′(θ) > 0`, of value `C - √(A² + B²)`.  The relative quaternion `[w, v]` with
`w ≥ 0` gives `cos θ = w² - s²` and `sin θ = 2ws` for `s = |v|`, so the check needs no
trigonometric function.

The check compares the endpoint values, and the stationary value unless a computed test excludes it
by more than `eta = 1e-12`, with the cone's cosine tightened by `margin`, the double nearest
`1.1e-9`.  The margin covers a rounding allowance of `1e-10` and a tube of `1e-9` rad around the
commanded rotation.  Below `s = 1e-7` the axis `v/s` is unreliable, and the check tests the start
attitude with `2.125 s` more slack, since no vector moves farther than the rotation angle.  Each
edge costs `⌈1000 T(θ)⌉ + ⌈1000 t_settle⌉` milliseconds, each ceiling built from the saturating
`Float.toUInt64`, because the verified compiler has no rule for `Float.ceil`.  An unreached node
costs `2^62`, and no path cost comes near it, since an edge costs less than `3.2e8` ms.

## Compilation

These commands build the compilation, write the module, and validate it.  The build of
`Verified.lean` takes about 3 minutes, and `tests/verified/run.sh --cases slew` runs the same steps
before it runs the cases.

```sh
tools/leanrun --timeout 60m lake build Demos.Slew.Verified
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Demos.Slew.Verified Demos.Slew.Verified.compiled.module build/verified/slew.wasm
wasm-tools validate build/verified/slew.wasm
```

The reflector needed one change to the program: `segmentField` bound `let big := sn ≥ axisMin`,
a proposition, which the dialect does not hold, and `let big : Bool := sn ≥ axisMin` replaces it
with the same meaning.  It accepts the index forms `p.1.toNat` and `(1 : UInt64).toNat`.  The
compilation yields these results:

- `compiled.plan.implements` states `ImplementsA true compiled.module 28 plan`, and the argument's
  type is `Array Float` rather than `Moved`, so `plan` borrows its input.
- `compiled.bytes` and `compiled.plan.trapFree` depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- `compiled.plan.bound_eq` states the allocation bound as `compiled.search.bound` plus
  `compiled.output.bound` for validated input.  `round` and `relax` take the search state, a
  record with array fields, as a parameter, and the verified compiler borrows every record
  parameter, so their updates copy arrays of up to 1,026 words in each of up to 1,027 rounds, and
  the bound counts each copy without reuse.
- [The allocation bound](Bound.lean) `plan_bound` bounds `compiled.plan.bound` by 68,020,488 bytes
  for every input: four arrays of at most 1,026 words from `initial`, two copies of them in each
  round, and an output of at most 11,294 words.  `slew_trapFree` states that the export computes
  `plan` without a trap whenever `top` can rise by 68,020,488 bytes within the memory's cap, and
  both depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Soundness of the checks

[The soundness proof](Check.lean) shows that `edgeOk` and `attitudeOk` accept only what the cones
allow, as statements about real numbers.  `edgeOk_sound` assumes an attitude `qa` with finite
components and a squared norm within `3e-12` of 1, a relative quaternion `rel` that is finite, has
`w ≥ 0`, and has a squared norm within `1e-11` of 1, and cones whose body vectors and axes are
finite with squared norms within `3e-12` of 1 and whose cosines are finite and in `[-1, 1]`.  If
`edgeOk` accepts `rel` from `qa`, then for every cone and every angle `φ` from 0 to the rotation
angle of `rel`'s real value, every vector within `1.05e-9` of the normalized body vector, rotated
by the normalized `qa` and then by `φ` about the axis of `rel`'s real value, lies on the allowed
side of the cone of the normalized axis.  `attitudeOk_sound` states the same at one attitude for
`attitudeOk` without slack, and both theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

The proof bounds each rounding error against the program's formulas in exact arithmetic on the
given, unnormalized inputs, which keeps the errors of the stationary-point tests below `eta`.
The normalization enters once, in the final bound.  The table lists the parts of the budget for
a rotation past the small-angle threshold, with `u = 2⁻⁵³`.

| Part | Bound |
|---|---|
| Rounding of `f₀`, `f₁`, the stationary value, and the limit | `2300 u`, about `2.6e-13` |
| `w² - s²` and `2ws`, which are `cos θ` and `sin θ` times `w² + s²` | `2.3e-11` |
| Normalization of the attitude, the body vector, and the cone axis | `1.3e-11` |
| The tube | `1.05e-9` |
| Total | about `1.0863e-9`, `1.3e-11` below `margin` |

Below `s = 1e-7`, the slack `2.125 s` exceeds the change `2.0003 S` of the cosine along the
rotation, where `S` is the real length of `rel`'s vector part.  The proof follows the program's
decisions through NaN results: Lean's `max a b` returns `a` when `b` is a NaN, so a keep-out check
that drops a NaN value still bounds the start, and the proof derives the finiteness of every other
value it needs from the error bounds.  The edge check's proof does not exclude a NaN `s`, which
would require `S² ≤ 5 · 2⁻¹⁰⁷⁵`, and the safety proof shows that the computed sum of squares is
never negative, so `s` is finite.

The theorems take the properties of the inputs as hypotheses, and the rotation they describe is
that of `rel`'s real value, which differs from the exact rotation between the normalized
attitudes by the rounding of `relative`.  The safety theorem derives the hypotheses from
`validInput` and `relative` and bounds that difference.

## Safety

[The safety theorem](Safety.lean) `plan_safe` concerns every output of status 1 and assumes
nothing about the input beyond what `validInput` checks.  It states that the output's start and
goal quaternions equal the input's, bit for bit, and that segment `g` of `K` stores its start
quaternion `q_g` at offset `4 + 11g`, its axis `n_g` at `8 + 11g`, and its angle `θ_g` at
`11 + 11g`, with the goal as `q_K`.  For each segment, the normalized axis `n̄_g` has length 1,
and the rotation by `θ_g` about `n̄_g` carries the attitude `R(q̄_g)` to within `1e-9` of
`R(q̄_{g+1})`, where the distance between attitudes is the largest displacement of a unit vector.  For each angle `φ` in
`[0, θ_g]` and each map `R'` that moves every unit vector at most `1e-9` from `R(n̄_g, φ) R(q̄_g)`,
every input cone holds for `R'` applied to the cone's normalized body vector, against its
normalized axis.  `R(q̄)` is the program's rotation formula on the normalized quaternion, which
equals `v ↦ q̄ v q̄*`, `R(n, φ)` is Rodrigues' formula, and the theorem depends only on `propext`,
`Classical.choice`, and `Quot.sound`.

The proof has five parts.  `validInput`'s norm tests give every node and cone the hypotheses of
the edge check: a component above 2 in magnitude makes the computed sum of squares at least about
4, so the test fails, and otherwise the test's rounding stays below `70 u`.  `relative` computes
each component within `13.04 u` of `±q_b q_a*`, so the rotation of its real value after
`R(q̄_a)` lies within `1.2e-14` of `R(q̄_b)`.  An invariant of `search` makes every segment an edge
that `edgeOk` accepted, on a path from the start to the goal: every node other than the start
with a finite cost, and every finalized node other than the start, has a finalized parent through
an accepted edge, and the parent chain of a finalized node reaches the start in fewer steps than
there are finalized nodes, which keeps the chain within the fuel of `pathLength`.  The output
angle `2 atan2 s w` lies within `1e-14` of the rotation angle of `rel`'s real value, from the
library's accuracy of `atan2` within two steps, and the output axis lies within `18.2 u` of its
axis, or, when the output axis is `+X`, the rotation is below `2e-149` rad.  These differences
displace a unit vector by at most `5e-14`, which the tube of `1.05e-9` covers.

The compiler's `compiled.plan.implements` states that the module's `plan` export returns `plan`
of its input or traps when an allocation finds no memory, so the theorem applies to every output
of status 1 that the export returns.  The theorem concerns the commanded rotations, and [the
premise theorem](#premises) relates them to a flown slew.

## NaN-freedom

[The NaN-freedom proof](NanFree.lean) `plan_finite` states that every floating-point value that
`plan` computes from an input that passes `validInput` is finite, and so not a NaN.  It lists the
values as the program's functions bind them: each `let` value, each operand of a comparison,
conversion, `min`, `max`, or `abs`, each divisor, each argument of a square root, and the
arguments and result of each call of `atan2`.  Every other operation lies inside one of these
expressions as a sum, difference, product, or negation, and its result is finite whenever the
expression's is.  The statement covers the static check of every node and the edge check,
relative quaternion, angle, duration, and output axis of every pair of nodes, and it depends only
on `propext`, `Classical.choice`, and `Quot.sound`.

The duration `slewTicks` takes the square root of `θ / a`, so the output angle `2 atan2 s w`
must not be negative.  The library's accuracy theorem for `atan2` allows a result two steps below
a tiny positive argument, so the proof follows the library's branches instead: for a positive
`s` and a `w` that is not negative, `atan2` returns `atan` of a quotient that is not negative, or
a positive constant, and `atan` keeps the sign of its argument.  The internal operations of the
library's `atan2` and `atan` lie outside the statement, and the statement concerns `plan` in
Lean: carrying it to the module's instructions needs a statement in Talos's semantics.

## Premises

[The premise theorem](Premise.lean) `plan_premise` relates a plan of status 1 to a flown slew.  It
measures the angle between two vectors with Mathlib's `InnerProductGeometry.angle`, the arccosine
of their inner product over the product of their lengths, which is `π/2` when either vector is
zero.  Let `φ` lie in `[0, θ_g]` for a segment `g`, let a map `A` move every unit vector by an
angle of at most `ε` from the commanded attitude `R(n̄_g, φ) R(q̄_g)`, and let cone `k` have a true
axis `u` within angle `d` of its normalized input axis `ū` and a true half-angle `α`.  For a
keep-out cone with `α + d + ε ≤ arccos c`, where `c` is the input cosine, the angle between `A b̄`
and `u` is at least `α`, and for a keep-in cone with `arccos c + d + ε ≤ α`, it is at most `α`.
The theorem depends only on `propext`, `Classical.choice`, and `Quot.sound`.

The statement concerns one instant, so the attitude, the axis, and the half-angle may change
during the slew.  If a keep-out cone's half-angle stays at most `α₀ + γ` for a nominal half-angle
`α₀`, an input cosine `c` with `arccos c ≥ α₀ + γ + d + ε` satisfies the hypothesis at every
instant, and a keep-in cone whose half-angle stays at least `α₀ − γ` needs
`arccos c ≤ α₀ − γ − d − ε`.  The hypotheses concern the real value of the input's float, so the
cosine of the enlarged half-angle, rounded down for a keep-out cone and up for a keep-in cone,
satisfies them.  The map `A` covers every difference between the flown and the commanded
attitudes, including control and knowledge errors, and the theorem assumes nothing else about it.

The proof applies `plan_safe` with the commanded attitude as `R'`, at distance 0 from itself.  The
commanded attitude preserves length, because `n̄_g` has length 1 and `R(q̄)` preserves length for
every `q`, so `b̄` maps to a unit vector, and the cone's bound on its cosine with `ū` bounds its
angle with `ū` through `arccos`, which is decreasing.  The triangle inequality for angles,
`InnerProductGeometry.angle_le_angle_add_angle`, holds for all vectors and adds `d` and `ε`.

## Tests

The tests follow the other verified examples.  [The
generator](../../tests/TestSupport/Slew/Cases.lean) draws the inputs from SplitMix64 with fixed
seeds and builds the geometry from rational parametrizations of angles, with no call to a platform
library.  Native Lean computes each expected
result, and `tests/verified/run.sh --cases slew` compares the module with it in Wasmtime, bit for
bit, with the host's input and the result as the only blocks left allocated after a call.  The
cases cover these classes:

- realistic plans with 0, 60, 200, and 500 waypoints, and variations of the limits;
- cones whose limit grazes a rotation's designed extremum, from `-1e-8` to `1e-8` away, the margin
  included;
- stationary points near the start and the end of a rotation, with `B` of both signs and within
  and beyond `eta`;
- rotations at both sides of the small-angle threshold, near and at `π`, and antipodal quaternions;
- cones of half-angles near 0° and 90°, and cones of 0° and 180°;
- vectors and quaternions just inside and just outside the norm tolerance;
- invalid inputs of every kind that `validInput` rejects;
- `atan2` on special values and on random arguments.

| Class | Plans | Status 1 | 0 | -1 | -2 | -3 |
|---|---:|---:|---:|---:|---:|---:|
| Realistic | 48 | 42 | 6 | 0 | 0 | 0 |
| Limits | 18 | 14 | 4 | 0 | 0 | 0 |
| Grazing | 240 | 83 | 157 | 0 | 0 | 0 |
| Stationary points | 336 | 168 | 0 | 84 | 84 | 0 |
| Angles near 0 and π | 114 | 72 | 22 | 0 | 20 | 0 |
| Extreme cones | 64 | 48 | 0 | 16 | 0 | 0 |
| Norms at the tolerance | 8 | 4 | 0 | 0 | 0 | 4 |
| Invalid inputs | 24 | 2 | 0 | 1 | 1 | 20 |

Before the safety theorem was proved, the generator also ran a sampled safety check, which
evaluated each cone along each segment of every plan of status 1 at 1,001 equally spaced angles
and found at least `1.23e-9` to spare.  `plan_safe` replaces that check: it covers every angle of
every segment and every input that passes `validInput`, and the generator no longer runs the
check.  `tests/TestSupport/Slew/CasesMain.lean` with the argument `--summary` prints the table's
counts.

`tests/slew/edges.sh`, which `tests/verified/run.sh` runs with the slew cases, compares the
module's `edgeOk` export with native Lean on 100,000 single-cone edges from [the edge
generator](../../tests/TestSupport/Slew/Edges.lean), all in one host session.  The edges are
random rotations, cones that graze a rotation's designed extremum within `1e-8`, stationary
points at either end with `B` within and beyond `eta`, and relative quaternions with vector
lengths near 0, near the small-angle threshold, and near 1.  All 100,000 results agree, 34,213 of
them acceptances, and the session allocates no block beyond its input.

The generator takes 14 s, the edge test 9 s, and the whole run of `tests/verified/run.sh --cases
slew` 80 s.  A plan of 500 waypoints takes at most 51 ms in the host, of which about 20 ms is the
start of the host and the compilation of the module.

## Theorems to prove

The journal states each theorem and the order of the work.

- **Compilation and execution:** the generated `compiled.plan.implements` and `trapFree` hold, and
  [the compilation section](#compilation) states the constant allocation bound, `plan_bound`, and
  `slew_trapFree`.
- **NaN-freedom:** no floating-point operation in the evaluation of `plan` on validated input has
  a NaN operand or result.  [The NaN-freedom section](#nan-freedom) states the proved theorem,
  `plan_finite`, for the evaluation in Lean.
- **Safety:** every commanded rotation of a plan, and every attitude within `1e-9` of it, satisfies
  every input cone, as a statement about real numbers.  [The safety section](#safety) states the
  proved theorem, `plan_safe`.
- **Premises:** if the flown attitude stays within `ε` of the commanded one, each constraint axis
  within `d` of its planning value, and each nominal half-angle grows by at most `γ`, then a plan
  computed with half-angles enlarged by `ε + d + γ` keeps the nominal limits along the flown
  slew.  [The premises section](#premises) states the proved theorem, `plan_premise`.
- **Optimality:** no path in the graph that the program's own checks define costs less than the
  plan.
- **File:** the written `slew.wasm` holds the encoding of `compiled.module`.
