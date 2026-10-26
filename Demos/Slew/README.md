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
The compiler's generated theorems state that the module computes `plan`, and [the soundness
section](#soundness-of-the-checks) states the theorems that the program's edge check and static
check accept only rotations and attitudes that the cones allow.  [The test section](#tests)
describes the cases, and [the theorem section](#theorems-to-prove) lists the theorems that remain.

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

The program imports only the dialect modules and `Library.Numerics.Float64.Atan.Program`, which
build from Lean's core library.  The representations need `LeanExe.Pipeline`, which depends on
Talos's CodeLib, and the compilation and the proofs need Mathlib.  `Demos.lean` imports the
program, the representations, and the proofs, and `Demos/Verified.lean` imports the compilation.

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
  `compiled.output.bound` for validated input, and the closed form remains to be derived.  `round`
  and `relax` take the search state, a record with array fields, as a parameter, and the verified
  compiler borrows every record parameter, so their updates copy arrays of up to 1,026 words in each
  of up to 1,027 rounds, and the bound counts each copy without reuse.

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
value it needs from the error bounds.  It does not exclude a NaN `s`, which would require
`S² ≤ 5 · 2⁻¹⁰⁷⁵`, and such an `s` makes a keep-in check fail and leaves a keep-out check the
bound at the start, which covers a rotation that small.

The theorems take the properties of the inputs as hypotheses, and the rotation they describe is
that of `rel`'s real value, which differs from the exact rotation between the normalized
attitudes by the rounding of `relative`.  The derivation of the hypotheses from `validInput` and
`relative`, the bound on that difference, and the path structure of the search belong to the
safety theorem.  Until that theorem exists, the sampled safety check below tests whole plans.

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

| Class | Plans | Status 1 | 0 | -1 | -2 | -3 | Least sampled spare |
|---|---:|---:|---:|---:|---:|---:|---|
| Realistic | 48 | 42 | 6 | 0 | 0 | 0 | 1.7e-3 |
| Limits | 18 | 14 | 4 | 0 | 0 | 0 | 3.3e-2 |
| Grazing | 240 | 83 | 157 | 0 | 0 | 0 | 1.23e-9 |
| Stationary points | 336 | 168 | 0 | 84 | 84 | 0 | 2.0e-9 |
| Angles near 0 and π | 114 | 72 | 22 | 0 | 20 | 0 | 1.01e-8 |
| Extreme cones | 64 | 48 | 0 | 16 | 0 | 0 | 3.4e-4 |
| Norms at the tolerance | 8 | 4 | 0 | 0 | 0 | 4 | 0.13 |
| Invalid inputs | 24 | 2 | 0 | 1 | 1 | 20 | 1.9e-2 |

The generator also runs a sampled safety check, a test that the safety theorem is to replace.  For
every plan of status 1 it evaluates each cone along each segment at 1,001 equally spaced angles,
with Rodrigues' formula and the library's `Trig.sin` and `Trig.cos`, and it fails when a cone has
less than `1e-9` to spare.  Samples `θ/1000` apart can miss an interior extremum by up to about
`10⁻⁶` in cosine on the longest rotations, so the check does not resolve the grazing cases at the
scale of the margin, which the theorem will.  `tests/TestSupport/Slew/CasesMain.lean` with the
argument `--summary` prints the table's counts and spares.

The generator takes 18 s, and the whole run of `tests/verified/run.sh --cases slew` 74 s.  A plan
of 500 waypoints takes at most 51 ms in the host, of which about 20 ms is the start of the host and
the compilation of the module.

## Theorems to prove

The journal states each theorem and the order of the work.

- **Compilation and execution:** the generated `compiled.plan.implements` and `trapFree` hold, and
  a constant allocation bound for validated input remains to be derived from `bound_eq`.
- **NaN-freedom:** no floating-point operation in the evaluation of `plan` on validated input has
  a NaN operand or result.
- **Safety:** every commanded rotation of a plan, and every attitude within `1e-9` of it, satisfies
  every input cone, as a statement about real numbers.  The soundness of the checks covers one
  rotation and one attitude.
- **Premises:** if the flown attitude stays within `ε` of the commanded one, each constraint axis
  within `d` of its planning value, and each nominal half-angle grows by at most `g`, then a plan
  computed with half-angles enlarged by `ε + d + g` keeps the nominal limits along the flown
  slew.
- **Optimality:** no path in the graph that the program's own checks define costs less than the
  plan.
- **File:** the written `slew.wasm` holds the encoding of `compiled.module`.
