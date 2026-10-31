# Slew: constraint-checked attitude slews

[The program](Program.lean) plans a slew of a spacecraft from a start attitude to a goal attitude
as a sequence of rest-to-rest eigenaxis rotations through a set of waypoint attitudes.  Every
rotation it returns keeps given body vectors outside keep-out cones and inside keep-in cones, and
the sequence has the least total duration, in whole milliseconds, among the walks of the graph that
the program's checks define.  The program is written in the verified compiler's dialect, takes one
array of binary64 values, and returns one.

`verified_compile` compiles the program, with the library's `atan` and `atan2`, into a module of
26,362 bytes.  In Wasmtime, the module's `plan` export agrees with native Lean, bit for bit, on 852
generated inputs, its `atan2` export on 1,225 calls, and its `edgeOk` export on 100,000 edges.
[The theorems](#theorems) state that every plan keeps every cone along its commanded rotations,
that it keeps the true cones along a flown slew when the input cones allow for the errors of the
flown attitude and of the cone axes, that the evaluation in Lean produces no NaN, that a plan is a
least-cost walk of the graph, that a call allocates at most 68,020,488 bytes, and that the written
file holds the module.  [The limits](#limits-of-the-theorems) state what the theorems leave out.

## The planning problem

An attitude is a unit quaternion `q = [w, x, y, z]` that maps body coordinates to inertial
coordinates by the rotation `R(q) v = q v q*`.  The program computes `R(q) v` as `v + w t + p × t`,
where `p = [x, y, z]` and `t = 2 p × v`, which equals `q v q*` for a unit quaternion, and the
theorems apply this formula in exact arithmetic to the normalized quaternion `q̄ = q/|q|`.  For a
vector `v`, `v̄ = v/|v|` is its normalization, and `R(n, φ)` is the rotation by the angle `φ` about
the unit axis `n`, which Rodrigues' formula gives.

A cone names a body vector `b`, an inertial axis `u`, the cosine `c` of its half-angle, and a kind.
A keep-out cone requires `u · R(q) b ≤ c`, which keeps the body vector at least the half-angle away
from the axis, and a keep-in cone requires `u · R(q) b ≥ c`.  The theorems state these conditions
for the normalized vectors `b̄` and `ū` and the attitude `R(q̄)`.  The distance between two maps of
vectors, such as two attitudes, is the largest displacement of a unit vector from one to the other,
so a tube of `ρ` around an attitude contains every map that moves no unit vector farther than `ρ`
from it.

A segment is an eigenaxis rotation: a rotation by an angle `θ` in `[0, π]` about an axis `n` fixed
in inertial coordinates.  It is a rest-to-rest rotation, which starts and ends with zero angular
rate, under a rate limit `ω` and an acceleration limit `a`.  Its duration is
`T(θ) = θ/ω + ω/a` when `θ ≥ ω²/a`, when it reaches the rate limit and coasts, and
`T(θ) = 2 √(θ/a)` otherwise.  A settling time `t_s`, a fixed wait, follows each segment.  The
attitudes that a segment visits are `R(n, φ) R(q)` for `φ` from 0 to `θ`, whatever its time profile.

The graph's nodes are the start, the goal, and the waypoints, numbered 0 for the start, 1 for the
goal, and `2 + i` for waypoint `i`.  A directed edge leads from node `u` to node `v` when each end
is the start, the goal, or a waypoint that passes the static check, the program's test of one
attitude against every cone, `v ≠ u`, the computed angle of the rotation from `u` to `v` is not
greater than `maxEdge` or the edge leads from the start to the goal, and the edge check, the
program's test of a whole rotation against every cone, accepts the rotation.  The edge costs
`⌈1000 T(θ)⌉ + ⌈1000 t_s⌉` milliseconds, computed in binary64 from the computed angle, and the
planner returns a walk from the start to the goal of least total cost.

## Interface

```text
input   index        value                                        validInput requires
        0            version                                      2
        1            nb, the number of body vectors               a whole number from 1 to 8
        2            nc, the number of cones                      a whole number from 0 to 16
        3            nw, the number of waypoints                  a whole number from 0 to 1,024
        4            rate limit ω (rad/s)                         from 1e-5 to 1
        5            acceleration limit a (rad/s²)                from 1e-7 to 1
        6            settling time t_s (s)                        from 0 to 3,600
        7            maxEdge (rad)                                from 0 to 4
        8 to 11      start quaternion, node 0                     squared norm within 1e-12 of 1
        12 to 15     goal quaternion, node 1                      squared norm within 1e-12 of 1
        16           nb body vectors, 3 values each               squared norm within 1e-12 of 1
        16 + 3 nb    nc cones, 6 values each:
                       body index                                 a whole number below nb
                       axis, 3 values                             squared norm within 1e-12 of 1
                       cosine of the half-angle                   from -1 to 1
                       kind                                       0 keep-out, 1 keep-in
        16 + 3 nb    nw waypoint quaternions, 4 values each,      squared norm within 1e-12 of 1
          + 6 nc     waypoint i is node 2 + i
        The input has exactly 16 + 3 nb + 6 nc + 4 nw values, and every value is finite.

output for status 1, with K segments, 8 + 11 K values:
        header (4)            1, K, total cost (ms), number of finalized nodes
        segment g (11 each)   quaternion of its first node (4), axis (3), angle (rad), cost (ms),
                              first node, second node
        goal quaternion (4)

output for status 0, -1, -2, or -3, 4 values:
        status, 0, 0, number of finalized nodes for status 0 and 0 otherwise

status   1   plan found
         0   no walk from the start to the goal in the graph
        -1   the start violates a cone
        -2   the goal violates a cone
        -3   the input fails validInput
```

Each segment's quaternion and the goal quaternion are copied from the input, bit for bit.  For the
relative quaternion `[w, v]` of a segment, the rotation from its first node to its second, with
`w ≥ 0`, the axis is the computed `v/|v|`, or `+X` when the computed `|v|` is below `1e-150`, and
the angle is `2 atan2(|v|, w)` with the library's `atan2`.  Costs and node numbers are whole numbers
held as binary64 values, which are exact below `2^53`, and every cost of a validated input lies far
below that.  The module exports every function of the compilation, and the tests call `plan`,
`atan2`, and `edgeOk`.

## Program and checks

The program uses flat arrays, counted loops through `LeanExe.loop`, `LeanExe.build`, and
`LeanExe.repeatWhile`, ties to the lowest index, and replacement only on strict improvement, as the
[drone planner](../Drone/README.md) does.  `validInput` rejects every input outside the interface
with status -3.  The static check, `attitudeOk q slack`, computes `f = u · R(q) b` in binary64 on
the given, unnormalized vectors for each cone and passes when `f ≤ c - margin - slack` for a
keep-out cone and `f ≥ c + margin + slack` for a keep-in cone.  The start and the goal get status
-1 or -2 when they fail it without slack, and a waypoint that fails it is left out of the graph,
so the admitted nodes are the start, the goal, and the waypoints that pass it.

`search` runs Dijkstra's algorithm on arrays.  A node is finalized when the search selects it as the
open node of least cost, and its cost and parent then stay fixed.  For each node that it finalizes,
`relax` computes, for every other open admitted node, the relative quaternion of the rotation
(`relative`), its angle (`angleOf`), and its cost (`slewTicks` and the settling time).  It calls
the edge check, `edgeOk`, only when the candidate cost would strictly improve the target's cost, in
an `if` of its own, since the compiled code evaluates both operands of `&&`.  The search stops when
it finalizes the goal or when no open admitted node has a finite cost, and `output` follows the
parent chain from the goal and writes the segments.

During a rotation by `φ` about the unit axis `n`, the cosine between the inertial image
`v₀ = R(q_a) b` of a body vector at the start attitude `q_a` and a cone axis `u` is
`f(φ) = A cos φ + B sin φ + C`, with `A = u·v₀ - (n·u)(n·v₀)`, `B = u·(n × v₀)`, and
`C = (n·u)(n·v₀)`.  On `[0, θ]` with `θ ≤ π`, `f` has an interior maximum only when `B > 0` and
`f′(θ) = B cos θ - A sin θ < 0`, of value `C + √(A² + B²)`, and an interior minimum only when
`B < 0` and `f′(θ) > 0`, of value `C - √(A² + B²)`.  The relative quaternion `[w, v]` with `w ≥ 0`
gives `cos θ = w² - s²` and `sin θ = 2ws` for `s = |v|`, so the check needs no trigonometric
function.

The edge check compares the endpoint values, and the stationary value unless a computed test
excludes it by more than `eta = 1e-12`, with the cone's cosine tightened by `margin`, the double
nearest `1.1e-9`.  The margin was chosen as a tube of `1e-9` around the commanded rotation plus a
rounding allowance of `1e-10`, and [the soundness proof](#soundness-of-the-checks) spends it as a
tube of `ρ = 1.05e-9` and rounding errors of at most `3.63e-11`.  Below `s = 1e-7`, the computed
axis `v/s` loses relative accuracy, and the check tests the start attitude with `2.125 · s` more
slack, since the rotation angle is about `2s` and no unit vector moves farther than the rotation
angle.  Each ceiling of a cost is built from the saturating `Float.toUInt64`, because the verified
compiler has no rule for `Float.ceil`.  An unreached node costs `2^62`, and no path cost comes near
it, since `edge_cost_le` bounds the cost of an edge by `2^34` ms and a walk that the search returns
has at most 1,025 edges.

## Theorems

Every theorem in the table depends only on the axioms `propext`, `Classical.choice`, and
`Quot.sound`, which [the axiom audit](../../tests/slew/Axioms.lean) and the file check confirm.
For an input `xs`, status 1 means `(plan xs)[0] = 1`, and `q_g`, `n_g`, and `θ_g` are the
quaternion, axis, and angle of segment `g` of the output, with the goal quaternion as `q_K`.
The real value of a float is the real number that it represents, and the real value of a
quaternion of floats, such as the relative quaternion `rel` of `edgeOk_sound`, is the quaternion of
the real values of its components.
[The verified compiler manual](../../docs/verified-manual.md#the-implements-and-trapfree-theorems)
defines the terms of the generated theorems.  A heap's `top` is the end of the memory that the
allocator has handed out, the memory cap is the largest number of 64 KiB pages that the store
allows, and the module declares a maximum of 65,535 pages.  The argument of `plan` has the type
`Array Float` rather than `Moved`, which would mark an argument that the call consumes, so `plan`
borrows its input, and entry 28 is the module's function for `plan`.  `segValue xs d st a b f` is
the value that `segmentField` writes at field `f` of the segment from node `a` to node `b`.

| Theorem | File | Hypotheses | Conclusion |
|---|---|---|---|
| `compiled.plan.implements` | [Compilation](Verified.lean) | Heap with the allocator invariant, a memory cap of at most 65,535 pages, and argument words that represent the borrowed `xs` | Entry 28, the `plan` export, returns words that represent `plan xs`, or traps at `unreachable`, which an allocation that finds no memory can cause. |
| `compiled.plan.trapFree` | [Compilation](Verified.lean) | Those of `implements`, and room for `top` to rise by `compiled.plan.bound xs` bytes within the cap | Entry 28 returns words that represent `plan xs` without a trap, and `top` rises by at most `compiled.plan.bound xs`. |
| `compiled.bytes` | [Compilation](Verified.lean) | None | `encode compiled.module` succeeds with bytes that decode to `compiled.module`, and the `implements` theorem of every function holds. |
| `edgeOk_sound` | [Soundness proof](Check.lean) | Attitude `q_a` with finite components and a squared norm within `3e-12` of 1, a relative quaternion `rel` with finite components, `w ≥ 0`, and a squared norm within `1e-11` of 1, cones whose body vectors and axes are finite with squared norms within `3e-12` of 1 and whose cosines are finite and in `[-1, 1]`, and `edgeOk` accepting `rel` from `q_a` | For every cone, every `φ` from 0 to the rotation angle of `rel`'s real value, and every vector within `1.05e-9` of `R(n, φ) R(q̄_a) b̄`, where `n` is the normalized vector part of `rel`'s real value, the vector satisfies the cone against `ū`. |
| `attitudeOk_sound` | [Soundness proof](Check.lean) | Attitude `q` and cones as for `edgeOk_sound`, and `attitudeOk` accepting `q` without slack | For every cone, every vector within `1.05e-9` of `R(q̄) b̄` satisfies the cone against `ū`. |
| `plan_safe` | [Safety theorem](Safety.lean) | Status 1 | For some `K ≥ 1`, the output has `8 + 11K` values and starts and ends with the input's start and goal quaternions, bit for bit.  For each segment `g`, `n̄_g` has length 1, `R(n̄_g, θ_g) R(q̄_g)` lies within `1e-9` of `R(q̄_{g+1})`, and for every `φ` in `[0, θ_g]` and every map within `1e-9` of `R(n̄_g, φ) R(q̄_g)`, the map's image of `b̄` satisfies every cone against `ū`. |
| `plan_finite` | [NaN-freedom](NanFree.lean) | `validInput xs` | Values that `validInput` computes, the conversion of every word to a float, the values of the static check of every node without slack, and, for every pair of nodes, the values of the edge check, the relative quaternion, the angle and the arguments and result of its `atan2` call, the duration, and the output axis are finite. |
| `plan_premise` | [Premise theorem](Premise.lean) | Status 1 with `K` segments, `g < K`, `φ` in `[0, θ_g]`, a map `F` that moves every unit vector by an angle of at most `ε` from `R(n̄_g, φ) R(q̄_g)`, a cone with a true axis `u` within angle `d` of `ū`, and a real `α` | For a keep-out cone with `α + d + ε ≤ arccos c`, the angle between `F b̄` and `u` is at least `α`.  For a keep-in cone with `arccos c + d + ε ≤ α`, it is at most `α`. |
| `edge_cost_le` | [Edge cost](Cost.lean) | `validInput xs`, and nodes `a` and `b` below `nw + 2` | Cost of the edge from `a` to `b`, `⌈1000 T(θ)⌉ + ⌈1000 t_s⌉` as computed, is at most `2^34` ms. |
| `plan_optimal` | [Optimality](Optimal.lean) | `validInput xs`, and the start and the goal pass the static check without slack | When the graph has a walk from the start to the goal, the output has status 1, its segments join the nodes of such a walk, each field as `segValue` gives it, its header reports the walk's cost, and no walk from the start to the goal costs less.  Otherwise the output has status 0. |
| `plan_bound` | [Allocation bound](Bound.lean) | None | `compiled.plan.bound xs ≤ 68,020,488`. |
| `slew_trapFree` | [Allocation bound](Bound.lean) | Those of `implements`, and room for `top` to rise by 68,020,488 bytes within the cap | Entry 28 returns words that represent `plan xs` without a trap, and `top` rises by at most 68,020,488 bytes. |
| `slew_file` | [File theorems](File.lean) | `build/verified/slew.wasm` as written | `encode compiled.module` equals the file's bytes. |
| `slew_file_decode` | [File theorems](File.lean) | Same file | `build/verified/slew.wasm` decodes to `compiled.module`. |

## Soundness of the checks

The soundness proof bounds each rounding error against the program's formulas in exact arithmetic
on the given, unnormalized inputs, which keeps the errors of the stationary-point tests below
`eta`.  The normalization enters once, in the final bound.  For a rotation past the small-angle
threshold, with `μ = 2⁻⁵³`, the margin covers these parts.

| Part | Bound |
|---|---|
| Rounding of `f₀`, `f₁`, the stationary value, and the tightened cosine `c ∓ margin` | `2300 μ`, about `2.6e-13` |
| Use of `w² - s²` and `2ws`, which equal `cos θ` and `sin θ` times `w² + s²`, in place of `cos θ` and `sin θ` | `2.3e-11` |
| Normalization of the attitude, the body vector, and the cone axis | `1.3e-11` |
| Tube `ρ` | `1.05e-9` |
| Total | about `1.0863e-9`, about `1.4e-11` below `margin` |

Below `s = 1e-7`, the slack `2.125 · s` exceeds the change `2.0003 S` of the cosine along the
rotation, where `S` is the real length of `rel`'s vector part.  The proof follows the program's
decisions through NaN results: Lean's `max a b` returns `a` when `b` is a NaN, so a keep-out check
that drops a NaN value still bounds the start, and the proof derives the finiteness of every other
value it needs from the error bounds.  It also covers a NaN `s`, which a negative computed radicand
would give and which requires `S² ≤ 5 · 2⁻¹⁰⁷⁵`, and [the output proofs](Angle.lean) show that the
computed radicand of every pair of nodes of a validated input is not negative, so `s` is finite.
The rotation that the theorems describe is that of `rel`'s real value, which differs from the exact
rotation between the normalized attitudes by the rounding of `relative`, and `plan_safe` bounds
that difference.

## Safety

`plan_safe`'s only hypothesis is status 1, which `plan` returns only for an input that passes
`validInput` and whose start and goal pass the static check.
`validInput`'s norm tests give every node and cone the hypotheses of `edgeOk_sound`: a component
above 2 in magnitude makes the computed sum of squares at least about 4, so the test fails, and
otherwise the test's rounding stays below `70 μ`.  `relative` computes each component within
`13.04 μ` of `±q_b q_a*`, so the rotation of its real value after `R(q̄_a)` lies within `1.2e-14`
of `R(q̄_b)`.  An invariant of `search` makes every segment an edge that `edgeOk` accepted, on a
walk from the start to the goal: every node other than the start with a finite cost, and every
finalized node other than the start, has a finalized parent through an accepted edge, and the
parent chain of a finalized node reaches the start in fewer steps than there are finalized nodes,
which keeps the chain within the fuel of `pathLength`.

The output angle `2 atan2(s, w)` lies within `1e-14` of the rotation angle of `rel`'s real value,
from the library's accuracy of `atan2` within two steps, and the output axis lies within `18.2 μ` of
its axis, or, when the output axis is `+X`, the rotation is below `2e-149` rad.  These differences
move a unit vector by at most `5e-14`.  `plan_safe` keeps a tube of `1e-9` and spends at most
`5e-14` of the remaining `5e-11` of `ρ` on them.

## NaN-freedom

`plan_finite` lists the values as the program's functions bind them: each `let` value, each operand
of a comparison, conversion, `min`, `max`, or `abs`, each divisor, each argument of a square root,
and the arguments and result of each call of `atan2`.  It omits `m1` and `m2` of the edge check,
which are maxima or minima of the listed values `f₀`, `f₁`, and `C ± √(A² + B²)` and which the
cone's decision compares with the tightened cosine.  Every other operation lies inside a listed
expression as a sum, difference, product, or negation, and its result is finite whenever the
expression's is.  The statement covers every node and every pair of nodes, whether or not the
search evaluates them.

The duration takes the square root of `θ/a`, so the output angle `2 atan2(s, w)` must not be
negative.  The library's accuracy theorem for `atan2` allows a result two steps below a tiny
positive argument, so the proof follows the library's branches instead: for a positive `s` and a
`w` that is not negative, `atan2` returns `atan` of a quotient that is not negative, or a positive
constant, and `atan` keeps the sign of its argument.  The internal operations of the library's
`atan2` and `atan` lie outside the statement.

## Premises

`plan_premise` relates a plan of status 1 to a flown slew.  It measures the angle between two
vectors with Mathlib's `InnerProductGeometry.angle`, the arccosine of their inner product over the
product of their lengths, which is `π/2` when either vector is zero.  The map `F`, named `A` in the
Lean statement, stands for the flown attitude at one instant and covers every difference between it
and the commanded attitude, including control and knowledge errors.  The theorem assumes nothing
else about `F`.

The statement concerns one instant, so the attitude, the axis, and the half-angle may change during
the slew.  If a keep-out cone's half-angle stays at most `α₀ + γ` for a nominal half-angle `α₀`, an
input cosine `c` with `arccos c ≥ α₀ + γ + d + ε` satisfies the hypothesis at every instant.  If a
keep-in cone's half-angle stays at least `α₀ - γ`, an input cosine with
`arccos c ≤ α₀ - γ - d - ε` does.  The hypotheses concern the real value of the input's float, so
the cosine of the adjusted half-angle, rounded down for a keep-out cone and up for a keep-in cone,
satisfies them.

The proof applies `plan_safe` with the commanded attitude as the map, at distance 0 from itself.
The commanded attitude preserves length, because `n̄_g` has length 1 and `R(q̄)` preserves length
for every `q`, so `b̄` maps to a unit vector, and the cone's bound on its cosine with `ū` bounds its
angle with `ū` through `arccos`, which is decreasing.  The triangle inequality for angles,
`InnerProductGeometry.angle_le_angle_add_angle`, holds for all vectors and adds `d` and `ε`.

## Optimality

`plan_optimal` concerns an input that passes `validInput` and whose start and goal pass the static
check, so that the output's status is 1 or 0.  Its graph is the directed graph of
[the planning problem](#the-planning-problem), with the program's own predicates and costs, and a
walk may repeat nodes, which changes no least cost, since no cost is negative.  The proof is the
correctness of Dijkstra's algorithm with integer costs, stated as an invariant of every state of
the search.  A finalized node holds the least cost of a walk to it, a node with a finite cost holds
the cost of the walk through its parent, and every node not yet finalized holds at most the cost
through each finalized node with an edge to it.

`relax` checks an edge only when its candidate cost improves the target, and a candidate that does
not improve the target already satisfies the last property, so skipping the check changes nothing.
[The edge cost](Cost.lean) `edge_cost_le` bounds the cost of every edge by `2^34` ms, from the
limits that `validInput` checks and the truncation of `Float.toUInt64`, so no sum of costs wraps
and no finite cost reaches the sentinel `infinity = 2^62`.  Each round that does not stop finalizes
one more node, so the `n + 1` rounds of `search` end with the goal finalized or with every open
admitted node unreached.

## Limits of the theorems

The theorems rest on the verified compiler's [trusted
base](../../docs/verified-manual.md#trusted-base): Lean's kernel with the three axioms, the
semantics of WebAssembly of
[Talos](../../docs/trusted-base.md#v-webassembly-modules-of-the-verified-compiler), an
interpreter written in Lean, the binary decoder, the module emitter, and, for the file theorems,
the elaborator `binary_file%`, which reads the written file.  The manual's section [outside the
proofs](../../docs/verified-manual.md#outside-the-proofs) lists what those semantics leave out,
such as engine instantiation and the call depth of a real engine.  `plan_safe`, `plan_premise`,
and `plan_optimal` concern `plan` in Lean, and `compiled.plan.implements` carries them to every
output that the module's `plan` export returns.  `plan_finite` concerns the evaluation in Lean and
states nothing about the module's instructions.

No theorem concerns time or dynamics, so `T(θ)` is a cost model, and the theorems concern the
attitudes that the commanded rotations pass through.  The checks are conservative: the margin, the
inclusion of a stationary value that a test does not exclude by more than `eta`, the slack below
the small-angle threshold, and `maxEdge` can reject safe rotations, so status 0, -1, or -2 does not
prove that no safe slew exists.  `plan_optimal` compares a plan only with the walks of the graph,
through the given waypoints, over the edges that the edge check accepts, with the computed costs.
When several walks share the least cost, the ties to the lowest index and the replacement only on
strict improvement choose the one returned, and no theorem states which.

`plan_bound` counts every block that a call allocates as new memory, at `8n + 56` bytes for a
block of `n` words, and ignores the reuse of freed blocks.  Its 68,020,488 bytes come to 1,038
pages of 64 KiB, far below the module's maximum of 65,535 pages, and the peak use of a call is not
measured.  No theorem concerns the header's count of finalized nodes.

## Building and testing

The commands run from the repository root.  They require Lean through Elan at the version in
[the toolchain file](../../lean-toolchain), `wasm-tools`, and the Wasmtime host that
`tools/build-wasmtime-host.sh` builds after `tools/download-wasmtime.sh`, as
[the repository's commands](../../README.md#commands) describe.  The first build covers every
module of the planner except the file theorems, which read the written module.

```sh
tools/download-wasmtime.sh
tools/build-wasmtime-host.sh
tools/leanrun --timeout 60m lake build Demos.Slew.Optimal Demos.Slew.Premise Demos.Slew.Bound
tests/verified/run.sh --cases slew
tools/leanrun --timeout 10m lake env lean Demos/Slew/File.lean
tools/leanrun --timeout 30m lake build TestSupport.Slew.CasesMain
tools/leanrun --timeout 10m lake env lean --run tests/TestSupport/Slew/CasesMain.lean --summary
```

`tests/verified/run.sh --cases slew` writes and validates `build/verified/slew.wasm`, runs
[the edge test](../../tests/slew/edges.sh), runs [the axiom audit](../../tests/slew/Axioms.lean),
which fails on any axiom other than the three, checks the file theorems, and compares the module
with native Lean on the generated cases.  The full `tests/verified/run.sh` runs the same steps and
checks the file theorems in its loop over the written modules.  Among Lake's build messages, a
passing run of `--cases slew` prints these lines.

```text
random: 40000 edges, 13866 accepted
grazing: 30000 edges, 7447 accepted
stationary: 15000 edges, 7933 accepted
angles: 15000 edges, 4967 accepted
slew edges: 100000 edges agree with native Lean, 1 allocations, 1 frees
Slew axiom check passed for 12 theorems
slew: slew.wasm holds the module of Demos.Slew.Verified, with the permitted axioms
native Lean: 0 accesses past the end and 0 insertIdx! past the end, as the cases expect
verified: passed 2077 failed 0
```

`Demos/Slew/File.lean` prints the axiom reports of `slew_file` and `slew_file_decode`, and
`CasesMain.lean --summary` prints the count of each class's statuses, as the table of
[the tests](#tests) gives them.  In runs on an aarch64 Linux machine with the proof modules
built, the generator took 14 s, the edge test 9 s, and the whole of
`tests/verified/run.sh --cases slew` 92 s.  In the host, a call took at most 51 ms for a plan of 500
waypoints and 18 to 28 ms for a call of `atan2`, which measures the start of the host and the
compilation of the module.  These times come from single runs and vary by machine.

## Tests

[The generator](../../tests/TestSupport/Slew/Cases.lean) draws the inputs from SplitMix64 with fixed
seeds.  It builds angles from rational parametrizations, normalizes vectors and quaternions with
`Float.sqrt`, which is correctly rounded, and takes the cosines of the realistic cones from the
repository's `Trig.cos`, so the inputs are the same on every host.  Native Lean computes each
expected result, and the comparison is bit for bit, with the host's input and the result as the only
blocks left allocated after a call.

| Class | Inputs | Plans | 1 | 0 | -1 | -2 | -3 |
|---|---|---:|---:|---:|---:|---:|---:|
| Realistic | Plans with 0, 60, 200, and 500 waypoints | 48 | 42 | 6 | 0 | 0 | 0 |
| Limits | Variations of the rate, acceleration, settling, and edge limits | 18 | 14 | 4 | 0 | 0 | 0 |
| Grazing | Cones whose cosine differs from the designed extremum of the cosine along a rotation by ten offsets from `-1e-8` to `1e-8`, `±margin` among them | 240 | 83 | 157 | 0 | 0 | 0 |
| Stationary points | Stationary points near the start and the end of a rotation, with `B` of both signs and within and beyond `eta` | 336 | 168 | 0 | 84 | 84 | 0 |
| Angles near 0 and π | Rotations on both sides of the small-angle threshold, near and at `π`, and antipodal quaternions | 114 | 72 | 22 | 0 | 20 | 0 |
| Extreme cones | Cones of half-angle `1e-6` rad on and beside a rotation's path, of 90°, and of 0° and 180° | 64 | 48 | 0 | 16 | 0 | 0 |
| Norms at the tolerance | Body vector and start quaternion with squared norms just inside and just outside the tolerance | 8 | 4 | 0 | 0 | 0 | 4 |
| Invalid inputs | Inputs that fail `validInput`, and a start and a goal that violate a cone | 24 | 2 | 0 | 1 | 1 | 20 |

The invalid inputs fail the tests of the minimum length of 16 values, the version, a count of
bodies of 0 or not a whole number, a count of cones above 16, a count of waypoints above 1,024,
finiteness, the lower rate limit, the upper acceleration limit, the lower settling time, the upper
`maxEdge`, the start's norm, a cone's body index, cosine, and kind, and the length's agreement with
the counts.  The cases do not exercise the tests of a count of bodies above 8, of counts of cones
and waypoints that are not whole numbers, of the upper rate limit, the lower acceleration limit,
the upper settling time, the lower `maxEdge`, the goal's norm, a waypoint's norm, a cone axis's
norm, and a cosine below -1.  The cases also call the `atan2` export on all 225 pairs of 15
special values and on 1,000 random arguments.

[The edge test](../../tests/slew/edges.sh) compares the module's `edgeOk` export with native Lean
on 100,000 single-cone edges from [the edge generator](../../tests/TestSupport/Slew/Edges.lean), all
in one session of the host, the program in `build/tools/leanexe-wasmtime-host` that calls a
module's exports through Wasmtime.  The edges are 40,000 random rotations, 30,000 cones that graze a
rotation's designed extremum within `1e-8`, 15,000 stationary points at either end with `B` within
and beyond `eta`, and 15,000 relative quaternions with vector lengths near 0, near the small-angle
threshold, and near 1.  All 100,000 results agree, 34,213 of them acceptances, and the test checks
that the session frees every block it allocates.  In the recorded run, the session's only block was
its input.

## Files

| File | Contents |
|---|---|
| [Program](Program.lean) | Planner in the dialect |
| [Representations](Flat.lean) | `Flat` instances for `V3`, `Q4`, `Dims`, and `Search` |
| [Compilation](Verified.lean) | `verified_compile compiled := [atan, atan2, …, plan]` |
| [Specification](Spec.lean) | Real vectors and quaternions, Rodrigues' rotation, rotation angle, and cone predicate |
| [Arc lemmas](Arc.lean) | Sinusoid form of the cosine along a rotation, endpoint lemma, and vector inequalities |
| [Binary64 facts](Rounding.lean) | Real values of floats, comparisons, constants of the program, and bounded approximation `Bnd` |
| [Vector errors](Error.lean) | Rounding errors of dot and cross products and of the rotation formula |
| [Axis and angle](Axis.lean) | Rounding errors of `s`, axis `v/s`, `w² - s²`, and `2ws` |
| [Normalization](Normalize.lean) | Difference between the cosines of the normalized and the given inputs |
| [Cone values](Cone.lean) | Rounding errors of `f₀`, `A`, `B`, `C`, `f₁`, and `f′(θ)` |
| [Amplitude](Hypot.lean) | Rounding error of `√(A² + B²)` |
| [Decisions](Decide.lean) | Comparisons, NaN propagation, and bounds that a decision gives over the rotation |
| [Soundness proof](Check.lean) | `edgeOk_sound` and `attitudeOk_sound` |
| [Rotations](Rotation.lean) | Quaternion products and actions, their composition and distances, and Rodrigues' rotation as an action |
| [Relative quaternion](Relative.lean) | `GoodRel` for `relative` and distance of its rotation from the exact one |
| [Input](Valid.lean) | `GoodQ` for every node and `ConeGood` for every cone of a validated input |
| [Search](Search.lean) | Invariant of `search`, segments of a plan as accepted edges, and bound on `pathLength` |
| [Output proofs](Angle.lean) | Axis and angle of the output against those of the relative quaternion |
| [Safety theorem](Safety.lean) | `plan_safe` |
| [NaN-freedom](NanFree.lean) | `plan_finite` |
| [Premise theorem](Premise.lean) | `plan_premise` |
| [Edge cost](Cost.lean) | `edge_cost_le` |
| [Optimality](Optimal.lean) | `plan_optimal` |
| [Allocation bound](Bound.lean) | `plan_bound` and `slew_trapFree` |
| [File theorems](File.lean) | `slew_file` and `slew_file_decode` |

The program imports only the dialect modules and `Library.Numerics.Float64.Atan.Program`, which
build from Lean's core library.  The representations need `LeanExe.Pipeline`, which depends on
Talos's CodeLib, and the compilation and the proofs need Mathlib.  `Demos.lean` imports the
program, the representations, and the proofs, `Demos/Verified.lean` imports the compilation and the
allocation bound, and the file theorems are checked on their own after the module is written.
