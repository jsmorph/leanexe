# Drone controller and correctness proofs

This file is the development handoff and progress log for the `drone` branch.
Update it at each meaningful proof checkpoint, then commit and push the Lean
changes and this file. The user explicitly requested frequent updates, commits
and pushes during proof development. Do not commit graphs, HTML notebooks,
binaries, downloaded toolchains, or generated build files.

## Goal and current boundary

Implement a toy terrain-following point-mass autopilot in LeanExe, compile and
run it, illustrate several terrains, and develop formal correctness proofs.
The input is an integer array of terrain elevations. The output is an integer
array `[alt0, speed0, alt1, speed1, ...]`. Minimize traversal time under simple
maneuverability constraints while maintaining a clearance corridor and beginning
and ending on the terrain. No motor, propeller, battery, attitude, drag, lift,
or detailed aerodynamic model is wanted.

The first milestone is complete: `WholeFlight.compute_safe` is a kernel-checked
whole-flight safety theorem for the current point-mass model, and a fresh
aggregate source check passes. The WASM execution proof is the next milestone.
Expansion of the model follows discussion with the user. The user declined
reproducible-artifact packaging as a task priority.  Keep the current
Lean-code-and-task-only commit scope.

`Output.compute_correct` proves that every nonempty accepted terrain produces
exactly 2n words encoding a feasible route, and that its exact tick/excess cost is globally minimal in
the finite graph. Separate corollaries prove on-ground stopped endpoints and
empty/rejected-input behavior. The forward/history and reconstruction helpers
are connected to the actual public entry. Checked segment theorems establish
continuous clearance, component kinematic bounds, physical-time derivatives,
exact tick timing and bounded word arithmetic. `Safety.lean` now exposes
those continuous guarantees directly for every segment of the returned output.
`Trajectory.compute_global_smooth` now assembles the actual output into a
global real-time path and proves its position derivative and continuous velocity,
including joins.  The cumulative-time intervals cover the entire flight and
agree with their local primitives.  Clearance and component speed bounds
transfer to the global coordinate functions. `WholeFlight.compute_safe` now
packages spatial clearance, speed, global velocity derivatives and acceleration
bounds, continuity, stopped ground endpoints, and the singleton case. Agreement
between compiled WASM execution and the proved source computation remains open.

## Safety status and remaining risks

### Current coverage and evidence

Resumed from `b5066cd49fd1a26ecb1dc8fbc63ac923b91128ae` on 2026-09-25 in
`/home/somebody/src/leanexe`. The existing aggregate source baseline passed
(1,998 jobs). The new whole-flight theorem and expanded aggregate check also
passed (2,001 jobs), with only `propext`, `Classical.choice`, and `Quot.sound` in
the axiom audit. A fresh native run reproduced the five-point example below.
Artifact preparation now reproduces the recorded 14,198-byte WASM, and fresh
runtime checks pass for 48 accepted flights, four empty/rejected inputs, and
12 native/WASM comparisons. Scalar helpers, the square-root loop, checked
terrain reads, and height validation also have checked execution lemmas.
The complete segment-cost, packed predecessor, predecessor-scan, and
best-predecessor functions also agree with their source definitions.

| Property | Current proof coverage |
|---|---|
| Clearance | `WholeFlight.compute_throughout` proves `Corridor.height terrain (globalX terrain t) ≤ globalZ terrain t` for every time in the finite flight. `Corridor.height_on_segment` identifies the spatial interpolation of `floorAt`, retaining 100-unit interior clearance and the specified takeoff/landing ramps. |
| Speed | `WholeFlight.compute_throughout` bounds horizontal speed between 0 and 20 and vertical speed magnitude by 20 at every time in the finite flight. |
| Acceleration | `WholeFlight.compute_acceleration_away_from_joins` proves that derivatives of the actual global velocities exist with magnitudes at most 1 horizontally and 4 vertically at every flight time outside the finite set of waypoint times. `Trajectory.compute_global_acceleration_within` supplies bounded one-sided derivatives on each closed segment, including both endpoints. |
| Continuity | `Trajectory.compute_joins` and `compute_global_smooth` establish matching positions and velocities and continuous global velocity.  Acceleration may jump at joins. |
| Interval coverage | `WholeFlight.compute_normalized_cover` transfers the segment results to every physical flight time. `compute_singleton` gives zero duration and a constant stopped ground path for one-point terrain. |
| Endpoints | `WholeFlight.compute_global_endpoints` proves the global path starts at horizontal position 0 and finishes at `100*(terrain.size-1)`, on the corresponding ground heights with both velocity components zero. |
| Feasibility and input handling | `Output.compute_correct` returns an encoded feasible route for every accepted nonempty terrain, with exactly two words per point.  Separate theorems cover empty and rejected inputs. |

Fresh runtime tests cover 48 accepted WASM trajectories and four empty/rejected
inputs against an independent finite-graph planner, plus 12 native comparisons.
The earlier six exhaustive short-route optima and separate translation checks
remain historical evidence. Drivers and logs are excluded from commits under
the existing scope. The source proofs quantify over all accepted inputs within
the stated bounds; helper execution lemmas do not yet establish the full
compiled entry theorem.

### Remaining risks

Source composition is checked in `WholeFlight.Safe` and
`WholeFlight.compute_safe`. The theorem assumes precisely `terrainBound terrain`
and a nonempty terrain. Acceleration bounds apply to ordinary derivatives
between joins and derivatives within each adjacent closed interval at a join;
the two one-sided accelerations need not agree.

Executable correctness: compiled WASM agreement remains unproved.  Array
allocation, copying, ownership, release, and loop execution require semantic
proofs and sufficient memory bounds.  The generated instruction stream will
determine their decomposition and the amount of new shared proof support.
Runtime test results support this work but do not establish the execution
theorem.

Model assumptions: safety assumes exact piecewise-linear terrain and exact
execution of the prescribed motion with independent horizontal and vertical
acceleration.  Terrain uncertainty, tracking error, disturbances, and coupled
actuator limits require additional assumptions and proofs before those effects
enter the safety claim.  The current model permits acceleration jumps at
waypoints.  Safety applies on the finite flight interval.  The formal global
curve extends the final polynomial after arrival.

## Repository and execution environment

The current workspace has the pinned Lean release under
`build/tools/lean-4.34.0-rc2-linux`, and the proof dependencies are materialized
at the committed revisions. The user authorized local Lean execution in this
workspace. Set `LEANRUN_LOCAL=1` and `LEANRUN_TOOLCHAIN` to that directory when
using the commands below. The runner still enforces its shared lock, timeout,
single Lean thread, nice and ionice settings. The earlier machine-specific
settings below are preserved as historical context.

- Upstream: https://github.com/jsmorph/leanexe
- Initial inspection: `main` at `a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`.
- Development branch: `drone`. Keep further proof work on this branch.
- Lean: pinned 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Talos/CodeLib: pinned `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`.
- Mathlib: pinned `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- Wasmtime: 44.0.0; wasm-tools: 1.251.0.
- The original workspace used Node 24.19.0; the full repository suite pins 24.13.0.
- Read and follow `AGENTS.md`. Every Lean, Lake and compiler invocation must go
  through `tools/leanrun`; never run them concurrently. Use bounded commands.
- The user authorized `LEANRUN_LOCAL=1` in the original workspace.  That
  authorization was specific to that environment.  Follow `AGENTS.md` for
  execution in the current checkout.
- Original local toolchain:
  `/workspace/scratch/56b924f3bc36/leanexe/build/tools/lean/lean-4.34.0-rc2-linux`.
  Use `LEANRUN_TOOLCHAIN` or the runner's `--toolchain` option to select it.
  This machine-specific path is not a portable prerequisite.
- Never retry an unchanged proof target after a silent timeout. Split the
  boundary or establish a reusable lemma first. Explicit tactic diagnostics
  should guide the next revision.

LeanExe programs are pure, first-order and monomorphic within a restricted Lean
subset. `UInt64`, bounded `Nat` indices and scalar arrays are supported. The
compiler follows reachable definitions, emits a library-mode WASM `compute`
export, and the repository's C Wasmtime host marshals the array ABI. Native Lean
execution and WASM execution are distinct checks. Signed Lean integer arithmetic
is not part of the chosen executable subset.

## Input and output contract

- 0 to 64 points, 100 horizontal units apart. Terrain is piecewise linear.
- The raw Lean entry accepts `UInt64` elevations at most 1,000,000, relative to
  a datum. Invalid raw input returns `[]`.
- A local JS convenience driver accepts signed decimal integers, subtracts the
  minimum elevation, invokes the unsigned ABI, and adds that datum back to the
  output altitudes. The accepted elevation span is at most 1,000,000.
- Output speed is instantaneous horizontal waypoint speed, not total airspeed.
  Vertical velocity is zero at all waypoints and specified between them by
  the motion primitive.
- First and last altitude equal terrain height, with horizontal speed zero.
  Each interior waypoint has at least 100 clearance.
- Empty input returns `[]`; singleton `h` returns `[h, 0]`. Two points form a
  direct rest-to-rest takeoff/landing transfer.

### Endpoint exception

Define `r[i] = terrain[i] + clearance[i]`, with clearance 0 at endpoints and 100
at every interior point. Interpolate this floor linearly in horizontal position.
This is a takeoff ramp from 0 to 100 required clearance on the first segment and
a landing ramp from 100 to 0 on the last. All other segments require 100
clearance throughout. For two points, clearance is zero over the transfer.
Exempting only the isolated endpoint instants would be inconsistent with
continuous departure from and arrival at the ground. This corridor convention
is intentional and must be preserved in the specification.

## Point-mass motion model

| Quantity | Assumption |
|---|---|
| Horizontal speed | 0 to 20 units/second; waypoint choices 0, 5, 10, 15, 20 |
| Horizontal acceleration | Absolute value at most 1 unit/second² |
| Vertical speed | Absolute value at most 20 units/second |
| Vertical acceleration | Absolute value at most 4 units/second² |
| Waypoint altitude | Floor plus 0, 25, 50, ..., 200 |
| Interior states | 9 altitude choices times 5 speeds = 45 |
| Endpoints | State 0: on the floor and stopped |
| Vertical waypoint velocity | Zero |
| Continuity | Position and velocity continuous; acceleration may jump |
| Controls | Independent net horizontal and vertical acceleration |
| Route | Monotone forward motion; braking and waypoint stops allowed |

The ideal plant can accelerate up/down and forward/backward. Planning excludes
backward excursions. There is no combined thrust budget, jerk limit, wind or
tracking error. Gravity is absorbed into commanded net vertical acceleration.
The returned waypoints plus interpolation define a feedforward autopilot, not a
feedback disturbance-rejection controller. A larger control problem could use
continuous `(x,z,vx,vz)` states and acceleration controls, receding-horizon
replanning and feedback tracking. None of those extensions are implemented.

For one 100-unit segment, let horizontal endpoint speeds be `u,v`, altitude
change `dz=z1-z0`, duration `T`, and normalized time `s=t/T`.

### Moving primitive (`u+v > 0`)

```text
T = 200/(u+v)
x(s) = x0 + 100 * (2*u*s + (v-u)*s²)/(u+v)
z(s) = z0 + dz*(3*s²-2*s³)
vx(s) = (1-s)*u+s*v
ax = (v²-u²)/200
vz(s) = dz*6*s*(1-s)/T
az(s) = dz*(6-12*s)/T²
```

Executable maneuverability tests are:

```text
|v²-u²| <= 200
3*|dz|*(u+v) <= 8000
6*|dz|*(u+v)² <= 160000
```

The clearance gap is a cubic with Bernstein coefficients:

```text
b0 = z0-r0
b1 = z0-r0 - 2*u*(r1-r0)/(3*(u+v))
b2 = z1-r1 + 2*v*(r1-r0)/(3*(u+v))
b3 = z1-r1
```

All coefficients must be nonnegative. Endpoint state bounds guarantee `b0,b3`;
the uphill/downhill branch checks the potentially negative middle coefficient.
This is a sufficient, conservative certificate for clearance over the whole
segment. Some safe cubics are rejected; this restriction belongs to the graph
whose optimum is being proved.

### Rest-to-rest primitive (`u=v=0`)

Both coordinates use `p(s)=3*s²-2*s³`, with horizontal displacement 100:

```text
T = max(25, ceil(3*|dz|/40), ceil(sqrt(3*|dz|/2))) seconds
```

Endpoint floor margins imply clearance because both coordinates share progress.
The duration obeys the component speed and acceleration limits. Its square root
uses 17 steps of binary search with bounds 0 and 65536. Such edges allow steep
terrain to be traversed slowly; zero waypoint speeds do not mean zero motion
between waypoints. Local acceptance and the all-stop whole-route witness are
proved and connected to the public computation, so every accepted nonempty
terrain has a feasible returned route.

## Optimization and representation

Dynamic programming operates on the layered 45-state graph. It minimizes the
lexicographic pair `(total traversal ticks, sum of excess waypoint altitudes)`.
The secondary cost never sacrifices time. Remaining ties retain the first
candidate in ascending predecessor order.

There are 840 ticks/second. A moving edge with `k=(u+v)/5` uses `33600/k` ticks;
`k` is in 1 through 8, and these durations are represented exactly. Rest edges
use `840*T` ticks. Rejection is represented by zero edge ticks. Unreachable row
cost is the sentinel `10^12`.

Rows pack `[time, excess, parent]` for each state into 135 scalar words. The
current public function stores a flat history of parent state numbers and
walks backwards from terminal state 0, builds reversed altitude/speed words,
and reverses the final array. Work is O(n*45²), with O(n*45) predecessor memory,
plus LeanExe array allocation/copy overhead.

Named tail-recursive helpers `validHeights`, `appendParents`, `buildHistory`
and `unwind` expose induction boundaries for the public source proof. Input
heights are checked in reverse order, with the same acceptance condition. The
redundant terminal-infinity return was removed: the checked all-stop witness
establishes a finite terminal label for every accepted nonempty input.

Bounds used by the proofs:

- Floor <= 1,000,100; altitude <= 1,000,300; speed sum <= 40.
- Relevant edge-check products are below 10 billion, hence below 2^64.
- Rest duration <= 75,023 seconds.
- Every edge cost <= 63,019,320 ticks.
- After `i` segments, reachable time <= `i*63,019,320` and excess <= `i*200`.
- For at most 63 actual segments, these costs are far below both the sentinel
  and the UInt64 modulus. Component lemmas allow a conservative 64-step bound.

Optimality is only within the finite graph, with its quantized altitude/speed
states, zero vertical velocity at nodes, primitive family, conservative
clearance test and monotone motion. Do not claim unrestricted continuous-time
physical optimality.

## Code and proof files

Executable:

- `LeanExe/Examples/Drone.lean`: the public `compute` entry and helpers.
- `test/DroneNative.lean`: native Lean CLI for raw unsigned comparison.

Proofs, under `proofs/talos/lean/Project/Drone/`:

| Module | Content and key results |
|---|---|
| `Motion.lean` | Real cubic/Bernstein clearance, vertical speed/acceleration, horizontal speed and endpoint lemmas |
| `Sqrt.lean` | `ceilSqrt_correct`: actual UInt64 search returns the least adequate square root for inputs below 2^32 |
| `Arithmetic.lean` | Actual state decoding and no-wrap bounds; `restSeconds_bounds` |
| `Edges.lean` | Guard extraction and no-wrap products; `state_edge_clearance` for every real s in [0,1] |
| `Dynamics.lean` | Actual accepted integer guards imply all real component speed/acceleration bounds |
| `Timing.lean` | `state_ticks_exact`, `rest_admitted`, `edge_cost_bound` |
| `Kinematics.lean` | First and second physical-time derivatives, horizontal progress bounds, endpoint values |
| `Selection.lean` | Actual tail-recursive scan minimum and attainment; finite result has an admitted predecessor |
| `Rows.lean` | Exact packed field representation (`advance_word`), prefix preservation and row size |
| `Costs.lean` | Exact non-wrapping predecessor sums, stored parent bound and recurrence, propagated row bounds |
| `Initial.lean` | Initial array fields, size, unique reachable state and zero-layer bounds |
| `Optimality.lean` | General layered-graph lower-bound certificate and attaining-route optimality theorem |
| `Planner.lean` | Bellman invariant, feasibility and optimum for repeated executable `advance` transitions |
| `Feasibility.lean` | All-stop route witness, finite and optimal terminal labels, exact floor decoding and terrain specialization |
| `Reconstruction.lean` | Following stored parent words yields a bounded concrete state list attaining the optimal label |
| `History.lean` | Actual input guard, flat parent-history size/indexing, correspondence with the row recurrence |
| `Output.lean` | Actual unwind loop, encoded route, `compute_correct`, invalid/empty cases and exact endpoint pairs |
| `Safety.lean` | Direct output-index interior clearance, admitted adjacent pairs, continuous segment clearance, component limits and exact duration/tick correspondence |
| `Gluing.lean` | Reusable finite-curve construction on cumulative time; matching value/derivative gluing and continuous velocity |
| `Trajectory.lean` | Returned primitive endpoints and derivatives, moving/rest joins, `compute_global_smooth` for the assembled path |
| `Acceleration.lean` | Actual global velocity derivatives and component acceleration bounds, including derivatives within closed segment intervals at joins |
| `Corridor.lean` | Spatial interpolation of the specified floor, horizontal progress bounds, and clearance at actual global horizontal position |
| `WholeFlight.lean` | `Safe` and `compute_safe`: finite flight time, universal spatial/speed bounds, global acceleration, continuity, ground endpoints and singleton behavior |
| `SourceChecks.lean` | Aggregate check and printed axiom audit for these source components |

`Planner.layers` is a reference sequence of the actual executable `initial`
and `advance` calls. `History.computed_history_valid` connects its stored
parents to `buildHistory`. `Output.unwind_words` connects the public backward
loop to the encoded feasible route. `Output.compute_correct` composes these
results with Bellman optimality for the actual returned array.

Proofs use no proof holes, custom axioms or native evaluation proof shortcuts.
The printed axiom dependencies are only the standard Lean `propext`,
`Classical.choice` and `Quot.sound`, as applicable. Do not weaken goals or add
assumptions that merely restate the desired result. Tests are evidence, never
premises of correctness theorems.

## Work completed and observed results

1. Inspected the repository, specification, compiler entry conventions, native
   and WASM runners, Talos documentation and ProofKit boundaries.
2. Designed and documented the model and the endpoint clearance corridor.
3. Implemented, built, compiled and ran the native Lean and WASM controller.
4. Exercised flat, plateau, hill and repeated-ridge terrain; generated altitude
   and speed graphs using the continuous motion equations and exact outputs.
5. Added proof components and refactored two induction boundaries without
   changing the flight model: explicit-fuel square root and named
   tail-recursive selection/row accumulators.
6. Proved the current segment, arithmetic, selection, row and DP components.
7. Saved a self-contained project notebook, and separately saved `Drone.lean`
   and the four-flight PNG at the user's request. Generated visual artifacts
   remain outside this Git commit policy.
8. Created branch `drone`; checkpoint and push Lean proof increments here.

Example:

```text
input:  [0, 20, 80, 40, 0]
output: [0, 0, 145, 10, 180, 15, 165, 10, 0, 0]
segment seconds: [20, 8, 8, 20]
total: 56 seconds = 47,040 ticks
```

Four saved 1,400-unit, 15-point routes:

| Terrain | Time in seconds | Maximum waypoint speed |
|---|---:|---:|
| Broad plateau | 107.428571... | 20 |
| Flat | 107.428571... | 20 |
| Rounded hill | 117.428571... | 20 |
| Repeated ridges | 136 | 15 |

Runtime regression passed 48 WASM trajectories, 12 native Lean comparisons,
six exhaustively enumerated short-route optima, continuous clearance and
kinematic checks, reversal/translation properties, signed CLI handling,
invalid input guards, the 64-point limit and million-unit elevation changes.
The four saved plotted outputs also match the refactored WASM exactly.

Current emitted WASM: 14,198 bytes; SHA-256:
`0c24d2c1568ca40321421d19387843d4ee81c970d53e75adcb035b32343c0942`.
The binary is not committed and is not an exact-artifact proof.
The full repo test suite and Talos artifact-proof gates have not been run for
this new controller.

## Verification and reproduction

Use a supported resource environment and the pinned toolchain. From repo root:

```sh
tools/leanrun --timeout 3m lake --dir proofs/talos/lean build Project.Drone.SourceChecks
tools/leanrun --timeout 15m lake build lean-wasm LeanExe.Examples.Drone
tools/leanrun --timeout 2m lake env lean --run test/DroneNative.lean 0 20 80 40 0
tools/leanrun --timeout 2m .lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.Drone --entry LeanExe.Examples.Drone.compute \
  --out build/drone/drone.wasm
```

Create the output directory before compiling if necessary. Download/build the
Wasmtime C host using the existing repo instructions, then invoke the unsigned
array ABI with the host's `call` subcommand. No JavaScript WASM execution is
used.  The original workspace used an authorized `LEANRUN_LOCAL=1` setting and
an explicit toolchain selection.  Follow the current environment's execution
authorization and resource policy.

The original workspace held the convenience JS driver, JS test suite, expanded
prose documentation, plots, and notebook generator.  These files were excluded
from commits under the user's Lean-code-and-task-only instruction.  Native Lean
execution and the aggregate proof command above use committed code.  Later
commits should respect that file scope unless the user changes it.

## Remaining verification plan, in order

- [x] Check the existing source baseline in the current environment with the
  pinned toolchain and required resource limits.  Run
  `Project.Drone.SourceChecks` and review its axiom audit.  Distinguish dependency
  setup from proof failures and preserve diagnostics.
- [x] Complete the public whole-flight safety theorem by composing the
  established results.  State the finite flight interval, terrain and input
  assumptions, spatial clearance, speed bounds, acceleration bounds between
  joins, continuous position and velocity, and stopped ground endpoints.
  Include the singleton case and retain the specified takeoff/landing corridor.
  Build the combined theorem and aggregate source checks.  This is the first
  safety milestone.
- [ ] Prove WASM execution agreement after the source safety milestone.
  Prepare the generated program and annotations, identify the exact binary
  being proved, and establish ABI, memory, ownership, and termination conditions.
  Prove scalar helpers first, then predecessor selection and row construction,
  parent-history construction, reconstruction and reversal, and the public
  guards and entry.  Compose a `Wasm.TerminatesWith` theorem returning the same
  words as `Drone.compute`, then transfer the source safety result to those
  words.  Check the execution theorem against the generated model and the
  identified bytes.
- [ ] Discuss expansion after the safety baseline is checked.  Choose each
  additional model assumption or controller feature with the user, then extend
  its safety statement and proof.

Keep this record current and commit/push checked Lean increments on `drone`.
Preserve the separate source and image outputs.  Existing graph optimality and
exact tick-timing results remain available for the execution proof.  Follow the
existing commit scope and preserve branch history.

## Findings and failed approaches worth preserving

- A mutable record holding multiple arrays plus nested parent arrays compiled
  but trapped in generated `release`, even on singleton input. Packed scalar
  rows and flat parent storage solved the runtime issue without compiler edits.
- An initial non-tail recursive row refactor was rejected by LeanExe. Tail
  recursive accumulators are supported and preserve stable tie breaking.
- `UInt64` numeral coercions and modular arithmetic must be reduced explicitly.
  Blind `Nat.mod_eq_of_lt` rewriting can target an inner state modulus instead
  of the outer machine-word modulus.
- Core range loops are not simply kernel-reducible at every boundary. Rewriting
  through `Std.Legacy.Range.forIn_eq_forIn_range'` and the pure-yield fold lemma
  made the initial array proof check.
- Avoid elaborator expansion of the full 45-candidate scan when comparing cost
  projections. Reduce the small `Selection.cost` wrapper explicitly first.
- Existing ProofKit offers useful scalar, array, loop and allocator lemmas,
  but not a complete ready-made shortest-path or this controller theorem.
- The global documentation checker reports an unrelated pre-existing absolute
  temporary path in `paper/wgsl-verification-report/review.md` at the inspected
  base. No unrelated fix was made.

## Checkpoint log

### 2026-09-25 — initial drone branch checkpoint

Includes the Lean executable, native runner and source-proof modules listed
above, plus this task record. Targeted executable/WASM regression passed before
this proof-only increment. The aggregate `Project.Drone.SourceChecks` target passed (1,991 build jobs,
mostly cached); the printed axiom audit contains only standard Lean axioms. The outstanding `compute` and artifact boundaries are
explicitly retained in this record. Graphs and HTML are excluded.


### 2026-09-25 — terrain feasibility checkpoint

The first checkpoint was published as `b79e90347218c0c36ad1fb66a2a37fa2f3c760dc`
on `origin/drone`. HTTPS Git write credentials were unavailable, so the checked
Git tree was published through the authenticated GitHub connector, fetched, and
matched byte-for-byte before synchronizing the local branch. Subsequent remote
updates use non-forced branch updates; preserve the previous local commit when
synchronizing equivalent GitHub-created commits.

Added `Feasibility.lean`. Lean now proves an all-stop path for any bounded floor
sequence, reachability of the terminal stopped state, and an attained optimum
at that state in the actual row recurrence. The floor decoding theorem proves
that its UInt64 addition does not wrap and gives the intended endpoint and
interior values. These results specialize to every nonempty terrain with at
most 64 elevations, each at most 1,000,000. `compute` guard/loop/reconstruction
correspondence remains unproved. The focused feasibility target passed, and
the aggregate source check includes its theorems and axiom audit.


### 2026-09-25 — stored-parent reconstruction checkpoint

The feasibility checkpoint was published as
`3eff0614bb5220861db5134c8b7585b345bdac3e`. Added `Reconstruction.lean` and checked
`parent_step`, `backtrack_correct`, and `reconstructed_optimal`. These follow
the actual predecessor words in the proved row sequence, producing a concrete
list of bounded states with exactly n+1 points. The list is feasible and attains
the globally optimal terminal label. The public function's separate flat parent
history and reversed altitude/speed output loop are not yet equated to this
reference reconstruction. That correspondence is the next implementation proof.
The aggregate source target includes the new theorems and axiom audit.


### 2026-09-25 — public source correctness checkpoint

The stored-parent checkpoint was published as
`6d1208f42d90e37c5eb3040f8f9889339f75d1ca`. Refactored the public loops into
named tail-recursive helpers supported by LeanExe. Added `History.lean` and
`Output.lean`. The aggregate `Project.Drone.SourceChecks` target passes
(1,995 jobs), including `compute_correct`, `compute_invalid`, and
`compute_endpoints`; axiom dependencies remain standard only. No proof holes
or unchecked evaluation shortcuts were introduced.

The new public entry was compiled to WASM and the full targeted drone
regression passed again: 48 WASM flights, 12 native comparisons, six exhaustive
short-route optima, continuous limit checks and input/translation cases.
Logs: `build/drone/source-proof-check.log` and
`build/drone/public-refactor-regression.log` (generated, not committed).
The graph contract is now proved for the actual source `compute`, while the
continuous whole-flight composition and exact emitted-WASM proof remain
explicit further tasks. Keep future commits restricted to Lean and this file.


### 2026-09-25 — public output continuous-safety checkpoint

The public source theorem checkpoint was published as
`263b45f1611a049f78849b8f61fa83e77b54dacc`. Added `Safety.lean`, connecting
individual output word indices to bounded states and every adjacent pair to
an admitted edge. The four public corollaries establish interior 100-unit
clearance, universal continuous segment clearance, all component maneuverability
bounds, and exact tick/duration correspondence. These are kernel proofs over
all accepted inputs and all real normalized segment times, not sampled checks.
The focused target and aggregate source target pass with standard axioms only.

No executable behavior changed in this proof increment, so the previously
passed runtime suite and the rechecked four graph outputs remain applicable.
Graphs/HTML remain outside commits. The exact-WASM theorem and a packaged
global real-time path remain future work; neither is claimed by this checkpoint.


### 2026-09-25 — global trajectory and velocity continuity checkpoint

Resumed from published commit `1e56a01f2bcdc335c90e2e4771678d7b870f1701` after
the transient checkout had been cleared. Restored branch `drone`, the exact
pinned Lean release (version/commit checked) and pinned proof dependencies.
The bounded cache restore made progress to 96% before its time limit; a second
bounded call restored the remaining files. The initial archive extraction had
ownership-setting warnings in this managed workspace; file extraction and the
pinned Lean version check succeeded. Future extractions should use
`tar --no-same-owner`.

Added `Gluing.lean` and `Trajectory.lean`. The generic `stitch_smooth` theorem
constructs one finite curve on cumulative physical time and proves its
specified derivative and continuous velocity from local derivatives and matching
endpoints. The public `compute_joins` and `compute_global_smooth` instantiate
that result for the actual returned drone words, including stopped/moving
transitions and the singleton constant path. Position and velocity are
continuous at internal joins; no second-derivative claim is made there.
The focused trajectory target and aggregate source checks pass, with only
standard Lean axioms. Executable code is unchanged.

Proof-development findings: unfold partially applied coordinate definitions
before rewriting branch conditions. Separate branch simplification from index
arithmetic and default list-index simplification, so a guard is not rewritten
into a syntactically different expression before its hypothesis applies.
The generic derivative gluing proof combines derivatives within the left and
right half-lines and uses continuity only for the velocity gluing step.

Prepared a local unfinished `drone` case in `proofs/talos/cases.json` for the
next exact-artifact step (`complete: false`, annotations enabled, source module
`LeanExe.Examples.Drone`, entry `LeanExe.Examples.Drone.compute`, Lean namespace
`Project.Drone`). Its future behavior target is `Project.Drone.Spec.compute_correct`;
that target is not yet proved. The JSON registry edit is deliberately outside
commits under the user's Lean-code-and-task-only instruction.


### 2026-09-25 — cumulative interval and global safety checkpoint

The global smoothness checkpoint was published as
`3e55d65e225782b241a2a97421e89f0e6369ef94`. Added monotonic cumulative clocks,
interval coverage, and `stitch_on_segment`: the assembled curve equals the
intended primitive on each whole closed interval. Public corollaries connect
all four actual global coordinates to local primitives and transfer continuous
clearance and speed bounds to the global functions. The aggregate source check
passes; axiom dependencies remain standard only. Executable source is unchanged.

Started `tools/talos-artifact.js prepare drone`. Restored the pinned native
verifier's dependencies, reusing build caches only after matching their exact
Git revisions. Its default optimized C compilation of the large generated
emitter was slow and was explicitly interrupted (exit 130) to complete source
proof checks first. The next attempt uses a temporary local `moreLeancArgs =
["-O0"]` in the verifier/interpreter package configuration. This changes native
build optimization, not Lean definitions, kernel checking, or proof assumptions.
Record the emitted artifact digest and check it against the prior 14,198-byte
artifact before claiming artifact reproduction. Do not mark the unfinished
behavior theorem or exact-byte decoder identity as proved merely from generation.

### 2026-09-25 — safety-first scope and status review

Reviewed `41a97a6e80ac90e503e981ecd7052c2b489619e9` and confirmed that the remote
`drone` branch still named that revision.  Work in this checkout through the
review consisted of source inspection and planning.  Fresh Lean and runtime
checks remain pending here.  Earlier passing checks are recorded above.

The user set the first milestone to a checked whole-flight safety proof under
the current point-mass assumptions, followed by expansion from that baseline.
Updated the current status, evidence, risks, and work order to put source
composition and fresh checking first, WASM execution agreement second, and
model expansion after discussion.  The user declined reproducible-artifact
packaging as a priority.  This checkpoint changes the task record.

### 2026-09-25 — whole-flight source safety checkpoint

Resumed `drone` from `b5066cd4` in `/home/somebody/src/leanexe`. Installed the
pinned Lean 4.34.0-rc2 release and verified compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. Materialized the pinned Talos,
mathlib, and supporting proof dependencies. The user's permission to execute
Lean locally authorizes `LEANRUN_LOCAL=1` here; all Lean and Lake commands used
`tools/leanrun` sequentially with bounded timeouts.

A session interruption left empty cache traces and truncated cached outputs.
Ordinary cache retrieval removed affected archives without repairing the empty
destination traces. A separately downloaded archive extracted correctly into
a fresh directory; forcing retrieval and extraction with `cache get!` repaired
the selected dependency closure. The initial aggregate run then reached its
three-minute limit while rebuilding supporting tactic libraries, with progress
diagnostics and no drone proof error. A separate `Project.Drone.Motion` build
completed that dependency boundary, followed by a successful original aggregate
source check (1,998 jobs). Setup failures and the interrupted build were not
treated as failures of the existing proof statements.

Added three proof modules. `Corridor.lean` uses the existing finite-curve
construction on 100-unit spatial intervals, proves that it interpolates
`floorAt`, and identifies normalized primitive progress with global horizontal
position. `Acceleration.lean` transports primitive velocity derivatives onto
the actual global velocity functions using agreement on each closed interval.
This yields bounded derivatives within each segment at both endpoints and
ordinary derivatives in the interior, without requiring acceleration to agree
across a join. `WholeFlight.lean` proves the global ground endpoints, normalized
time coverage, and bounds at every time in the finite flight, then packages
them in `WholeFlight.Safe` and `WholeFlight.compute_safe`. Its acceleration
corollary quantifies directly over all flight times outside the finite set of
waypoint times. Singleton terrain has zero duration and a constant stopped
ground path.

The focused modules and `Project.Drone.SourceChecks` passed (2,001 aggregate
jobs). The expanded printed axiom audit, including `WholeFlight.compute_safe`,
contains only the standard `propext`, `Classical.choice`, and `Quot.sound`.
There are no added proof holes, axioms, or native evaluation proof shortcuts.
Initial diagnostics were namespace resolution and endpoint index/coercion
normalization issues; no specification or input assumption was weakened.

Fresh native execution of `test/DroneNative.lean 0 20 80 40 0` returned
`[0, 0, 145, 10, 180, 15, 165, 10, 0, 0]`, matching the recorded example.
The executable planner was unchanged. The broader historical native/WASM
regression suite and artifact gates were not rerun for this proof-only increment.

Local evidence is retained in `build/logs/`: `cache-repair.log`,
`source-baseline-complete.log`, the focused proof logs (including failed
attempts), `source-whole-flight.log`, and `native-example.log`. These logs,
dependencies and toolchain files remain ignored local state. This checkpoint
contains only Lean proofs and this handoff. The first safety milestone is now
complete; exact compiled-WASM execution agreement remains the next proof task.

### 2026-09-25 — artifact generation recovery and annotation repair

Continued from `a669b528` toward WASM execution agreement. Installed Node
24.13.0, wasm-tools 1.251.0, and the checked Wasmtime 44.0.0 C API archive in
ignored local build directories. The user installed the missing C headers;
the repository's Wasmtime C host then built with the pinned Lean distribution's
Clang, using its builtin-header include directory together with the system
headers. No project runtime source changed.

The verifier's generated `Emit.c` crashed in bundled Clang 22.1.4 at `-O0`
(`alloc-token`) and `-O1` (`always-inline`). A focused build succeeded with
`moreLeancArgs = ["-O0", "-Xclang", "-disable-llvm-passes"]` in the ignored
Talos verifier package. The interpreter package retains the local `-O0`
setting. These flags affect native build optimization only. The compiler's
`Extract.Values` module also failed once while saving its `.olean`, then passed
on a focused bounded rebuild. Failure logs and compiler crash reproducers were
preserved locally.

Artifact preparation exposed an actual annotation bug in `directCallResults`:
`List.take resultCount` can yield a shorter suffix at the end of a branch, and
`mapM` on that suffix can succeed without a complete set of result stores.
The emitter now checks the suffix length before describing a complete local
result bundle. A call without that bundle keeps the stack-result annotation.
Focused regression cases cover no stores, a partial two-result bundle, and a
complete reversed stack-to-local bundle.

`tools/talos-artifact.js prepare drone` passes after that change. Its generated
`Program.lean` and `AnnotationMatches.lean` describe the real artifact. Both
before and after the annotation fix, the WASM has 14,198 bytes and SHA-256
`0c24d2c1568ca40321421d19387843d4ee81c970d53e75adcb035b32343c0942`, exactly
matching the earlier artifact. A fresh Wasmtime run returns
`[0, 0, 145, 10, 180, 15, 165, 10, 0, 0]` for the recorded example. A local
regression driver checks 48 accepted flights and four empty/rejected inputs
against an independent finite-graph planner; all pass, including 64-point
terrains and the maximum allowed height range. Runtime testing is supporting
evidence, not the missing execution theorem.

The first generated-annotation Lean build reached its five-minute limit while
building the broader interpreter dependency closure. It reported dependency
segfaults and a missing compiled linter declaration, before reaching drone proof
checking. A full forced cache restore is replacing the incomplete mixed mathlib
cache. Its first attempt was blocked by sandbox DNS and was stopped; the
approved network retry downloaded all 8,747 files and is extracting them.
`ExecutionScalar.lean` is being developed against the emitted functions, but
its Lean checks, the generated annotation checks, and native comparison harness
remain pending at this point. The full WASM execution and safety-transfer
milestone remains open. The local case registry stays outside commits.

The full forced cache extraction completed successfully. The corrected
`test/direct_call_annotations.lean` passes, and the generated native harness
passes all 12 native/WASM comparisons. This verified compiler-annotation
checkpoint includes `Binary.lean`, that focused regression, and this handoff.
The generated model and in-progress scalar proof files await their own Lean
verification before being committed. No instruction bytes changed.

### 2026-09-25 — interpreter dependency isolation

After restoring the full cache, a fresh `Project.Drone.SourceChecks` build
passed all 2,001 jobs again, including the whole-flight theorem and its
standard-axiom audit (`build/logs/source-after-cache-repair.log`). The restored
interpreter semantics module also builds successfully. The first scalar/model
aggregate then exhausted its eight-minute limit in `Interpreter.Wasm.SmallStep`,
before reaching the new drone proofs.

Divided that dependency into diagnostic boundaries instead of repeating the
unchanged target: executable definitions checked in seconds, and the full
inductive step relation checked separately with profiling. A simplification
trial for the scalar-float bridge lemmas passed but offered little improvement
and was not retained. A focused full dependency build uses sequential
elaboration and progress instrumentation only; its semantic definitions and
theorem statements/bodies are unchanged. The pending drone proof modules cover
scalar helpers, the square-root loop, and checked terrain reads. They remain
unverified development files until the dependency build allows their checks.

The instrumented `SmallStep` dependency build completed successfully in 760
seconds, with all five checkpoints reached. No proof rewrite or semantic
change was needed. Its profile records most time in simplification, tactic
execution, and processing recursive proof declarations. The prepared further
split was therefore not applied. The scalar/model aggregate is now rebuilding
the remaining interpreter proof modules against that checked dependency.

The generated drone `Program.lean` and all ten scalar execution lemmas now
check. The lemmas cover the three Choice projections, lexicographic choice,
distance, altitude, speed, both constants, and the unreachable sentinel, with
unchanged stores and only standard Lean axioms. Initial failures in these
drafts were proof scripting, typed-control normalization, and Nat/UInt64
conversion obligations; their final statements have no added assumptions.

The first annotation check exposed missing result-type metadata in the shared
`ScalarTransition.Expr.program` description. Its generated `and`/`or` branches
must carry an i32 result, while division/remainder guards and value branches
carry i64. Updated the shared description and its semantic proof using the
existing typed-control compatibility theorem. The generated drone annotation
identities now check by reflexivity, including the complete square-root loop;
no generated drone file or WASM instruction was hand-edited. All generic scalar
transition proofs also pass. Logs are `drone-model-scalar-5.log` (failed shared
proof attempt) and `drone-model-scalar-6.log` (passing drone and generic targets).

The same aggregate attempted two existing annotation examples but exhausted
its three-minute budget while building `FixedArrayAllocator`, before checking
those examples. Those regression checks remain pending; the successful drone
and shared scalar targets are not evidence that the entire aggregate passed.
Next checks are the bounded square-root loop and the checked terrain read.

Published the model/scalar checkpoint as `eec06de5`. The next focused aggregate
passes both `ExecutionSqrt.lean` and `ExecutionRead.lean`
(`build/logs/drone-sqrt-read-4.log`, 3,363 jobs). The square-root invariant ties
the current fuel and interval to the original source result; fuel decreases
on search steps and the completion flag decreases the measure on early exit.
It proves arbitrary UInt64 inputs and any representable fuel, not just the
17-step wrapper. The terrain-read theorem uses `UInt64Array.At`, an in-range
index, checked-load semantics, the stored length, and overflow-free index
increment to establish the exact source `floorAt` result with unchanged memory.
Both modules' axiom audits contain only the three standard Lean axioms.
Their earlier failed attempts are retained in the numbered local logs.

Published the square-root/read checkpoint as `843f3e6f`. Checked
`ExecutionValidation.validHeights_exact` against the actual input-validation
loop, including zero fuel, normal fuel decrease, early rejection, and the
borrowed-array ownership bookkeeping. Its store is unchanged. Checked
`ExecutionRest.restSeconds_exact`, preserving intermediate operand-stack values
across the repeated square-root calls with `TerminatesWith.append_args`.
The four duration comparisons use the source UInt64 maximum definition;
simplifying comparison hypotheses into different order relations too early
prevented their later use, so the final proof preserves those hypotheses.

Also checked `ExecutionPredecessorRead.predecessor_readTime`: the emitted
checked multiplication, checked array access, and precise resulting frame for
the first packed-row load. It is a prefix theorem, not the full predecessor
specification. `ExecutionEdgePrefix.edgeTicks_entry` checks the shared entry
setup and initial distance call. All four modules have standard-only axiom
audits. Their local logs include `drone-rest-validation-4.log`,
`drone-rest-edges-4.log`, `drone-read-edge-rest.log`, and
`drone-edge-prefix-rest-4.log`; aggregates that include a later failed or
timed-out target are not recorded as fully passing runs.

The full segment-cost tactic search reached its time budget without a
diagnostic. Split the duration theorem, rest/moving cases, and common entry
prefix instead of rerunning the same target unchanged. The rest case still
timed out after the prefix split, so a separate body theorem now uses explicit
call boundaries rather than searching through alternative callee rules.
Its check and the moving-case proof remain pending. The existing external
annotation examples remain pending behind the allocator dependency as recorded
above. No executable instructions or source input assumptions changed.

### 2026-09-25 — edge branch and arithmetic checkpoint

Published the validation/read-prefix checkpoint as `76e8c330`. Added and checked
`ProofKit.ConstIf.wp_constIf`, which handles constant-valued Boolean branches
without duplicating the caller's postcondition, and
`ProofKit.CheckedNatAdd.guard_spec`, which discharges the emitted overflow guard
from a representable Nat sum. Their axiom audits contain only standard axioms.
`Drone.EdgeSource.edgeTicks_eq` gives a checked non-monadic equation for the
source segment cost. `ExecutionEdgeRestBody` and `ExecutionEdgeRest` now prove
the complete emitted rest-to-rest segment-cost case. The final body check takes
about four seconds, and the public wrapper checks in two seconds.

The unrestricted moving-case tactic still exceeded its bounded runtime after
several control-flow reductions. A no-progress simplification could roll back
a preceding branch split; fixing that exposed the remaining nested arithmetic.
The next decomposition uses the already-checked `ScalarTransition.Expr`
framework for that arithmetic suffix, with an explicit evaluation lemma before
reconnecting it to the emitted body. That suffix, the moving-case theorem,
and the full predecessor theorem remain unverified development files. A generic
WP congruence experiment is also local and has not established a performance
benefit yet. No source behavior, instruction bytes, or input bounds changed.

Evidence: `build/logs/const-if-1.log`, the passing `CheckedNatAdd` target in
`edge-source-add-rest-1.log`, and the passing rest wrapper in
`drone-edges-compact-1.log`. Those latter aggregates contain other failed targets
and are not recorded as wholly passing runs. Subsequent tail attempts and
moving-case timeouts remain in their numbered local logs.

The emitted moving branch and complete `ExecutionEdges.edgeTicks_exact` now
check. `ExecutionEdgeTailModel` describes the arithmetic suffix using the shared
scalar-expression language; the `change` step in the execution theorem checks
its identity with the actual emitted suffix. `ExecutionEdgeTail` evaluates that
descriptor using the established `U64State` bridge. Explicit Option-bind and
constructor simplification, together with the seven semantic guard cases, avoids
the earlier unproductive generic simplification. The evaluation proof checks in
13 seconds and the moving execution proof in 5.3 seconds. The experimental WP
congruence rule was removed from imports and kept only as an ignored diagnostic;
the final proof does not require it.

`ExecutionPredecessor.predecessor_exact` also passes, covering both checked
packed-row reads, all altitude/speed/edge calls, the reachability guard, and the
exact three-word Choice result, with unchanged memory. Its assumptions are the
array representation, both row accesses in range, and a representable target.
The check takes 7.6 seconds. The aggregate
`build/logs/drone-predecessor-1.log` passes all 3,379 jobs, with standard-only axiom
audits. Predecessor scanning and the allocating array loops remain open.

The user explicitly authorized up to 12 GB of RAM for Lean on this machine.
Local runner mode still has no enforced cgroup memory cap; keep one Lean process
and bounded timeouts, and monitor memory against that ceiling. Recent drone
checks use about 4 GB resident memory. The earlier 4/6 GB standard-mode settings
are not active in this authorized local mode.

The scan proof now has checked entry, frame/invariant, and first-candidate
prefix lemmas. `scanPrefix_spec` checks the source-index increment and overflow
guard, copied arguments, actual predecessor call, and resulting comparison
stack in about four seconds. The first failed frame comparison was an
elaboration problem: normalize list append and the two representations of the
UInt64 index before matching the continuation. The instruction prefix itself
was already reducing successfully.

The combined scan-step proof still exceeded its bounded runtime, so its time
comparison cases were split into separate modules. `scanStep_time_lt` now
checks in 18 seconds, with only standard axioms (`drone-scan-time-1.log`).
The branch tactic stops at the continuation instead of trying more instruction
rules there, and uses explicit Boolean reductions. The equal-time branch needs
the UInt64-specific irreflexivity theorem; the generic order theorem did not
rewrite that comparison. The remaining cases, complete scan, and best-choice
wrapper are still being checked. Allocation/release adaptation and the
previously pending held-out annotation regressions remain open.

All scan cases now pass: equal-time in 58 seconds and the remaining unequal-time
case in 19 seconds. Their composition checks in 2.9 seconds, the complete
`scanPredecessors_exact` loop theorem in 5.3 seconds, and
`bestPredecessor_exact` in 3.8 seconds. The aggregate
`build/logs/drone-scan-best-8.log` passes all 3,388 jobs. All axiom audits contain
only standard Lean axioms. The loop theorem quantifies over representable
targets and packed predecessor rows covering the requested source range,
preserves the store, returns the exact three source Choice words, and proves
termination by decreasing fuel. The source-index overflow guard and borrowed
array ownership bookkeeping are included. Peak observed resident memory stayed
near 4.3 GB. Allocating array loops and the full compiled entry remain open.

Published the scan/best checkpoint as `8dcce121`. Split the unchanged allocator
definitions and frame helpers into `FixedArrayAllocatorBase.lean`, leaving its
execution theorem in `FixedArrayAllocator.lean`. The base checks in 4.6 seconds;
the focused execution check passes in 93 seconds (`allocator-region-1.log`,
3,345 jobs). The formerly blocked annotation regressions now both pass:
`Project.TinyGpt2Seq.AnnotationMatches` and
`Project.SequenceSoftmax.AnnotationMatches` (`scalar-held-out-2.log`, 3,362 jobs).
This closes the held-out regression gap for the shared scalar control-type
change. Drone heap allocation/release adaptations are next; their initial check
also needs the existing shared runtime/heap proof dependencies to be built.

Published the allocator/regression checkpoint as `c404f1a2`. The initial heap
aggregate built the uncached runtime and existing heap dependencies, then reached
its ten-minute limit before the final targets. Split the generic word-buffer
finishing lemma into `HeapWordsFinishBase.lean`, preserving the old public
release theorem through its original import. The drone allocation and release
adaptations now check in about three seconds each. They use the actual drone
module and release function 29, including free-list reuse and memory growth.

Added checked empty-array memory/ownership lemmas, exact word-array capacity
arithmetic, and preservation of borrowed arrays across allocation, writes, and
release. The borrowed representation matters for the actual host ABI:
`tools/wasmtime-host.c` allocates terrain through the raw-buffer allocator and
writes its length and words, without changing the header to internal-array kind.
The input-preservation assumptions therefore do not require that internal kind.
The empty-array proof was divided at the memory-write boundary after a bounded
aggregate expired; its two final checks take about three seconds each.

The first empty-array axiom audit exposed an inherited native `bv_decide` axiom
through `Mem.read64_write64_same`. Replaced that use in all six locations in
`ProofKit.FixedArrayResult` with the existing kernel-checked
`ProofKit.Memory.read64_write64`. The allocator, empty, singleton, and pair
result audits now contain only standard Lean axioms
(`build/logs/allocator-result-axioms.log`). The new heap, borrowed-array, empty
array, and capacity lemmas also have standard-only audits. Both held-out
annotation regressions pass again after this shared change.

`WordArrayPush.program` describes the common fifteen-scratch-slot push sequence.
`Drone.ArrayPushShape` checks by reduction that all three pushes in the emitted
advance loop match it exactly. Those are instruction-identity lemmas; the full
shared push execution proof and the allocating controller loops remain open.
The aggregate `build/logs/drone-array-foundations-2.log` passes all 3,489 jobs,
including the retained Euler release theorem and both annotation examples.
`drone-array-memory-1.log` separately passes the borrowed-input and empty-memory
lemmas. Earlier failed and timed-out runs remain in their numbered local logs.

The shared array-push execution theorem now passes. `WordArrayPushFrame` models
the fifteen scratch slots; separate preparation, capacity, header installation,
and copy/append lemmas each check in roughly three seconds. The complete drone
`word_push_spec` composes them with the existing free-list allocator, returns
the exact pushed array and pointer, preserves the borrowed source, and restores
the heap and new-buffer ownership invariants. Its write-range result also lets
callers preserve unrelated live arrays. Both fresh allocation and free-list
reuse are covered. `build/logs/drone-push-3.log` passes all 3,484 jobs, and every
new axiom audit contains only standard Lean axioms.

The small failed iterations were local elaboration issues: slot zero needs an
explicit frame lookup, store addresses need the numeric 32-bit modulus exposed,
and UInt64 capacity equality must be converted to a natural-number bound. No
silent timeout occurred in this checkpoint. The full allocating controller
loops and compiled compute/safety transfer remain open; source and earlier
scalar/scan execution proofs remain checked.

Published the shared push theorem as `2396ddba`. The budgeted push wrapper now
reuses `OutputBudget` to account for allocation bytes, physical pages, and the
module's memory cap while preserving every previously live borrowed/owned word
array. The emitted empty-array allocation sequence also has an execution
theorem, checked instruction matches in `advance` and `initial`, and a budgeted
wrapper. The initial budget build populated existing output-map dependencies;
its final diagnostics were two redundant tactics, not resource exhaustion.

The parent-history loop now has checked packed-parent reads and both cleanup
cases. `append_read_spec` covers state increment, multiplication by three,
offset addition, and checked load. The cleanup proofs distinguish an initial
borrowed buffer from a tracked buffer that must be released. Both cases check
in about eight seconds. `PreservesWords` records caller-owned and borrowed
arrays across allocations/releases; the complete `append_step_spec` uses it
to keep the caller's live memory intact and proves the next loop state and
remaining budget. `build/logs/drone-append-step-3.log` passes all 3,532 jobs;
all new dependency audits contain only standard Lean axioms. The terminating
parent-history loop, other allocating loops, and compiled compute theorem are
still open.

Published the budget/parent-step checkpoint as `11a0dfa2`. The complete
`appendParents_exact` function proof now passes (`drone-append-3.log`, 3,531
jobs, 4.5 seconds for the final theorem). It proves source agreement and
termination with decreasing fuel, exact owned-array return values, preservation
of the caller's live arrays, nonaliasing of the new result after a nonempty
append, and the remaining allocation/page budget. The entry and loop invariant
are separate from the step theorem. All audits remain standard-only. The next
allocating function is the row-building advance loop, combining best-choice
scanning with three pushes per state.

The entire row-building `advanceLoop_exact` and its `advance_exact` wrapper
now pass. Choice selection covers ordinary states and the final-layer stopped
state restriction; preparation checks target increment; the three pushes
preserve every caller-live array and have exact allocation budgets; both
borrowed and tracked old-row cleanup cases pass. The loop proves termination,
source agreement, owned results, and nonaliasing/preservation.

The first combined three-push proof reached its elaboration heartbeat limit.
Splitting off `advance_two_push_spec` reduced the final two/three-push checks
to about four seconds each. Some large instruction-shape reductions also
needed the existing 32,768 recursion-depth setting. The wrapper now has
separately checked entry and finish lemmas; its earlier heartbeat failures
also followed a shadowed `previous` binder (allocator scratch word versus
source array), which is fixed. Read the first diagnostic before the later
normalization errors. The final wrapper check takes 3.1 seconds.

`build/logs/drone-advance-5.log` passes all 3,572 jobs, with standard-only
axiom audits. The row loop itself checks in 4.5 seconds and the complete step
in 4.7 seconds. Observed Lean RSS was about 4.1 GB plus 0.9 GB for Lake, below
the user's 12 GB ceiling. Initial-row construction, full history construction,
route unwinding/reversal, and the compiled compute/safety transfer remain open.

The complete compiled initial-row constructor now checks in `initial_exact`.
The source range fold is characterized by `initialRows`; each emitted loop
step chooses the exact initial cost, performs three budgeted pushes, releases
the previous tracked row, and advances its state without overflow. The loop
terminates after 45 states. The wrapper allocates and finally releases its
empty seed while preserving every caller-live array and returning a fresh,
owned array equal to the source `initial`.

The large loop step was divided into preparation, one/two/three pushes,
cleanup, and a small invariant. A shared `RangeGuard` lemma handles the
emitted unsigned range exit without expanding the following body. Early
cleanup failures exposed missing nonzero-root assumptions and an unresolved
`br_if` condition; the checked proof makes those conditions explicit. The
entry proof also needed explicit allocator scratch normalization. Failed
runs are retained. `build/logs/drone-initial-3.log` passes all 3,595 jobs;
the loop checks in 3.6 seconds and the final wrapper in 3.1 seconds. All new
axiom audits contain only standard Lean axioms. Full history construction,
route unwinding/reversal, and the compiled compute/safety theorem remain open.

`buildHistory_exact` now verifies the complete compiled history constructor.
The emitted loop reads adjacent terrain floors, detects the last layer,
allocates a seed, executes the checked row solver, appends all 45 parents,
and advances its parameters. Its invariant proves termination, exact source
agreement, preservation of live arrays, fresh nonempty results, and the
remaining allocation/page budget. The emitted ownership trackers remain zero
through this wrapper; its budget conservatively includes every allocation.

The append-call setup hit a 200,000-heartbeat elaboration limit. Splitting
its parameter preparation into a separate lemma resolved that boundary.
An additional checked `owned_root_ne_zero` lemma prevents Lean from expanding
an entire source row computation just to project an allocation's root bound.
The combined step then checks in 3.4 seconds. `NatSub.guard_spec` now exposes
saturated subtraction at an already-evaluated branch, for history reads and
the forthcoming unwind loop. Failed runs remain in `build/logs`.
`build/logs/drone-history-5.log` passes all 3,600 jobs, and every new axiom
audit is standard-only. Route unwinding/reversal and final compiled
compute/safety transfer remain open.
