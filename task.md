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

The first milestone is a kernel-checked whole-flight safety theorem for the
current point-mass model, followed by a fresh aggregate source check.  The WASM
execution proof follows that result.  Expansion of the model follows an
established safety baseline and discussion with the user.  The user declined
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
transfer to the global coordinate functions.  The next source task is to
assemble these results into one public whole-flight safety statement.  Agreement
between compiled WASM execution and the proved source computation remains open.

## Safety status and remaining risks

### Current coverage and evidence

The reviewed source revision is `41a97a6e80ac90e503e981ecd7052c2b489619e9`,
which matched `origin/drone` on 2026-09-25.  The review inspected source,
theorem statements, tooling, and the checkpoint record.  Fresh Lean and runtime
checks in the current checkout remain outstanding.  The preceding checkpoints
record successful aggregate source builds with standard Lean axioms.

| Property | Current proof coverage |
|---|---|
| Clearance | `Safety.compute_segment_clearance` covers every normalized segment time.  `Trajectory.compute_global_clearance` transfers this result to global altitude on each cumulative-time interval.  The corridor has 100-unit interior clearance and the specified takeoff/landing ramps. |
| Speed | `Trajectory.compute_global_speed` bounds horizontal speed between 0 and 20 and vertical speed magnitude by 20 on every flight interval. |
| Acceleration | `Safety.compute_segment_maneuverable` bounds horizontal acceleration magnitude by 1 and vertical acceleration magnitude by 4.  `Kinematics` identifies these expressions as physical-time derivatives within each primitive. |
| Continuity | `Trajectory.compute_joins` and `compute_global_smooth` establish matching positions and velocities and continuous global velocity.  Acceleration may jump at joins. |
| Interval coverage | `compute_global_segment` identifies all four global coordinates with their local primitives.  `compute_global_cover` covers every time in a nontrivial finite flight.  A singleton terrain gives a constant path. |
| Endpoints | `Output.compute_endpoints` proves that the returned route starts and finishes on the terrain, stopped.  The local primitive endpoint lemmas connect waypoint words to position and velocity. |
| Feasibility and input handling | `Output.compute_correct` returns an encoded feasible route for every accepted nonempty terrain, with exactly two words per point.  Separate theorems cover empty and rejected inputs. |

The recorded runtime tests cover 48 WASM trajectories, 12 native comparisons,
and six exhaustive short-route optima, together with clearance, kinematic,
input-boundary, and translation checks.  Their driver and logs were excluded
from the branch under the existing commit scope.  These results are historical
test evidence.  The source proofs quantify over all accepted inputs within
the stated bounds.

### Remaining risks

Proof composition: the safety results span several theorems.  The public
whole-flight statement must express clearance against the corridor evaluated
at the global horizontal position, connect acceleration bounds to derivatives
of global velocity inside each segment, and establish the global path's
departure and arrival conditions.  Interval coverage must transfer the
segment-indexed bounds to every time in the finite flight.  Existing lemmas
supply the components.  Construction and a fresh Lean check of the combined
statement remain outstanding.  Acceleration bounds apply between joins, with
the existing one-sided primitive bounds at a join.

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

The machine-specific settings below describe the original proof-development
workspace.  The review checkout lacked the compiler executable and materialized
Talos dependency at inspection.

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

- [ ] Check the existing source baseline in the current environment with the
  pinned toolchain and required resource limits.  Run
  `Project.Drone.SourceChecks` and review its axiom audit.  Distinguish dependency
  setup from proof failures and preserve diagnostics.
- [ ] Complete the public whole-flight safety theorem by composing the
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
