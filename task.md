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

**The current proof is not yet an end-to-end theorem about `compute` or the
emitted WASM.** Checked components establish segment clearance, component
kinematic bounds, physical-time derivatives, exact tick timing, bounded word
arithmetic, predecessor selection, packed row representation, and cost/parent
invariants. A Bellman invariant connects repeated calls to the actual row
transition to feasible minimum-cost prefixes. The public input validation,
forward/history loops, final reconstruction and output encoding still need to
be connected to those results. Exact-artifact execution is a further boundary.

## Repository and execution environment

- Upstream: https://github.com/jsmorph/leanexe
- Initial inspection: `main` at `a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`.
- Development branch: `drone`. Keep further proof work on this branch.
- Lean: pinned 4.34.0-rc2, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.
- Talos/CodeLib: pinned `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`.
- Mathlib: pinned `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- Wasmtime: 44.0.0; wasm-tools: 1.251.0.
- This session's Node is 24.19.0; the full repository suite pins 24.13.0.
- Read and follow `AGENTS.md`. Every Lean, Lake and compiler invocation must go
  through `tools/leanrun`; never run them concurrently. Use bounded commands.
- The user explicitly authorized running Lean locally in this session, so
  `LEANRUN_LOCAL=1` is authorized here. It keeps the lock, time limit, single
  Lean thread, nice and ionice, but omits systemd cgroup resource controls.
- Current local toolchain, if continuing in this workspace:
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
between waypoints. Local acceptance is proved. The all-stop whole-route witness
still needs to be connected to the public computation.

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
| `SourceChecks.lean` | Aggregate check and printed axiom audit for these source components |

`Planner.layers` is a reference sequence consisting of the actual executable
`initial` and `advance` calls. It is not yet identified with the public
function's forward loop or history. `layers_optimal` must not be represented as
an end-to-end output theorem until those representation and reconstruction
bridges are complete.

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

Current emitted WASM: 14,903 bytes; SHA-256:
`8bda7ff61e5c9771bbe28be59f6c6d6a9303b09a262a5ce4a608912d01d906eb`.
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
used. Locally authorized `LEANRUN_LOCAL=1` and the toolchain selection may be
needed in this container; do not infer that permission for another environment.

The convenience JS driver, JS regression suite, expanded prose documentation,
plots and notebook generator exist in this session's workspace but are not
staged under the user's Lean-code-and-task-only commit instruction. Native Lean
execution and the aggregate proof command above use committed code. Later
commits should continue respecting that file scope unless the user changes it.

## Remaining verification plan, in order

1. **Connect input guards and floor decoding.** Prove accepted terrain bounds,
   floor arithmetic and endpoint/interior conventions for the actual entry.
   Handle empty, singleton, two-point and rejected-input cases explicitly.
2. **Connect forward computation and history.** Identify the public forward
   loop with `Planner.layers`; prove history size, stored parent values and
   indexing. Use the checked `advance_word`, `best_parent`, `advance_bound`
   and Bellman invariant. Introduce named helpers if they make the boundary
   smaller, then check that LeanExe still accepts them and rerun behavior tests.
3. **Whole-route feasibility.** Lift `rest_admitted` to an all-stop route for
   every accepted terrain. Conclude the terminal label is finite and safely
   separated from the unreachable sentinel.
4. **Reconstruction and output contract.** Prove all parent reads in range,
   predecessor traversal reaches the unique initial state, the output has
   length 2n and correct alternating encoding, endpoints are on the ground
   and stopped, every adjacent output pair is an admitted edge, and the
   reconstructed route attains its final DP cost.
5. **Compose full source correctness.** Combine reconstruction, the checked
   Bellman invariant and exact tick timing into minimum-time and secondary-cost
   optimality for the public output. Compose segment clearance, physical-time
   derivatives and component bounds across the flight. Formalize the global
   position/velocity joins; acceleration may jump at waypoints.
6. **Exact WASM semantics.** Freeze the compiled artifact and digest. Prepare
   Talos's decoded program and annotations, prove ABI/array/allocator/loop
   behavior and an actual `Wasm.TerminatesWith` theorem for that artifact.
   Run the repository's independent artifact-proof gates. Do not infer this
   theorem from source proofs or native/WASM agreement. No completed Drone
   case is registered in `proofs/talos/cases.json` at this checkpoint.
7. **Maintain artifacts and checkpoints.** Keep this task record current,
   update the separate project notebook's proof status when milestones land,
   and commit/push verified Lean increments frequently on `drone`. Preserve
   the user's separate source/image outputs. Avoid force pushes and unrelated
   changes; no merge to main is authorized by the branch request.

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
