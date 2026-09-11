# Complete Riemann solver proof

## Authorized calculation

The user authorized the complete development after reviewing the design.
One Lean program, compiled by LeanExe, takes a runtime grid size and runs
in one local Wasmtime process on one thread.  Both the Lean source and
the exact generated WASM require checked proofs against the numerical
specification.  Complete those proofs before the production calculations.
Then run 192 by 192, plot its final density and pressure, run 800 by 800,
and plot its final density and pressure, in that order.  Preserve the
earlier datasets and figures.

The unit square has interfaces at x = y = 0.8 and final time 0.8.
The pressure, density, x-velocity, and y-velocity are:

| Quadrant | Pressure | Density | x-velocity | y-velocity |
|----------|----------|---------|------------|------------|
| Top left | 0.3 | 0.5323 | 1.206 | 0 |
| Top right | 1.5 | 1.5 | 0 | 0 |
| Bottom left | 0.029 | 0.138 | 1.206 | 1.206 |
| Bottom right | 0.3 | 0.5323 | 0 | 1.206 |

Keep gamma 1.4, conservative area averages for intersected cells,
first-order Rusanov updates, x-then-y splitting, clamped transmissive
boundaries, target CFL 0.4, and the rounded CFL acceptance ceiling 0.5.
Preserve the floating-point association of the existing calculation.
The numerical executable owns initialization, reductions, timestep
selection, retries, all array traversal, stopping, and pressure extraction.
The host invokes the module and saves returned words for plotting.

## Proof obligations

The current cell artifact theorem proves exact terminating cell execution
and accepted-state safety.  Its mathematical sweep and finite-run theorems
do not prove executable grid or time control.  The earlier 192-grid host
calculation remains a comparison dataset with that recorded scope.

The user approved using Talos's five `Wasm.IEEE64` arithmetic definitions
in the source and compiling their calls to the corresponding floating-point
instructions.  Source and exact-WASM proofs can share these definitions.
The five mappings and a composed division/square-root expression pass
source comparisons and byte-identity tests against the existing wrappers.
The complete source and exact-WASM proofs remain open.

Array updates copy the array.  Each sweep must construct its result in
linear time and reclaim obsolete storage.  The memory proof must account
for temporary arrays, allocator metadata, retained references, and free
storage, with a bound independent of elapsed timestep count.  Three arrays
of four binary64 fields require 58.6 MiB at 800 by 800.  Separate final
density and pressure arrays require 9.8 MiB.  These figures count payloads
only and do not establish the complete peak-memory bound.

Prove successful completion at the requested final time, with all returned
cells equal to the specified numerical recurrence.  A theorem conditional
on successful intermediate steps leaves the success obligation open.
The existing host's 10,000-step and 24-attempt limits are historical bounds,
not evidence that the requested runs satisfy them.

## Work order

- [x] Prove the ordered index array, clamped-neighbor bounds and coordinate correspondence, and interface-fraction bounds.
- [x] Prove the four conservative states and admissibility of all 36 rounded cell-average combinations.
- [x] Test the generated grid-helper WASM, including the complete 800-grid index array.
- [ ] Define the numerical recurrence, accepted sizes, and output layout.
- [x] Add and test the approved compiler mappings for Talos's formal arithmetic definitions.
- [ ] Implement and prove linear-time initialization and directional traversal.
- [ ] Prove allocator reuse and the complete memory bound.
- [ ] Implement and prove timestep selection, retry, and final-time control.
- [ ] Prove source correctness and successful completion for the supported inputs.
- [ ] Freeze the generated WASM and check its complete execution theorem and axiom audit.
- [ ] Run 192 by 192 and save its final result.
- [ ] Render and inspect the 192-grid density and pressure figure.
- [ ] Run 800 by 800 and save its final result.
- [ ] Render and inspect the 800-grid density and pressure figure.

Use the local leanrunner limits for builds, proof checks, and runtime work.
The user selected local execution.  A change to remote or parallel
execution requires discussion.  The complete proof remains unfinished.

## Current checkpoint

[Grid source](../LeanExe/Examples/EulerRiemann/Grid.lean) accepts sizes from
2 through 800.  Its tail-recursive array construction passes the source
sequence proof and compiler ownership report.  The report supplies no
fresh-result summary or emitted releases for that recursive helper.
Its allocations require a bounded initialization argument in the final
WASM proof.

[Initial admissibility](../proofs/talos/lean/Project/EulerRiemann/Initial.lean)
uses the specified primitive words and rounded conservative averages.
All completed source/model theorem audits contain only the accepted
standard logical axioms.  The 48 [grid tests](../test/euler_riemann_grid.js)
pass.  Production execution remains behind the complete proof gate.

The user approved the compiler arithmetic mappings.  Their focused tests
pass, and the compiler-wide checks are in progress.
