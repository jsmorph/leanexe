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
storage, with a bound independent of elapsed timestep count.  The current
cell representation stores seven words: index, four conserved fields,
pressure, and status.  Three such arrays require 102.5 MiB at 800 by 800.
Separate final
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
- [x] Define the numerical recurrence, accepted sizes, and output layout.
- [x] Add and test the approved compiler mappings for Talos's formal arithmetic definitions.
- [ ] Implement and prove linear-time initialization and directional traversal.
- [x] Prove source-array initialization, accepted-sweep correspondence, and the wave-speed reduction.
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
sequence proof and compiler ownership report.  Its allocations require
a bounded initialization argument in the final WASM proof.

[Initial admissibility](../proofs/talos/lean/Project/EulerRiemann/Initial.lean)
uses the specified primitive words and rounded conservative averages.
All completed source/model theorem audits contain only the accepted
standard logical axioms.  The 62 [grid tests](../test/euler_riemann_grid.js)
pass, including full-word initialization, split-step, and output comparisons
at sizes 2, 3, and 5, and complete runs at sizes 2 and 3.  The complete runs
reach time 0.8 with status zero and match every formal source output word.
Production execution remains behind the complete proof gate.

The source-array proofs connect initialization and accepted directional
steps to the existing functional-grid recurrence.  The reduction proof
identifies acceptance of every directional thermodynamic calculation and
the maximum raw speed word.  Grid-size encoding and strictly decreasing
remaining-time word bounds also pass their focused proofs.

[Control](../proofs/talos/lean/Project/EulerRiemann/Control.lean) implements
whole-step retries with halved timesteps and advances after acceptance.
The checked source theorems connect accepted retries to the numerical
recurrence, preserve grid indices through time control, and show that
status zero implies final time 0.8.  The decreasing remaining-time word
measure proves that the outer-loop fuel cannot exhaust.  Successful
completion remains open.
[The source trace proof](../proofs/talos/lean/Project/EulerRiemann/ControlTrace.lean)
connects every supported-size result to accepted functional Rusanov steps
from the specified initial grid, with valid rounded time advancement at
each step.  It includes the accepted prefix retained after a failure.
The trace length is bounded by the increase in the raw time word.
[The generated execution model](../proofs/talos/lean/Project/EulerRiemann/Program.lean)
now comes from the registered complete source entry.  The artifact driver
loads its checked declarations from the proof workspace.  The generated
21,386-byte module matches the artifact used by the passing small-grid
tests.  All four runtime-definition checks pass.  The
[thermodynamic execution proof](../proofs/talos/lean/Project/EulerRiemann/ExecutionSide.lean)
transfers the existing fourteen-function theorem after checking every
renamed definition.  Its axiom audit uses only the accepted standard axioms.
The scalar flux and conservative-update regions, their forwarding
functions, the complete two-dimensional flux, and the cell update now
have all-input execution theorems with exact result words and complete
store preservation.  The source scan callback's execution theorem covers
both directional side calls, status accumulation, and maximum selection.
All focused builds and axiom audits pass.
[The complete scan proof](../proofs/talos/lean/Project/EulerRiemann/ExecutionScan.lean)
now covers entry setup, every seven-field read, the callback, loop
termination, and the returned status/speed pair.  It preserves the complete
store and agrees with the source fold for every represented grid.
The memory representation proves address bounds and preservation under
changes outside the grid.
[The sweep callback proof](../proofs/talos/lean/Project/EulerRiemann/ExecutionUpdateCell.lean)
composes checked clamped-neighbor arithmetic, eight bounded field reads,
momentum orientation, and the numerical cell evaluator.  It covers every
valid cell index for sizes 2 through 800, with arbitrary cell words and
ratio, and preserves the store.
[The cell-write proof](../proofs/talos/lean/Project/EulerRiemann/MemoryWriteCell.lean)
extends the destination prefix through all seven fields and preserves a
disjoint source grid.  Its shared read/write round-trip theorem uses
kernel-checked bit extensionality.  All audits contain only the accepted
standard axioms.
[The sweep-loop proof](../proofs/talos/lean/Project/EulerRiemann/SweepLoop.lean)
composes the callback and writes into a terminating traversal.  It proves
source agreement for every indexed grid at supported sizes and preserves
all store components outside the allocated destination bytes.  Allocator
setup and reuse remain open.
[The allocator-growth proof](../proofs/talos/lean/Project/EulerRiemann/AllocationGrowth.lean)
matches the generated growth region and covers both the growth and
no-growth branches within the runtime memory cap.  It preserves existing
grid representations.
[The allocation-header proof](../proofs/talos/lean/Project/EulerRiemann/AllocationHeader.lean)
matches both generated header regions and proves the bump header's
bounded stores, metadata values, and preservation of disjoint grids.
Its shared proofs use only the accepted standard axioms.
[The bump-allocation proof](../proofs/talos/lean/Project/EulerRiemann/AllocationBump.lean)
composes heap-address preparation, conditional growth, heap-top and root
assignment, and metadata stores into the complete generated bump branch.
It proves exact page and global updates and preserves disjoint grids.
[The selected-node reuse proof](../proofs/talos/lean/Project/EulerRiemann/AllocationReuse.lean)
covers head and interior unlinking, metadata stores, and returned-pointer
assignment.  The reused memory model and free-list state lemmas now have
standard-only audits in a separate shared module.
[The search-fragment proofs](../proofs/talos/lean/Project/EulerRiemann/AllocationSearchRead.lean)
cover bounded capacity/next reads and pointer advancement.
[The no-fit search proof](../proofs/talos/lean/Project/EulerRiemann/AllocationSearchNone.lean)
proves termination after all undersized nodes, store preservation, and a
zero selected pointer.
[The fitting search proof](../proofs/talos/lean/Project/EulerRiemann/AllocationSearchFit.lean)
proves termination, first-fit selection, bounded predecessor writes,
unlinking, metadata construction, and the returned root.  Both execution
audits contain only the accepted standard logical axioms.
[The allocator composition](../proofs/talos/lean/Project/EulerRiemann/AllocationExecute.lean)
covers search initialization, both outcomes, conditional bump allocation,
and counter advancement.  It requires address and runtime-cap bounds
when no node fits.
[The capacity proof](../proofs/talos/lean/Project/EulerRiemann/AllocationCapacity.lean)
matches the local-length prefix and gives exactly 8 + 56 times the cell
count in bytes for supported grids.
[Allocation bounds](../proofs/talos/lean/Project/EulerRiemann/AllocationBounds.lean)
establish sufficient capacity, root and payload bounds, fresh metadata,
and page-count bounds.
[Allocation preservation](../proofs/talos/lean/Project/EulerRiemann/AllocationPreserve.lean)
proves the source grid survives allocation and the destination is disjoint
when free nodes and the new heap region are separated from the source.
Its shared byte-frame theorem covers predecessor unlinking and all header
writes.  Free-list representation survives byte-identical page growth.
[The complete sweep execution](../proofs/talos/lean/Project/EulerRiemann/ExecutionSweep.lean)
composes entry, capacity calculation, allocation, destination setup, the
terminating traversal, and the returned owner/root pair.  Its result
agrees with the source sweep, preserves the input grid, and confines loop
writes to the destination payload.  The theorem keeps the represented
free-list separation and available heap/runtime-cap premises explicit.
The complete solver's ownership and peak-memory invariants remain open.
[The fixed-array release proof](../proofs/talos/lean/Project/EulerRiemann/ExecutionRelease.lean)
gives the exact store after a refcount-one grid is freed.  The strengthened
shared runtime theorem preserves all components outside memory and
globals, including runtime memory limits.  Its existing public theorem
retains the same statement through projection.
[Release memory preservation](../proofs/talos/lean/Project/EulerRiemann/ReleaseMemory.lean)
proves bytes outside the freed header unchanged and inserts the buffer
into the represented free list using kernel-checked read/write facts.
[Allocation state](../proofs/talos/lean/Project/EulerRiemann/AllocationState.lean)
identifies the remaining nodes, preserves their representation, and
proves strict address bounds and separation from the selected buffer.
[Sweep resources](../proofs/talos/lean/Project/EulerRiemann/SweepResources.lean)
composes allocation, length installation, and the loop write frame to
preserve fresh destination metadata, full-capacity bounds, and the free
list.
[Allocator globals](../proofs/talos/lean/Project/EulerRiemann/AllocationGlobals.lean)
identify the heap top and free-list head, preserve other globals and
runtime memory caps, and place allocated and remaining free buffers
below the resulting top.
[Owned-source preservation](../proofs/talos/lean/Project/EulerRiemann/AllocationFrame.lean)
retains the source's complete region through allocation and its fresh
header through subsequent sweep writes.  The solver's persistent
ownership and peak memory bound still require composition across calls.
[The acceptance scan](../proofs/talos/lean/Project/EulerRiemann/ExecutionAccepted.lean)
proves exact execution of the array's all-zero-status predicate.  Its
loop covers every bounded seven-word cell read, early rejection at a
nonzero status, termination, the empty array, and complete store
preservation.  This result selects the second sweep and retry branches
in the generated controller.
[The sweep ownership theorem](../proofs/talos/lean/Project/EulerRiemann/SweepOwned.lean)
returns the updated heap, the preserved source, a fresh destination,
mutual separation, page-count bounds, and the unchanged runtime cap.
The heap and owned-grid relations preserve other live grids through the
same allocation and writes, including the original grid retained for
retry.  Their allocation and release transformations compose the six
runtime globals with represented free-list and buffer state.
[The complete timestep](../proofs/talos/lean/Project/EulerRiemann/ExecutionStep.lean)
composes the first sweep, acceptance test, conditional second sweep,
and intermediate release.  It returns the source step's represented
grid and resulting heap, preserves runtime limits, and preserves every
live input grid with separation from the result.  The theorem retains
explicit space and runtime-cap bounds for both possible allocations.
The full solver's peak-memory invariant must discharge those premises.
[Heap reservations](../proofs/talos/lean/Project/EulerRiemann/HeapReserve.lean)
count sufficiently large free buffers and bound the bytes needed for
the requested allocations beyond those buffers.  Allocation consumes
one reservation, and release restores one.
[The reserved timestep](../proofs/talos/lean/Project/EulerRiemann/StepReserve.lean)
derives both allocation bounds, returns one fewer reservation, and
restores the initial reservation count when its result is released.
The initializer's byte bound and full control composition remain open.
[The time guard](../proofs/talos/lean/Project/EulerRiemann/ExecutionTimeGuard.lean),
[grid spacing](../proofs/talos/lean/Project/EulerRiemann/ExecutionSpacing.lean),
and [CFL proposal](../proofs/talos/lean/Project/EulerRiemann/ExecutionProposal.lean)
now have exact execution proofs.  They cover all short-circuit guards,
the ten small-natural exponent intervals, rounded binary64 operations,
both minimum branches, full store preservation, and caller operands
retained below nested calls.  Successful retry and final-time completion
still require the controller and numerical progress proofs.
[The retry trial](../proofs/talos/lean/Project/EulerRiemann/RetryTrial.lean)
composes spacing, the reserved timestep, and acceptance while preserving
the resulting heap and live-input facts for its continuation.
[The retry branches](../proofs/talos/lean/Project/EulerRiemann/RetryBranches.lean)
prove accepted-result assignment and rejected-trial release, rounded
halving, owner tracking, parameter replacement, and fuel decrement.
These regions compose through the retry invariant and termination proof.
[The retry frame](../proofs/talos/lean/Project/EulerRiemann/RetryFrame.lean)
preserves the parameters, tracker, result fields, completion flag, and
frame size through each region and proves strict fuel decrease.
[Guard execution](../proofs/talos/lean/Project/EulerRiemann/RetryGuard.lean)
covers active entry, completed exit, and the validity-call prefix.
[Retry resources](../proofs/talos/lean/Project/EulerRiemann/RetryResources.lean)
preserve every original live grid through a timestep and trial release.
The combined invariant separates active and completed frames.
[The retry iteration](../proofs/talos/lean/Project/EulerRiemann/RetryIteration.lean)
preserves that invariant and strictly decreases its measure at each
back edge.  [The complete retry function](../proofs/talos/lean/Project/EulerRiemann/ExecutionRetry.lean)
composes entry, terminating loop, completed exit, and four returned
words.  It returns the source result's represented grid, preserves
original live grids and runtime limits, and consumes one reservation.
The theorem requires source retry success.  The final solver proof
must discharge that premise and establish completion at time 0.8.
[The outer-loop source decomposition](../proofs/talos/lean/Project/EulerRiemann/ControlAdvanceStep.lean)
derives successful scan/retry premises and bounded retry-fuel encoding
from a successful nonterminal source advance.
[The scan and trial regions](../proofs/talos/lean/Project/EulerRiemann/AdvanceTrial.lean)
compose the generated reduction, proposal, checked increment, retry,
and result placement.
[Frame preservation and guards](../proofs/talos/lean/Project/EulerRiemann/AdvanceGuard.lean)
cover active/completed entry, end-time lookup, and terminal assignment.
[Grid replacement](../proofs/talos/lean/Project/EulerRiemann/AdvanceContinue.lean)
preserves a borrowed initial grid or releases a tracked current grid,
then advances rounded time, replaces parameters and tracking, and
decrements fuel.  The [outer-loop invariant](../proofs/talos/lean/Project/EulerRiemann/AdvanceInvariant.lean)
tracks borrowed or newly allocated grids, live-grid separation, source
agreement, and reservations for subsequent trials.  The iteration
preserves this invariant and decreases a natural measure.  The
[complete advance function](../proofs/talos/lean/Project/EulerRiemann/ExecutionAdvance.lean)
composes entry, terminating loop, and the four returned words under
explicit source-success and sufficient-fuel premises.  Both retry and
advance now use the shared `BlockLoop.program_spec` composition theorem.
All public audits use standard axioms.
Initialization's [scalar helpers](../proofs/talos/lean/Project/EulerRiemann/ExecutionInitialScalars.lean)
now have exact execution proofs for the six fifth weights and arbitrary
weighted/conservative input words.  The four quadrant constructors and
[weighted initializer](../proofs/talos/lean/Project/EulerRiemann/ExecutionInitialWeighted.lean)
compose the recorded calls and preserve the full store.  A compact
suffix theorem separates the weighted initializer's 22-call proof.
Cell indexing, grow/extract traversal, and initialization allocation
remain open.
Compiler annotation generation now runs through the case's artifact
command.  The [shared fuel/completion guard](../proofs/talos/lean/Project/ProofKit/FuelGuard.lean)
and [LTG entry](../ltg/entries/fuel-completion-guard/README.md)
replace the four retry/advance guard derivations.  Generated equalities
also match the initializer guard.  Review each remaining proof attempt
against its compiler evidence and retrieved support, and record reusable
results and failed applications in the journal.
[Output](../proofs/talos/lean/Project/EulerRiemann/Output.lean) returns status,
time, two dimensions, and contiguous density and pressure blocks.  Its
layout and maximum length of 1,280,004 words have checked source proofs.
The complete control module compiles.  The compiler now preserves the
continuing retry branch's explicit release and tracks the fresh retry
result between timesteps.  The generated time loop releases its previous
tracked owner before replacement.  The complete exact-WASM proof remains
open.  The source safety theorem preserves cell bounds and Euler
admissibility through control, including a failure result that retains
the last accepted grid.

Compiler diagnostics found repeated ordinary-callee expansion during
recursive-expression discovery.  The revised pass scans each ordinary
function at its declaration boundary.  The step now compiles.  Its
ownership report recognizes fresh sweep results and identified an
unreleased intermediate grid.  The source release now passes the checker
and numerical tests.  Array-helper expression lowering binds both owner
and data-pointer results.  The focused ownership tests pass, including
rejection of releases through aliases and nested arrays.

Internal Nat-tail helpers now use the existing per-iteration owner
tracking.  Tests cover replacement, retention, and preservation of the
caller's initial array.  The explicit-release checker recognizes direct
maps and concatenations while preserving rejection of retained nested
roots.  All 28 focused ownership and array-call tests pass.  Nat-tail lets
now share their materialized value, preserve explicit releases, and pass
ownership facts to continuations.  Fresh-result analysis accounts for
zero-initialized locals and computes loop facts to a fixed point.  Map
callbacks materialize multi-field results once per element.  Explicit
source bindings share neighbor indices, neighbor states, and cell inputs.
The emitted sweep calls its update helper once per cell.  The complete
memory and runtime bounds remain open.

The compiler-wide execution gate has a stale release-input record, and
the aggregate proof build timed out after matching all 37 generated
caches.  Preserve that evidence and divide the aggregate build before
retrying.  These gates remain open.
