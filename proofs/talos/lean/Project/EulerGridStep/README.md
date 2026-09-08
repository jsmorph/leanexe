# Checked conservative grid step

[The source](../../../../../LeanExe/Examples/EulerGridStep.lean) accepts a flat
array of conservative triples and uses transmissive end states. A checked
maximum-speed scan supports adaptive time steps. The step reads the old grid
and fills a separate result array: a leading status, followed by six words
per cell (density, momentum, energy, pressure, signal speed, rounded Courant).
Malformed shape or invalid ratio returns `#[1]`. A cell rejection sets status
one and stops; its partially written payload must not be used as a new grid.
The scan uses a named `scanAt` body; its exact execution work is recorded
[separately](../EulerGridScan/README.md). Input reads use total `getD` with zero defaults, which preserves strict calls
to the existing checked-cell function without changing the compiler.

[Model.lean](Model.lean) names the finite scan and fill recurrences.
[Safety.lean](Safety.lean) proves output size, preservation of earlier words,
persistence of rejection, and acceptance of every requested cell computation
when the fill returns status zero. These model theorems use standard logical
axioms. [Payload.lean](Payload.lean) proves exact correspondence of all six
fields and preservation by subsequent cells. [Outputs.lean](Outputs.lean)
transfers accepted state, pressure, speed and Courant safety to the actual
returned array and proves its expected length. [Scan.lean](Scan.lean) proves
that an accepted scan checks every input cell and returns a positive finite
speed bounding all computed cell speeds in decoded-real order. This bounds
the rounded computed speeds; it does not assert a bound on exact-real wave
speeds. Generated-WAT array execution and frozen-byte verification remain
open; the grid-step source case is explicitly registered as incomplete.

The named writeCellField helper isolates the common copying array write;
writeCell calls it six times and releases five intermediate arrays. The
current binary has 8,866 bytes (SHA256
bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297),
reduced from 11,222 bytes without changing any of the 31 regression results.
The separate verified scan remains byte-identical. [Program.lean](Program.lean)
is the exact generated Talos model. [Helpers.lean](Helpers.lean) identifies
field write27, writer34, advance35, entry36 and release40, and proves the
complete checked-cell layout unchanged at functions0–25. Allocation, release,
neighbor reads and the outer fill loop remain to prove.
[FieldMemory.lean](FieldMemory.lean) proves an in-bounds physical word store
realizes the logical array update, preserves a disjoint input array and
leaves all bytes outside that word unchanged. Its
[WordRoundtrip.lean](WordRoundtrip.lean) helper reconstructs the eight stored
bytes with a kernel-checked bit proof. These theorems use only standard
logical axioms; the existing native-decision read-back lemma is not used.

[CopyModel.lean](CopyModel.lean) tracks the copied prefix, both arrays, all
non-memory store fields and bytes outside the destination payload.
[CopyFrame.lean](CopyFrame.lean) handles encoded addresses and loop locals.
[CopyLoop.lean](CopyLoop.lean) proves the complete terminating copy loop under
valid, disjoint source/destination array assumptions, preserving the input
and outside memory. [FieldShape.lean](FieldShape.lean) identifies that exact
loop in generated field writer27. Allocation must still establish those
preconditions. The copy execution theorem uses only standard logical axioms.

[HeaderMemory.lean](HeaderMemory.lean) initializes the array length over
arbitrary existing payload bytes. [FieldTailModel.lean](FieldTailModel.lean)
combines that header, copying and one store into an exact logical update.
[FieldTail.lean](FieldTail.lean) proves the complete generated tail after
allocation, including the returned pointer, unchanged source, other store
fields and bytes outside the destination array. This theorem requires
bounded, disjoint allocated storage and the expected live locals; its
allocator preconditions remain to prove. Its axiom audit is standard.

[HeaderStores.lean](HeaderStores.lean) proves individual metadata stores with
unchanged local frames. [AllocationHeader.lean](AllocationHeader.lean) proves
the six emitted metadata writes and identifies the exact allocator region,
including its localTee instruction.
[FieldAllocationBump.lean](FieldAllocationBump.lean) proves fresh allocation
with an empty free list and enough existing memory: exact metadata, updated
heap top and allocation count, and the resulting local frame. It builds in
7.4s with standard logical axioms. Free-list reuse, ownership transfer and
composition with the field-write tail remain open.

[The focused regression](../../../../../test/euler_grid_step.js) passes 31
compiled cases covering single-cell boundaries, moving uniform states,
two-cell and initial 100-cell Sod grids, malformed shape, bad states, invalid
ratios, CFL rejection and final-state rejection. IR/WAT checks confirm that
the array wrapper reuses one cell-call boundary without additional floating
point arithmetic. A preliminary compiled 100-cell run reaches t=0.2 in 93
steps and matches all 300 final raw state words of the independent host
calculation. That run is runtime evidence; runner proofs and a maintained
scientific data package are still pending.

Run focused checks serially:

```sh
source tools/macos-env.sh
tools/leanrun --timeout 2m lake --no-ansi build LeanExe.Examples.EulerGridStep
tools/leanrun --timeout 2m lake -d proofs/talos/lean --no-ansi build Project.EulerGridStep.Outputs
tools/leanrun --timeout 2m lake -d proofs/talos/lean --no-ansi build Project.EulerGridStep.Scan
node test/euler_grid_step.js
```
