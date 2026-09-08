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
complete checked-cell layout unchanged at functions0–25. Multi-buffer ownership
composition, neighbor reads and the outer fill loop remain to prove.
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
loop in generated field writer27. The complete field theorem below establishes those
preconditions from explicit allocation bounds and separation. The copy execution theorem uses only standard logical axioms.

[HeaderMemory.lean](HeaderMemory.lean) initializes the array length over
arbitrary existing payload bytes. [FieldTailModel.lean](FieldTailModel.lean)
combines that header, copying and one store into an exact logical update.
[FieldTail.lean](FieldTail.lean) proves the complete generated tail after
allocation, including the returned pointer, unchanged source, other store
fields and bytes outside the destination array. This theorem requires
bounded, disjoint allocated storage and the expected live locals; its
allocator preconditions are discharged by the complete field theorem below. Its axiom audit is standard.

[HeaderStores.lean](HeaderStores.lean) proves individual metadata stores with
unchanged local frames. [AllocationHeader.lean](AllocationHeader.lean) proves
the six emitted metadata writes and identifies the exact allocator region,
including its localTee instruction.
[FieldAllocationBump.lean](FieldAllocationBump.lean) proves fresh allocation
with an empty free list and enough existing memory: exact metadata, updated
heap top and allocation count, and the resulting local frame. It builds in
7.4s with standard logical axioms.

[ReuseHit.lean](ReuseHit.lean) proves the successful first-candidate branch.
[ReuseSearch.lean](ReuseSearch.lean) reads that candidate and proves the
terminating search with a one-to-zero measure.
[FieldAllocationReuse.lean](FieldAllocationReuse.lean) composes the complete
emitted allocator path when the free-list head has sufficient capacity: it
unlinks and initializes that block, skips bump allocation, increments the
allocation counter and returns the exact local frame. This build takes3.0s
with standard logical axioms. The complete field theorem composes this path
with the tail; ownership across multiple intermediate buffers remains open.

[ArrayFrame.lean](ArrayFrame.lean) transfers represented arrays across
byte-preserving store changes. [AllocationMemory.lean](AllocationMemory.lean)
proves exact owned-header values, the 48-byte metadata footprint, preservation
of disjoint arrays, and preservation of metadata by field writes.
[Release.lean](Release.lean) applies the existing scalar-array runtime proof
at function40: an owned array is freed with exact memory writes, free-list
update and release/free counters. These checks take under four seconds each
and audit to standard logical axioms. Composition of these facts across the
writer and its intermediate buffers remains pending.

[FieldIndexing.lean](FieldIndexing.lean) proves checked field-offset guards
and exact scalar-array byte capacity for bounded lengths.
[FieldPrefix.lean](FieldPrefix.lean) proves the first44 emitted instructions,
including zero/nonzero index paths, checked additions, the length-header read
and the true bounds test, with an exact20-local frame.
[FieldCapacity.lean](FieldCapacity.lean) proves the next22 instructions
inside the accepted branch, setting copy count and normalized capacity.
These builds take6.8s and3.8s respectively and audit to standard logical
axioms. The complete field theorem below joins these regions.

[AllocationPost.lean](AllocationPost.lean) connects both allocator memory
models to represented input, initialized owned metadata, destination bounds
and the object footprint. [AllocationChoice.lean](AllocationChoice.lean)
provides a common exact execution theorem with explicit capacity, availability
and separation conditions. [FieldFrame.lean](FieldFrame.lean) proves the live
local-variable conditions required by the copy/update tail for both paths.
These focused builds take3.5–4.0s and use only standard logical axioms.
The complete field theorem below joins these contracts; the multi-buffer
arena invariant remains open.

[FieldBody.lean](FieldBody.lean) composes the complete accepted branch.
[FieldExecution.lean](FieldExecution.lean) proves exact terminating execution
of generated function27, including checked index setup and both returned
pointer values. It realizes the logical array update, preserves the input,
keeps the new result metadata owned, preserves page count and all memory
outside the new object's metadata and used array bytes. Allocation globals
and other store fields are framed by the exact chosen allocator model.
The theorem assumes an in-bounds field, sufficient existing memory, explicit
source/destination separation and either an empty free list for fresh
allocation or a sufficient first free block. Builds take3.5s and3.9s, with
only standard logical axioms. Composition across six field writes and five
intermediate releases, rejection, neighbor reads and the grid loop remains.

[ObjectFrame.lean](ObjectFrame.lean) strengthens separation to include both
runtime headers and proves that field writes preserve other live buffers.
[ReleaseMemory.lean](ReleaseMemory.lean) proves exact reusable metadata after
release, unchanged payload/page count and preservation of separate buffers.
[FreeFrame.lean](FreeFrame.lean) preserves existing free-list nodes across
field writes and release. [ReleaseFramed.lean](ReleaseFramed.lean) attaches
these facts to exact generated release function40. Builds take3.5–3.8s with
standard logical axioms. These facts support the upcoming multi-buffer
invariant; they do not yet prove the complete cell writer or grid loop.

[FreeChain.lean](FreeChain.lean) represents finite, uniformly sized free
buffers with physical bounds and exact next links. Its first node establishes
the actual allocator preconditions. [FreeChainExecution.lean](FreeChainExecution.lean)
proves that a full field write consumes one node and that release adds a node,
with exact runtime-global updates and preserved remaining chain.
[LiveBuffers.lean](LiveBuffers.lean) preserves lists of owned intermediate
arrays and adds the exact updated clone. These builds take3.6–3.9s with
standard logical axioms. Pairwise buffer separation remains explicit; the
complete cell-writer and grid arena invariants remain pending.

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
