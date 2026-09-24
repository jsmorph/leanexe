# Checked conservative grid step

The [grid-step source](../../../../../LeanExe/Examples/EulerGridStep.lean) accepts a flat array of conservative triples and uses transmissive boundaries.  It returns a status word followed by six words per cell: density, momentum, energy, pressure, signal speed, and rounded Courant.  Malformed shape or an invalid ratio returns `#[1]`.  A rejected cell sets status one and stops the loop.  The runner accepts the payload as a new grid only when status is zero.

## Execution and safety

The [public specification](Spec.lean) proves termination and exact output for the [current generated program](Program.lean).  Its assumptions are the input representation, empty free list, typed allocator counters, page bounds, and disjoint arena in [the entry predicate](GridEntryReady.lean).  For `N` cells, the arena budget reserves `N + 6` objects of `64 + 48N` bytes each.  The current implementation reuses outputs after the first two accepted cells.

| Declaration | Result |
|-------------|--------|
| `Spec.stepCheckedBits_exact` | Exact represented output of `Model.stepCheckedBits` for every permitted input and ratio. |
| `Spec.stepCheckedBits_wat_safe` | Exact execution plus finite, admissible accepted cell states and rounded Courant at most one half. |
| `Spec.reset_exact` | Exact reset of the six allocator globals with memory preserved. |

The complete current specification passed on 2026-09-24.  The execution and safety proofs use the standard logical axioms.  The [model](Model.lean), [payload correspondence](Payload.lean), and [output safety](Outputs.lean) connect the cell recurrence to all six returned fields.  The [separate maximum-speed scan](../EulerGridScan/README.md) bounds rounded computed speeds and supports adaptive time steps.

### Buffer lifecycle

Slot zero holds the initialized output and remains protected until the final return.  Each accepted cell calls the field writer six times and releases five intermediate arrays.  The outer loop reads the previous output's status, then releases that output when it differs from both slot zero and the new result.

| Step | Field storage | Heap position after the step | Outer-loop release |
|------|---------------|------------------------------|--------------------|
| Initialization | Fresh slot zero. | Slot 1. | None. |
| First accepted cell | Six fresh objects. | Slot 7. | Slot zero remains protected. |
| Second accepted cell | Five reused objects and one fresh object. | Slot 8. | Previous output joins the five freed intermediates. |
| Later accepted cell | Six reused objects. | Slot 8. | Previous output completes the six-node free list. |
| First rejected cell | One fresh object. | Slot 2. | Slot zero remains protected. |
| Later rejected cell | One reused object. | Previous heap position. | Previous output joins the remaining free list. |
| Return | Current output remains owned. | Unchanged. | Slot zero joins the free list. |

The [rotating-pool lemmas](RotatingPool.lean) prove slot bounds, separation, and pool rotation.  The [rotating arena state](RotatingArenaState.lean) covers the five-reuse/one-fresh second cell and the six-reuse later cells.  [Accepted advance](AdvanceRotatingAccepted.lean) and [rejected advance](AdvanceRotatingRejected.lean) retain the old output until the loop finishes reading it.

The [framed previous-output release](ReleasePreviousOutput.lean), [grid release composition](GridRotatingRelease.lean), and [release continuation](GridAdvanceFinish.lean) establish the next storage state while preserving the input and protected initial output.  The [loop storage invariant](GridLoopStorage.lean) distinguishes initialization, accepted output, and rejected output.  The [loop theorem](GridLoop.lean) covers every cell and the final condition-only iteration.  [Final geometry](GridFinalGeometry.lean) and [final release](GridFinalRelease.lean) preserve the returned output while freeing slot zero.

### Proof composition

| Modules | Responsibility |
|---------|----------------|
| [Field memory](FieldMemory.lean), [copy loop](CopyLoop.lean), and [field execution](FieldExecution.lean) | Exact cloning and indexed writes, termination, address bounds, and preservation of separate arrays. |
| [Allocation choice](AllocationChoice.lean), [free chain](FreeChain.lean), and [buffer state](BufferState.lean) | Fresh/reused allocation, owned metadata, free-list links, counters, and page limits. |
| [Fresh writer](FreshWriterFramed.lean), [mixed writer](MixedWriterFramed.lean), and [reused writer](ReusedWriterFramed.lean) | Six writes and five intermediate releases under each allocation schedule. |
| [Neighbor reads](AdvanceReads.lean) and [advance execution](AdvanceExecution.lean) | Boundary clamping, nine input reads, checked-cell execution, and output writing. |
| [Initial arena](InitialArena.lean), [entry guards](EntryGuards.lean), and [rejected entry](RejectedEntryExecution.lean) | Dimensions, fresh allocation, zero fill, and malformed-entry behavior. |
| [Grid setup](GridSetup.lean), [loop frame](GridLoopFrame.lean), and [return staging](GridFinish.lean) | The emitted 52-local entry function and its release guards. |
| [Valid branch](GridValidBody.lean) and [complete export](GridExecution.lean) | Composition into the public step theorem. |

The earlier growing-arena lemmas remain checked support for the first-cell and mixed allocation cases.  The current outer loop uses the rotating arena invariant.

## Frozen binary

The historical package contains 8,866 bytes with SHA-256 `bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297`.  [Embedded bytes](ArtifactBytes.lean), [decoding](ArtifactDecode.lean), [validation](ArtifactValidation.lean), and [translation](ArtifactTranslation.lean) establish its binary identity and execution model.  Its `Frozen` proof modules retain the allocation behavior of that binary.  Rechecking this historical package against the updated shared verifier remains part of the current release work.

Decoder-cache witnesses use the repository's native-decision policy.  Execution, safety, and reset proofs use the standard logical axioms.  The [artifact format](../../../../../docs/artifact-format.md) defines the independent package boundary.

## Repeated steps and tests

The [repeated-step recurrence](Runner.lean) projects the three conservative fields and rejects a failed step before copying its partial output.  Its induction theorem records each IEEE output, pressure, speed, Courant value, and accepted conservative grid.  [Repeated execution](RunnerExecution.lean) transfers the step theorem to stores satisfying `GridEntryReady`.  Host time selection, memory preparation, scientific validation, and presentation remain outside the execution theorem.  The [scientific dataset](../../../../../data/euler-sod-v2/README.md) records the Sod experiment.

The [compiled tests](../../../../../test/euler_grid_step.js) cover boundaries, uniform states, Sod grids, malformed inputs, invalid ratios, CFL rejection, and final-state rejection.  Repository verification commands run serially:

```sh
tools/talos-proof.js check euler_grid_step
node test/euler_grid_step.js
```
