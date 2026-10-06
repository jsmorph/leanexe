# Smalltalk VM and GC proof work

Status recorded on 2026-10-06 UTC, before committing this document.
Repository: `jsmorph/leanexe`. Branch: `smalltalk-vm`, based on `deslop`.
The local and remote heads at this checkpoint are
`cb1f5bc9cdd8d293fb4ceee891e17034b5b349c1`.

The task is to prove the actual Lean VM and collector correct, keep the
implementation simple, run the compiled WASM, and commit and push checked
increments. The task is unfinished. No WASM compilation proof is being added.

## Working rules

- Give a concrete progress update every 30–45 seconds while working.
- State what passed, what failed, what remains, and which commit was pushed.
- Check each proof increment, document its assumptions, commit, and push.
- Keep all Lean and Lake processes serial and run them through `tools/leanrun`.
- Local Lean execution is authorized. Do not add Rust or another runtime.
- After a proof reaches a limit, split it or check a useful helper before
  trying it again. Do not raise limits to conceal the problem.
- Keep documentation exact. A conditional helper theorem is not a proof of
  the entire VM. Execution tests are not a proof of emitted WASM correctness.

## Executable code

`LeanExe/Smalltalk/Arena.lean` implements the arena, allocation, reservation,
initialization, and nonmoving mark-and-sweep collector.
`LeanExe/Smalltalk/Runtime.lean` implements instruction execution, calls,
returns, method lookup, program validation, boot, and fuel-limited execution.
Neither file has changed during the proof increments described here.

The arena has 24 registers, eight-word cells, and a worklist with one slot per
cell. Capacity is clamped to 8 through 1,048,576. Handle zero means absent.
The collector follows the pointer fields of objects, activations, blocks,
and links. Class IDs, method IDs, PCs, integer words, and class-object metadata
are scalar fields. Roots are the three canonical values, current activation,
result, and external root.

Construction reserves its complete cell budget before allocation. Allocation
does not collect. Register 19 holds a temporary construction head and is not
a collector root, so collection must not occur during construction.

## Checked and pushed results

All results below refer to actual executable definitions unless explicitly
identified as a list model. Their assumptions remain part of the claims.

| Work | Checked result | Main files in `Project/Smalltalk/` |
| --- | --- | --- |
| Array reads and writes | Exact writes, other reads unchanged, register/cell separation, address arithmetic within bounds | `Memory.lean` |
| Allocation and free list | Exact allocated cell, head removal, complete distinct free list, count, empty-list error 9 | `Allocation.lean`, `FreeList.lean` |
| Complete collector | For a valid graph and non-error phase, preserves reachable payloads and frees exactly unreachable cells; does not assume correct input marks or spare worklist space | `Graph.lean`, `MarkInvariant.lean`, `ScanInvariant.lean`, `Marking.lean`, `Collector.lean` |
| Repeated collection | Preserves graph validity and reachability; a second collection preserves the same live payloads | `CollectorPreservation.lean` |
| Fresh arena | Actual capacity clamp, headers, seeding, canonical values, free-list completeness, and `Heap.Valid` | `InitializationBase.lean`, `SeedMemory.lean`, `Seeding.lean`, `InitializationGraph.lean`, `InitializationFree.lean` |
| Heap allocation | Preserves graph and free-list validity for supported tags and valid new pointers; allocation alone leaves existing reachability unchanged | `HeapAllocation.lean`, `AllocationEffect.lean` |
| Writes and frame updates | Valid pointer/root writes preserve the heap; actual advance and retirement preserve it under activation and value assumptions | `HeapWrite.lean`, `FrameHeap.lean` |
| Traversal | Actual operand and lexical traversal select the represented element or zero; reachable traversal stays zero or reachable, including repeated links and cycles | `Traversal.lean`, `Reachability.lean` |
| Caller and home search | Actual bounded caller membership and lexical-home selection agree with represented paths | `CallChain.lean`, `Home.lean` |
| Return control and delivery | Checks, exact retirement through a represented target, caller stack delivery, final return, and reservation before unwind; caller and chain assumptions remain explicit | `ReturnChecks.lean`, `Unwind.lean`, `ReturnValue.lean`, `ReturnReservation.lean` |
| Reservation | Preserves the valid heap and reachable payloads; supplies the requested free cells or reports error 9; includes stress and pressure collection | `Reservation.lean` |
| Pop and stores | Actual pop and slot stores preserve heap validity, including failure branches, for a valid current activation and zero/link store target | `StackWrite.lean` |
| Push and loads | Actual push preserves heap validity and either reports error 9 or creates the specified operand link and increments the PC; the pushed value must be zero or reachable across reservation | `StackPush.lean`, `PushDispatch.lean`, `PushReservation.lean` |
| Literals | Actual two-cell integer, class, and captured-block construction preserves heap validity | `LiteralHeap.lean` |
| Twelve instruction cases | Heap preservation through actual `execute` and `step` for opcodes 0–9, 14, and 15, including validation and stopped-state branches | `InstructionHeap.lean`, `ExecuteHeap.lean` |
| Pointer cell types | Caller/lexical/capture pointers name activations; field/slot/operand/next pointers name links; initialization, collection, reservation, and checked writes preserve these requirements | `PointerTypes.lean`, `TypedCollection.lean` |
| Typed unwind | Retirement and the bounded unwind loop preserve heap validity, pointer types, caller and value validity, and registers under the stated cursor/caller assumptions | `FrameTypes.lean`, `UnwindHeap.lean` |
| Typed allocation | Allocation preserves pointer cell types when new typed pointers match their required cell types | `TypedAllocation.lean` |
| Public return preservation | Actual local and nonlocal returns preserve heap validity and pointer types; successful caller membership establishes target reachability across reservation | `ReturnCallerHeap.lean`, `ReturnHeap.lean`, `CallChainReachability.lean`, `PublicReturnHeap.lean` |
| Construction links | A construction prepend creates the specified link, preserves existing cells and types, changes the specified registers, consumes exactly one free cell, and prepends the specified logical value; applies to actual `fillOne` | `Construction.lean`, `ConstructionValues.lean` |
| Field-building loop | The complete loop finishes all requested visits, builds exactly the requested handle-1 list, preserves old allocated cells and types, and accounts for all consumed cells; connected to the actual pair-pattern loop | `FillLoop.lean` |
| Complete object construction | Actual `newReady` stores the class and metadata words, produces the exact requested field-value list, clears scratch register 19, preserves old allocated cells and types, and consumes exactly `fields + 1` cells | `ObjectConstruction.lean` |
| Fuel | Actual run composes across fuel segments under the stated word-bound assumption; stopped execution stays stopped | `Execution.lean` |

`Heap.Valid` combines valid graph roots, pointers and tags with the complete
free list. `PointerTypes.Valid` adds the specific cell types required by frame
and list operations. The full VM has not yet been proved to preserve both
through every operation.

`Control.lean` also proves properties of a separate list model. Those results
are not substituted for proofs of concrete runtime lookup or return.

Recent pushed checkpoints:

| Commit | Change |
| --- | --- |
| `8228d97b` | Allocation preserves heap validity and old reachability |
| `734e691f` | Pointer writes and frame updates preserve heap validity |
| `da12434e` | Reachable traversal, pop, and stores |
| `256521af` | Push across reservation and collection |
| `0af581f3` | Literal construction and twelve actual instruction/step cases |
| `e7ffde84` | Pointer cell types through initialization and collection |
| `0a3b36fd` | Typed retirement and bounded unwind |
| `98ba259a` | Typed allocation and public return preservation |
| `8111e36d` | Construction link effects and value order |
| `cb1f5bc9` | Complete field-building loop |

## Current increment

Complete actual `newReady` object construction passes the combined build and
axiom audit. It stores the specified class and metadata words, retains the exact
requested handle-1 field list, clears scratch register 19, preserves old
allocated cells and pointer types, and consumes exactly `fields + 1` cells.
The input budget is stated in natural numbers so its arithmetic cannot wrap.

Next are activation slot binding and argument ordering. The send guard must
establish that selected argument links exist. Dispatcher composition of returns,
exact return path conditions, boot, lookup, and the complete execution invariant
remain unfinished. All checked proof files are included in this increment; no
full VM correctness claim is made.

## Next work, in order

1. Frame retirement typing and bounded unwind preservation are checked and
   pushed as `0a3b36fd`. Keep the work document current with every
   subsequent proof commit.
2. Allocation typing is checked in this increment using the existing exact
   allocation effects. The allocator and collection points are unchanged.
3. Public return heap preservation is checked in this increment, including
   return-to-caller, final return, typed unwind, reservation, and actual guards.
   Connect the exact delivery theorem's caller-path conditions to reachable
   VM states and compose the return opcode cases with the dispatcher.
4. Prove object and activation construction. Check each list-building iteration,
   the allocation counts, temporary register 19, constructed field/slot order,
   caller and lexical captures, and the final current activation. The original
   reservation must supply every allocation in the construction.
   Complete object construction is now checked. Activation binding remains.
   Derive
   argument-link validity from the actual send guard. Preserve canonical value
   contents as part of the complete state invariant, not just their allocation.
5. Prove VM boot from the actual initialized arena and a validated program.
   Connect entry method, receiver construction, slots, initial PC, and roots.
   Arena initialization is already proved; VM boot is not.
6. Prove concrete method lookup against a separate first-match and superclass
   search specification. Account for the flat method scan, owner/selector
   comparisons, inherited lookup, finite search budget, and word arithmetic.
   The existing list-model lookup theorem does not prove `Runtime.lookup`.
7. Prove sends, superclass sends, block calls, and primitives. Check receiver
   and argument selection, arity, fallback methods, construction budgets,
   numeric results and overflow fallback, identity, explicit collection, and
   missing-method and other errors. This completes the remaining opcode
   heap-preservation cases, 10 through 13, together with returns.
8. Define a sufficient VM state invariant and prove boot establishes it and
   every actual step preserves it. Include both heap validity and pointer cell
   types, current activation, rooted values, construction completion, and the
   caller/lexical conditions needed by control operations. Derive finite-run
   preservation from the checked step theorem.
9. State instruction behavior independently of the implementation and prove
   the actual decoder and execution implement it. State the limits precisely:
   malformed inputs, resource errors, fuel exhaustion, and bounded searches.
   Heap preservation alone does not establish instruction semantics or that
   a particular program computes its intended result.
10. Review assumptions, implementation, proofs, and docs together. Close any
    remaining proof gap or explicitly report it. Run the complete Smalltalk
    driver, including real WASM execution, and commit and push the final checked
    changes. Do not label the full VM correct while obligations remain.

Steps may be split into smaller checked commits. If a proof exposes an actual
implementation bug, fix that bug, add a targeted behavior check, rerun the
affected native and WASM checks, and document the changed behavior. No bug has
been identified by the proof increments recorded here.

## Checking and publishing

`Project/Smalltalk/Proofs.lean` imports the checked proof modules.
`tests/smalltalk/proofs.lean` examines every theorem in `Project.Smalltalk` and
its dependencies. It permits only the standard axioms `propext`, `Quot.sound`,
and `Classical.choice`. It rejects admitted proofs, `native_decide` dependencies,
and additional axioms. The driver runs this audit before execution tests.

For a proof-only increment, run a focused check, build the proof umbrella,
run the axiom audit, and run `git diff --check`. Record useful failures and
their resolution in `smalltalk-proof-journal.md`; do not discard the failures
or raise proof limits. Do not rerun unchanged WASM for every proof-only edit.
Run the full driver after executable changes and at the final review.

Current local commands, from the checkout:

```bash
source /workspace/scratch/73af3f54e839/lean-env.sh
tools/leanrun --timeout 60s lake env lean Project/Smalltalk/UnwindHeap.lean
tools/leanrun --timeout 60s lake --log-level=error build Project.Smalltalk.Proofs
tools/leanrun --timeout 60s lake env lean tests/smalltalk/proofs.lean
tests/smalltalk/run.sh
```

The environment script enables the already authorized local runner mode and
the pinned Lean 4.34.0-rc2 toolchain. It retains the shared lock and timeout;
systemd CPU and memory limits are absent in this local mode. Do not start a
second Lean/Lake process while one is running. The repository driver calls the
runner itself and must not be wrapped in another runner.

After each checked increment, commit locally. Publishing currently uses the
GitHub connector to create the changed tree, verify that its SHA equals the
local tree SHA, create a commit, and update `smalltalk-vm` with the expected
parent SHA and `force: false`. Fetch the published commit and align the local
branch with a soft reset, preserving pending work. Keep the original local
commit on a checkpoint branch. Do not force-update the remote or merge a PR.

The checkout is currently
`/workspace/scratch/73af3f54e839/leanexe-regex`. Its directory name predates this
task; the active branch and work are Smalltalk. Git-backed files belong in this
repository, not a separate artifact store.

## Latest complete execution evidence

The most recent full driver passed after the concrete return-control proofs:

- 136 native executions: 68 programs in normal and stress-collection modes.
- 181 WASM checks, including 136 exact arena comparisons with native results.
- 19 rejected invalid compiler inputs.
- CLI examples, eight invalid-option cases, and zero-fuel rejection.
- A 25,208-byte WASM module with zero imports.
- WASM SHA-256:
  `423aaec2687c65c9993160400cad47efe89f62cfb42d6e2d3095cef90b76b19e`.

The local full-driver log is `build/smalltalk/proof-control-review.log`.
Subsequent increments changed proofs and documentation only. Their combined
Lean builds and axiom audits passed. The latest audit log is
`build/smalltalk/proof-object-construction-audit.log`. Build logs and emitted artifacts
can be regenerated with the driver.

See `smalltalk-vm.md` for executable formats and proof limits,
`smalltalk-compilers.md` for compiler status, and
`smalltalk-proof-journal.md` for the proof attempts and corrections.
