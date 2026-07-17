# Development Status

This report records the repository state on 2026-07-17.  It distinguishes completed and committed work from the remaining `clob_depth` proof obligations.  The [development plan](../plan.md) remains the authoritative work queue, while the [development journal](../devnotes.md) records dated design decisions and individual test results.

## Summary

LeanExe has completed the runtime-ownership, single-evaluation, and CLOB `cancel` phases of the current plan.  Input-generic Talos proofs cover `findBest`, `postOnly`, `matchFuel`, `limit`, and `market`, in addition to the earlier artifacts.  The remaining input-generic CLOB export is `depth`, whose source model, representation, source properties, control-flow decomposition, price scan, and missing-price append phases now have separately compiled theorems.

Measured by planned milestones, the next stable point is about 83 percent complete.  That estimate counts three completed plan phases, five completed exports in the remaining CLOB phase, and one complete generated level-update branch inside `depth`.  The estimate does not predict elapsed time because the found update path, per-side fold, exported two-call composition, and aggregate-proof refresh contain most of the remaining semantic integration.

The missing-price append path has a complete theorem from its scan frame through its owned appended-array result.  It verifies preparation, the stated empty-free-list search, bump allocation, finalization, word copying, stores, result locals, allocator globals, source ownership, pages, and the below-heap byte frame.  No failing proof is committed, and the aggregate proof object remains stale after artifact regeneration and cache removal.

## Repository State

The repository is on `main`, and the latest completed proof increment is `1ba780c` (`Prove depth missing-price branch`).  Both the compiler and proof workspaces select `leanprover/lean4:v4.31.0` through their respective `lean-toolchain` files.  The checked-in depth artifact exists and is pinned, while its complete exported correctness theorem remains open.

| Item | Current state | Evidence |
|------|---------------|----------|
| Branch | `main` | Current Git branch |
| Latest proof increment | `1ba780c Prove depth missing-price branch` | Committed 2026-07-17 proof increment |
| Compiler Lean | Lean 4.31.0 | Root `lean-toolchain` |
| Talos proof Lean | Lean 4.31.0 | `proofs/talos/lean/lean-toolchain` |
| Depth artifact | Registered and tracked | 3,602-byte WASM and checked-in WAT |
| Aggregate Talos proof object | Stale | Requires a planned, divided rebuild |
| Unrelated directory | `leanclob/` is untracked and separate | Nested Git repository; excluded from this work |

All proof edits through the missing-price final stores are committed.  The unrelated `leanclob/` nested repository remains untracked and excluded from this work.  No incomplete Lean theorem or failing proof file is present in the worktree.

### Recent Committed Increments

The recent commits divide the depth proof at meaningful semantic boundaries.  Each commit records a theorem or artifact registration that compiled in isolation before the next boundary was opened.  The sequence avoids committing a large monolithic theorem whose elaboration cost and failure point cannot be isolated.

| Commit | Subject | Completed result |
|--------|---------|------------------|
| `bf687fc` | Register the depth artifact | Added `clob_depth` source model, generated program, pinned WASM and WAT, Rust case registration, runtime pins, and a focused check script. |
| `631e00a` | Prove depth source properties | Added the stride-two level representation, ownership predicate, first-price order facts, exact modular aggregation, and bounded natural-number corollary. |
| `d0d073e` | Divide depth level update | Split generated function 3 into the scan, missing, found, allocation, copy, store, and result regions. |
| `f891009` | Prove depth price scan | Proved the input-generic first-price scan and exact frames for both found and missing outcomes. |
| `cba8190` | Prove depth allocation preparation | Proved field extraction, length arithmetic, capacity rounding, allocator scratch initialization, and free-list-head loading. |
| `91bece9` | Prove depth empty allocator search | Proved immediate free-list search exit under the stated zero-head premise. |
| `801c472` | Prove depth bump allocation | Proved the stride-two header writes, heap-top update, page conditions, and exact allocator store. |
| `db818b3` | Prove depth allocation finish | Proved allocation-counter increment, target propagation, length initialization, and zero copy cursor. |
| `9047fc7` | Prepare depth copy proof | Named the generated loop and proved source representation preservation across disjoint target writes. |
| `d5dca0e` | Prove depth copy invariant | Proved the semantic copied-prefix transition and target/source frame facts. |
| `ffbebbe` | Prove depth missing-level copy | Proved the generated old-level copy loop and its decreasing termination measure. |
| `eefcc84` | Prove depth append-store facts | Reconstructed the exact appended level list after the final two stores. |
| `7a9605e` | Prove depth missing-level stores | Proved the generated final stores and exact result-local assignments. |
| `873a04d` | Prove depth missing-branch facts | Connected allocation finalization to copy initialization and transported the final semantic state to the input allocator state. |
| `1ba780c` | Prove depth missing-price branch | Composed the complete generated branch with exact ownership, allocator, page, byte-frame, and result-local facts. |

## Completed Work

The current plan requires three kinds of evidence: differential execution tests, byte-pinned artifacts, and Talos theorems over decoded WASM.  The compiler remains outside the Talos trusted base because each theorem proves a decoded generated artifact and the check script compares that artifact byte-for-byte with the checked-in WASM and WAT.  The [verification guide](verifying.md) describes this boundary and the [Talos proof inventory](../proofs/talos/README.md) records the completed theorem scopes.

### Plan Phases

| Plan phase | State | Evidence retained in the repository |
|------------|-------|-------------------------------------|
| Runtime intrinsic semantics and direct handoffs | Complete | Extended runtime semantics, ownership-report diagnostics, rejection tests, Wasmtime counter tests, and Talos runtime theorems. |
| Evaluate matched values once | Complete | Reduced fixtures, IR and WAT assertions, execution comparisons, and repaired affected artifacts. |
| Complete CLOB `cancel` behavior | Complete | One input-generic theorem for found and missing identifiers, exact ownership and allocator facts, and the per-case gate. |
| Remaining CLOB kernel | In progress | `findBest`, `postOnly`, `matchFuel`, `limit`, and `market` are complete.  `depth` remains. |
| Consolidate proof machinery | Partly complete | Shared fixed-array, order-word, allocation, and branch-continuation lemmas are in use. |
| Diagnostics and tool reproducibility | Substantially complete | Tested CLI error categories, pinned Node, `wasm-tools`, Wasmtime hashes, and documented resource limits. |

The complete execution baseline recorded on 2026-07-16 passed 791 accepted cases, 45 rejections, 14 traps, 340 standard-Lean comparisons, 62 IR comparisons, 41 reference-counting cases, 9 CLI failure cases, and 3 process-launch error cases.  The same baseline includes matched-value IR and WAT assertions.  These are historical gate results, not a claim that the complete suite was rerun after the present depth allocation split.

Nineteen byte-pinned Talos cases are complete before `depth`.  They include the self-compiled unsigned LEB128 encoder, runtime allocation and teardown cases, and exact CLOB behavior for `quote`, `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, and `market`.  The aggregate script first verifies all artifact bytes and then checks whether the proof workspace is current, which keeps a changed binary from being mistaken for a proof failure.

### Documentation and Developer Guidance

The documentation has clear ownership by subject.  [Developing LeanExe](../DEVELOPING.md) defines setup, versions, the development workflow, test gates, generated-file rules, failure diagnostics, and the required resource policy.  The [user manual](manual.md) defines source authoring, the [language specification](spec.md) defines accepted behavior, the [verification guide](verifying.md) defines the proof procedure, and the [Talos proof inventory](../proofs/talos/README.md) identifies checked cases and theorem scope.

The developer guide names the pinned versions: Lean 4.31.0, Node 24.13.0, `wasm-tools` 1.251.0, and Wasmtime 44.0.0.  It documents the ordinary build, the separate Talos setup, the focused and aggregate proof gates, CLI statuses and stderr format, generated-file ownership, and troubleshooting.  It also makes the resource-limited `systemd-run` invocation mandatory for commands that invoke Lean, Lake, `lean-wasm`, or scripts that start them.

The documentation still needs ordinary maintenance as the depth proof becomes complete.  The proof inventory must add `clob_depth` only after its theorem and case gate are complete, and the development plan and journal must change in the same commit.  This report provides a current snapshot and does not replace those authoritative documents.

## Depth Proof

The generated `clob_depth` artifact is registered under `proofs/talos`.  Its WASM file is 3,602 bytes, its WAT is checked in, and `Project/ClobDepth/Program.lean` contains the generated Talos model.  Function 3 updates or appends one depth level, function 6 folds one side of the order book, function 7 implements the export, and the shared runtime functions follow those program functions.

The source proof work has established the data representation before entering the instruction proof.  `Project.ClobDepth.Representation` defines the stride-two layout for price and quantity levels and the owned fixed-array predicate.  `Project.ClobDepth.Properties` proves side filtering, first-occurrence price order, price uniqueness, exact modular per-price aggregation, and a natural-number interpretation when the stated no-overflow bound holds.

The generated function 3 now has a documented decomposition in `Project.ClobDepth.Entry`.  The scan, missing branch, found branch, allocation search, bump path, allocation finish, copy loop, stores, and result epilogue have separate named program regions.  This structure permits a theorem to end at a `wp` boundary and pass a concise local frame to the theorem for the next region.

`Project.ClobDepth.Scan` proves the first-price search at an input-generic boundary.  In the missing case, the theorem records the encoded zero index, the cursor at the array length, the condition flag, and the retained input fields.  In the found case, it records the one-based encoded index, the zero-based matching index, the matched price and quantity, the condition flag, and the remaining locals needed by the update branch.

### Current Missing-Price Branch

The missing-price branch appends a new `(price, quantity)` level to a stride-two fixed array.  Its proved phases copy the scan fields, compute the target length and rounded capacity, exit an empty free-list search, allocate by bump, initialize the length and allocation counter, copy every old word, store the new pair, and assign the result locals.  The semantic final state records an owned array representing the exact appended list, a preserved source representation, unchanged pages and relevant globals during copying, and byte equality outside the target region.

The first proof attempt treated the forty-four-instruction preparation as one simplification boundary and exhausted the default heartbeat before later exceeding recursion depth.  The completed proof divides preparation into twenty- and twenty-four-instruction regions, then gives search, bump allocation, finalization, copy, and stores their own explicit programs and theorems.  Each decomposition remains definitionally equal to the generated function, so the smaller boundaries do not weaken the artifact claim.

`Project.ClobDepth.MissingCopyInvariant.CopyState.advance` contains the memory reasoning for one copy iteration.  `LevelsAt.frame_write64_flatWordsDisjoint` preserves the source representation, while the invariant preserves the fresh header, initialized length, copied prefix, pages, globals, and outside-target bytes.  `MissingCopy.missingCopyProg_spec` applies that transition to the generated loop with a strictly decreasing word-count measure.

`Project.ClobDepth.MissingStoreFacts.finish` reconstructs `LevelsAt` for the old list followed by the new level.  It combines that representation with the preserved fresh header as `OwnedLevelArrayAt` and retains the source representation and outside-target frame after both writes.  `MissingStore.missingStoreProg_spec` proves the generated stores and exposes the exact working, owner, and pointer locals to its continuation.

`Project.ClobDepth.MissingBranch.missingProg_spec` completes branch composition.  It instantiates the copy invariant from the post-allocation store, carries the source and allocator frames through the loop, and connects the final owned array and result locals to the missing scan outcome.  Its empty-free-list premise remains explicit because generated function 6 performs no release and therefore preserves an initially empty free list throughout its fold.

### Remaining Depth Work

The missing branch is complete under its stated allocator and memory premises.  The found branch requires same-length allocation, copying, and replacement of the first matching quantity, with exact ownership, allocator counters, page preservation, and source frames.  The found proof can reuse `LevelCopyInvariant.CopyState.advance`, the level flat-word API, and disjoint-write preservation while adding only its generated-local adapter and indexed-replacement facts.

Function 6 then needs a loop invariant for the per-side aggregation.  The invariant must relate the consumed order prefix to the source side filter, the first-occurrence price sequence, the represented level array, and the accumulated modular quantities.  Function 7 must compose the two side folds, return both owned arrays in the export ABI, and preserve the input book and allocator facts across both calls.

The source properties already identify reusable statements likely to reduce this work.  The stride-two representation and exact aggregation theorems should be the semantic target of the copy and fold proofs, while existing fixed-array allocation, copy, branch-continuation, and frame lemmas should carry repeated instruction patterns.  A new general lemma or tactic is justified only after the same statement shape appears in independent depth branches or another artifact; no broad normalizer should be added to hide a single local capacity rewrite.

## Verification Status and Risks

Focused depth modules have been built one at a time under the required cgroup policy.  Recent focused builds completed in 1.9 seconds for the representation lemma, 2.7 seconds for the copy loop, 2.9 seconds for semantic final-store facts, 2.0 seconds for the final instruction theorem, and 1.1 seconds for `Project.ClobDepth.Spec`; the final two used `--wfail`.  No current focused depth target fails or approaches its 90-second diagnostic limit.

The aggregate `Project` proof object is stale.  The planned divisions include `Project.Validate.Spec`, `Project.SharedPair.Spec`, `Project.LebU32.Iter`, and `Project.LebU32.NegIter`, with several shorter dependencies also needing refresh.  Earlier constrained builds of the long targets reached their diagnostic time limits, so they must be divided at instruction or theorem boundaries before another aggregate proof rebuild is attempted.

Mathlib cache removal freed disk space but means a cold proof setup can rebuild a large dependency graph.  A cold build is acceptable only through the constrained user scope and with no concurrent Lean or Lake activity.  The focused modules used for the current depth work have continued to build, so there is no evidence of a missing dependency or toolchain incompatibility at this boundary.

No external blocker prevents the next depth proof step.  The main technical risk is preserving the complete allocator and source-ownership state while composing the small theorems, followed by the larger function 6 loop invariant.  The explicit semantic predicates and short instruction adapters keep those obligations separate from generated-program normalization.

## Required Lean and Lake Resource Policy

Every `lean`, `lake`, Lean compiler, `lean-wasm`, or script that starts one of those commands must run in a resource-limited transient user scope.  This includes `tools/setup-talos.sh`, `tools/check-talos.sh`, and `node test/run_all.js` when they invoke Lean or Lake.  Do not run two such jobs concurrently, including from separate terminals, because the policy limits one scope but cannot protect the machine from several scopes competing for memory and CPU.

Run the command from the directory that owns the relevant Lake workspace.  The proof workspace is `proofs/talos/lean`, while ordinary compiler builds run from the repository root.  The `timeout` must bound commands whose runtime is not intrinsically bounded, and a timeout without a diagnostic requires proof or module division before another attempt.

```sh
systemd-run --user --scope --quiet --collect \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=1G \
  -p CPUQuota=100% \
  nice -n 10 ionice -c 3 \
  timeout <duration> <lean-or-lake-command>
```

`systemd-run --user` asks the per-user systemd manager to create the cgroup.  `--scope` runs the named process directly in that cgroup, `--quiet` suppresses the generated unit name, and `--collect` removes the transient scope after its processes exit.  These options ensure that Lake children remain inside the same scope and that completed diagnostic runs do not accumulate units.

`MemoryHigh=4G` begins memory-pressure handling when the scope exceeds four gibibytes.  `MemoryMax=6G` enforces the hard cgroup memory limit, and `MemorySwapMax=1G` prevents unlimited swap growth from making the workstation unusable.  `CPUQuota=100%` limits all processes in the scope to one CPU core in aggregate, which is required because Lake 5.0.0 has no job-count option.

`nice -n 10` lowers CPU scheduling priority relative to interactive work.  `ionice -c 3` gives the process idle I/O priority, so compiler reads and writes yield to interactive I/O.  `timeout` stops a diagnostic run at the stated duration, but it does not make an unchanged timed-out theorem appropriate to rerun.

The focused proof command starts from the proof workspace because its `lakefile.toml` owns the Talos project.  The command below builds one bounded module and fails on warnings, which makes it appropriate for an in-progress theorem.  Wait for this scope to exit before starting any other Lean or Lake command.

```sh
cd proofs/talos/lean
systemd-run --user --scope --quiet --collect \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=1G \
  -p CPUQuota=100% \
  nice -n 10 ionice -c 3 \
  timeout 90s lake build Project.ClobDepth.MissingFields --wfail
```

Use the same wrapper around a direct Lean invocation or a script that starts Lake.  Repository-level scripts start from the repository root, and a cold Talos setup needs a longer diagnostic budget than a focused module build.  Select the timeout from the known behavior of the named job, record a new limit in the development journal when it becomes routine, and never remove the cgroup properties to make a command finish.

```sh
cd /media/hd2/src/leanexe
systemd-run --user --scope --quiet --collect \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=1G \
  -p CPUQuota=100% \
  nice -n 10 ionice -c 3 \
  timeout 30m tools/setup-talos.sh
```

The setup command can rebuild many cached dependency outputs after cache removal.  It still runs as one CPU-limited, memory-limited scope, and it must run alone.  A timeout without a specific error requires inspection of the next compilation boundary rather than another identical cold setup.

```sh
cd /media/hd2/src/leanexe
systemd-run --user --scope --quiet --collect \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=1G \
  -p CPUQuota=100% \
  nice -n 10 ionice -c 3 \
  timeout 20m tools/check-talos.sh
```

The aggregate check compares every pinned artifact before it tests proof freshness.  The current aggregate proof object is stale, so this command is expected to reveal that state until the planned proof divisions and rebuilds are complete.  Do not treat a stale aggregate result as evidence that the focused depth modules have failed.

Do not substitute `ulimit -v`, `prlimit --as`, a background process, or an unbounded bare `lake build` for this policy.  If `systemd-run --user --scope` or any required cgroup property is unavailable, stop rather than running Lean without an enforced memory limit.  If a target reaches its timeout with no useful diagnostic, first divide its instruction program or theorem, or prove a reusable lemma that reduces the elaboration boundary.

## Next Order of Work

The immediate task is the found-price branch: prepare a same-length allocation, copy all level words, replace the first matching quantity with modular addition, and return the exact updated list.  Function 3 composition follows by selecting the missing or found theorem from the scan outcome and returning the shared result predicate.  Each increment requires a focused resource-limited warning-failing build and a journal entry before commit.

After both update branches are proved, the per-side depth fold becomes the central proof task.  Its theorem should state exact first-price order and modular aggregation without adding an unstated no-overflow assumption, then derive the natural-number result under the explicit bound already present in the source properties.  The exported theorem should compose the two side arrays and state their ownership, contents, allocator effects, page bound, and input-memory frame.

The stable-point work after `depth` remains finite but material.  It includes the planned aggregate-proof divisions, the remaining copy-loop and fresh-array library generalization, release-tree array-kind and shared-interior generalization, and cleanup of proof warnings encountered during substantive bounded rebuilds.  The next stable point cannot be declared until the depth case is in the proof inventory, the aggregate proof object is current, the complete execution and artifact gates pass, and the plan, journal, verification inventory, and this status report agree on the evidence.
