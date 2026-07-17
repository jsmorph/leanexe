# Development Status

This report records the repository state on 2026-07-17.  It distinguishes completed and committed work from the unfinished `clob_depth` proof currently present in the worktree.  The [development plan](plan.md) remains the authoritative work queue, while the [development journal](devnotes.md) records dated design decisions and individual test results.

## Summary

LeanExe has completed the runtime-ownership, single-evaluation, and CLOB `cancel` phases of the current plan.  Input-generic Talos proofs now cover `findBest`, `postOnly`, `matchFuel`, `limit`, and `market`, in addition to the earlier artifacts.  The remaining input-generic CLOB export is `depth`, whose proof has begun with the artifact, source model, representation, source properties, control-flow decomposition, and price-scan theorem in place.

Measured by planned milestones, the next stable point is about 80 percent complete.  That estimate counts three completed plan phases, five completed exports in the remaining CLOB phase, and substantial proof-library work already reused by those exports.  It is not a schedule estimate: `depth` contains allocation, two copy paths, a per-side fold, and ownership obligations that can consume a disproportionate share of the remaining proof effort.

The current worktree contains a deliberately incomplete split of the missing-price allocation path.  Its first module compiles under the required resource limits, while the second has two specific type mismatches around capacity normalization.  No failing proof has been committed, and the full aggregate proof gate remains stale after artifact regeneration and cache removal.

## Repository State

The repository is on `main` at committed proof revision `f891009` (`Prove depth price scan`).  Both the compiler and proof workspaces select `leanprover/lean4:v4.31.0` through their respective `lean-toolchain` files.  The checked-in depth artifact exists and is pinned, but its handwritten specification is not yet complete.

| Item | Current state | Evidence |
|------|---------------|----------|
| Branch | `main` | Current Git branch |
| Last committed change | `f891009 Prove depth price scan` | Committed 2026-07-16 proof increment |
| Compiler Lean | Lean 4.31.0 | Root `lean-toolchain` |
| Talos proof Lean | Lean 4.31.0 | `proofs/talos-gcd/lean/lean-toolchain` |
| Depth artifact | Registered and tracked | 3,602-byte WASM and checked-in WAT |
| Aggregate Talos proof object | Stale | Requires a planned, divided rebuild |
| Unrelated directory | `leanclob/` is untracked and separate | Nested Git repository; excluded from this work |

The current proof edits are not committed.  `Project/ClobDepth/Entry.lean` modifies the generated-control decomposition, and `Project/ClobDepth/MissingFields.lean` and `Project/ClobDepth/MissingPrepare.lean` are new handwritten proof modules.  This status report is intended to be committed separately from those in-progress proof files so that the current diagnosis remains available without treating the incomplete theorem as finished.

### Recent Committed Increments

The recent commits divide the depth proof at meaningful semantic boundaries.  Each commit records a theorem or artifact registration that compiled in isolation before the next boundary was opened.  The sequence avoids committing a large monolithic theorem whose elaboration cost and failure point cannot be isolated.

| Commit | Subject | Completed result |
|--------|---------|------------------|
| `bf687fc` | Register the depth artifact | Added `clob_depth` source model, generated program, pinned WASM and WAT, Rust case registration, runtime pins, and a focused check script. |
| `631e00a` | Prove depth source properties | Added the stride-two level representation, ownership predicate, first-price order facts, exact modular aggregation, and bounded natural-number corollary. |
| `d0d073e` | Divide depth level update | Split generated function 3 into the scan, missing, found, allocation, copy, store, and result regions. |
| `f891009` | Prove depth price scan | Proved the input-generic first-price scan and exact frames for both found and missing outcomes. |

## Completed Work

The current plan requires three kinds of evidence: differential execution tests, byte-pinned artifacts, and Talos theorems over decoded WASM.  The compiler remains outside the Talos trusted base because each theorem proves a decoded generated artifact and the check script compares that artifact byte-for-byte with the checked-in WASM and WAT.  The [verification guide](verifying.md) describes this boundary and the [Talos proof inventory](proofs/talos-gcd/README.md) records the completed theorem scopes.

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

The documentation has clear ownership by subject.  [Developing LeanExe](DEVELOPING.md) defines setup, versions, the development workflow, test gates, generated-file rules, failure diagnostics, and the required resource policy.  The [user manual](manual.md) defines source authoring, the [language specification](spec.md) defines accepted behavior, the [verification guide](verifying.md) defines the proof procedure, and the [Talos proof inventory](proofs/talos-gcd/README.md) identifies checked cases and theorem scope.

The developer guide names the pinned versions: Lean 4.31.0, Node 24.13.0, `wasm-tools` 1.251.0, and Wasmtime 44.0.0.  It documents the ordinary build, the separate Talos setup, the focused and aggregate proof gates, CLI statuses and stderr format, generated-file ownership, and troubleshooting.  It also makes the resource-limited `systemd-run` invocation mandatory for commands that invoke Lean, Lake, `lean-wasm`, or scripts that start them.

The documentation still needs ordinary maintenance as the depth proof becomes complete.  The proof inventory must add `clob_depth` only after its theorem and case gate are complete, and the development plan and journal must change in the same commit.  This report provides a current snapshot and does not replace those authoritative documents.

## Depth Proof

The generated `clob_depth` artifact is registered under `proofs/talos-gcd`.  Its WASM file is 3,602 bytes, its WAT is checked in, and `Project/ClobDepth/Program.lean` contains the generated Talos model.  Function 3 updates or appends one depth level, function 6 folds one side of the order book, function 7 implements the export, and the shared runtime functions follow those program functions.

The source proof work has established the data representation before entering the instruction proof.  `Project.ClobDepth.Representation` defines the stride-two layout for price and quantity levels and the owned fixed-array predicate.  `Project.ClobDepth.Properties` proves side filtering, first-occurrence price order, price uniqueness, exact modular per-price aggregation, and a natural-number interpretation when the stated no-overflow bound holds.

The generated function 3 now has a documented decomposition in `Project.ClobDepth.Entry`.  The scan, missing branch, found branch, allocation search, bump path, allocation finish, copy loop, stores, and result epilogue have separate named program regions.  This structure permits a theorem to end at a `wp` boundary and pass a concise local frame to the theorem for the next region.

`Project.ClobDepth.Scan` proves the first-price search at an input-generic boundary.  In the missing case, the theorem records the encoded zero index, the cursor at the array length, the condition flag, and the retained input fields.  In the found case, it records the one-based encoded index, the zero-based matching index, the matched price and quantity, the condition flag, and the remaining locals needed by the update branch.

### Current Missing-Price Branch

The missing-price branch appends a new `(price, quantity)` level to a stride-two fixed array.  It must first copy the fields from the scan result, read the represented length, compute the target length and rounded allocation capacity, choose a free-list or bump allocation, initialize the new header, copy old levels, store the new pair, and return an owned array.  The final theorem must also preserve the input array, allocator counters, relevant globals, page bound, and the memory frame required by the exported depth result.

The first forty-four instructions of this branch previously formed one preparation theorem.  A broad `simp` over that sequence exhausted the default heartbeat and then exceeded recursion depth when enlarged, so it did not provide a useful proof boundary.  The preparation is now divided at instruction 20 into `missingFieldsProg` and `missingAllocPrepareProg`, each written as an explicit instruction list whose concatenation is proved by `rfl`.

`Project.ClobDepth.MissingFields.missingFieldsProg_spec` is complete and compiles in 1.4 seconds under the required cgroup limits.  It transforms the missing scan frame into the field frame by copying the price and quantity, reading the represented length, and computing the source and target word counts.  Its only arithmetic bridge proves that `UInt64.ofNat levels.length + 1` equals `UInt64.ofNat (levels.length + 1)` below the established `2^32` length bound.

`Project.ClobDepth.MissingPrepare.missingPrepareProg_spec` currently targets only `missingAllocPrepareProg`, not the full forty-four-instruction prefix.  It derives the exact rounded stride-two capacity, proves that the new array needs at least the minimum eight bytes, and prepares the allocator scratch locals and free-list cursor.  The latest focused build stopped with two type mismatches, both caused by a presentation difference between the raw rounded `UInt64` expression emitted by the instructions and `fixedArrayBytesU (levels.length + 1) 2` used by the local frame.

The next proof step is narrow.  The capacity-rounding equality should be rewritten explicitly at the false branch of the minimum-capacity conditional before applying the lower-bound fact, and again before the final frame is compared with `prepareFrame`.  The current `simp [hRound]` does not perform that rewrite at either required boundary, so the theorem should use the equality directly rather than increase heartbeats, recursion depth, or simplifier scope.

### Remaining Depth Work

The missing branch requires the empty free-list search, the bump allocation branch, allocator finalization, the old-level copy loop, and the two final stores after allocation preparation.  The found branch has the analogous same-length allocation and copy work, followed by replacement of the matched quantity.  Each branch must establish a precise fresh-array predicate, borrowed-versus-owned result status, allocator globals and counters, page preservation, and the input memory frame.

Function 6 then needs a loop invariant for the per-side aggregation.  The invariant must relate the consumed order prefix to the source side filter, the first-occurrence price sequence, the represented level array, and the accumulated modular quantities.  Function 7 must compose the two side folds, return both owned arrays in the export ABI, and preserve the input book and allocator facts across both calls.

The source properties already identify reusable statements likely to reduce this work.  The stride-two representation and exact aggregation theorems should be the semantic target of the copy and fold proofs, while existing fixed-array allocation, copy, branch-continuation, and frame lemmas should carry repeated instruction patterns.  A new general lemma or tactic is justified only after the same statement shape appears in independent depth branches or another artifact; no broad normalizer should be added to hide a single local capacity rewrite.

## Verification Status and Risks

Focused depth modules have been built one at a time under the required cgroup policy.  The representation build completed in 1.7 seconds, source properties in 2.4 seconds, the initial entry decomposition in 1.5 seconds, scan in 3.4 seconds, and the new missing-fields theorem in 1.4 seconds.  The current allocation-preparation build failed in 1.6 seconds with the two diagnostic mismatches described above, which is useful progress because it exposes a bounded local proof obligation rather than an unbounded elaboration failure.

The aggregate `Project` proof object is stale.  The planned divisions include `Project.Validate.Spec`, `Project.SharedPair.Spec`, `Project.LebU32.Iter`, and `Project.LebU32.NegIter`, with several shorter dependencies also needing refresh.  Earlier constrained builds of the long targets reached their diagnostic time limits, so they must be divided at instruction or theorem boundaries before another aggregate proof rebuild is attempted.

Mathlib cache removal freed disk space but means a cold proof setup can rebuild a large dependency graph.  A cold build is acceptable only through the constrained user scope and with no concurrent Lean or Lake activity.  The focused modules used for the current depth work have continued to build, so there is no evidence of a missing dependency or toolchain incompatibility at this boundary.

No external blocker prevents the next depth proof step.  The current problem has a known cause, a small typed proof boundary, and an explicit equality that bridges the two forms of the capacity expression.  The main risk is time spent on repeated elaboration rather than semantic proof work, which the decomposition and resource policy address directly.

## Required Lean and Lake Resource Policy

Every `lean`, `lake`, Lean compiler, `lean-wasm`, or script that starts one of those commands must run in a resource-limited transient user scope.  This includes `tools/setup-talos.sh`, `tools/check-talos.sh`, and `node test/run_all.js` when they invoke Lean or Lake.  Do not run two such jobs concurrently, including from separate terminals, because the policy limits one scope but cannot protect the machine from several scopes competing for memory and CPU.

Run the command from the directory that owns the relevant Lake workspace.  The proof workspace is `proofs/talos-gcd/lean`, while ordinary compiler builds run from the repository root.  The `timeout` must bound commands whose runtime is not intrinsically bounded, and a timeout without a diagnostic requires proof or module division before another attempt.

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
cd proofs/talos-gcd/lean
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

The immediate task is to complete `missingAllocPrepareProg_spec` with the explicit capacity rewrite.  The next commits should then add the free-list search and bump-allocation theorems, each at its own `wp` boundary, before composing them with the complete missing-price allocation path.  Each increment should receive a focused resource-limited build and a journal entry before it is committed.

After both update branches are proved, the per-side depth fold becomes the central proof task.  Its theorem should state exact first-price order and modular aggregation without adding an unstated no-overflow assumption, then derive the natural-number result under the explicit bound already present in the source properties.  The exported theorem should compose the two side arrays and state their ownership, contents, allocator effects, page bound, and input-memory frame.

The stable-point work after `depth` remains finite but material.  It includes the planned aggregate-proof divisions, the remaining copy-loop and fresh-array library generalization, release-tree array-kind and shared-interior generalization, and cleanup of proof warnings encountered during substantive bounded rebuilds.  The next stable point cannot be declared until the depth case is in the proof inventory, the aggregate proof object is current, the complete execution and artifact gates pass, and the plan, journal, verification inventory, and this status report agree on the evidence.
