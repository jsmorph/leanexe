# Development Status

This report records the repository state on 2026-07-18.  The `clob_depth` proof is complete and the focused depth gate passes against a regenerated model.  The [development plan](../plan.md) remains the authoritative work queue, while the [development journal](../devnotes.md) records dated design decisions and individual test results.

## Summary

LeanExe has completed the runtime-ownership, single-evaluation, and CLOB `cancel` phases of the current plan, and the remaining-CLOB phase now includes `depth`.  Input-generic Talos proofs cover `quote`, `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, `market`, and `depth`, in addition to the earlier artifacts.  `ClobDepth.Func7.func7_terminates` proves that the exported depth function terminates for every represented order book under the stated allocator budget and returns two owned level arrays representing the exact source `depthL` bids and asks.

The two proof failures recorded by the previous aggregate run are repaired.  Both were unfolding gaps after the shared allocation definitions moved their header writes into `fixedArrayHeaderMem`, and each needed one definition added to a closing simplification set.  The aggregate proof gate and the execution gate are the remaining stable-point evidence; their most recent results appear in the development journal.

## Current State

| Item | State | Evidence |
|------|-------|----------|
| Branch | `main` | Twenty-one depth proof commits since `0dea0bf`. |
| Depth artifact | Complete | `cases.json` carries `complete: true`; `tools/talos-proof.js check clob_depth` passed on 2026-07-18. |
| Aggregate imports | Current | `Project.lean` imports `Project.ClobDepth.Spec`. |
| PostOnly repairs | Complete | Focused warning-failing builds pass in 12 and 7.1 seconds. |
| Lean toolchain | `leanprover/lean4:v4.31.0` | Both compiler and proof workspaces. |

## Depth Proof Structure

The proof divides generated function 3 at the scan, branch, allocation, copy, store, and result boundaries, with each region's theorem passing an exact local frame to the next.  The missing-price branch appends one level through bump allocation and a stride-two copy, while the found-price branch allocates a same-length array, copies every level word, and replaces the matched quantity with modular addition.  Both branches share the empty free-list search theorem, the generic bump theorem, the level-copy invariant, and the fixed-array allocation library, and `Func3.UpdateResult` states their one conclusion: the returned array represents `addLevelL levels price qty` with a capacity derived from the result length.

Function 6 reads the order count, allocates two empty level arrays through one shared adapter, and folds the orders on the selected side.  `Func6Fold` defines the represented levels, match count, heap top, result root, owner, and capacity after any order prefix, and bounds the heap top by `g0 + 112 + k * stepBytes count`.  `Func6Loop` carries the loop invariant with exact allocator globals, the owned result array, the preserved orders representation, and the byte frame below the initial heap top; its body theorem steps each order through `wp_call_tw` and the function 3 `TerminatesWith` wrapper, and one budget premise discharges every per-call fit.

Function 7 composes the two side folds.  The second fold runs at the first fold's exact heap top and counters, the first result array survives through the below-heap byte frame, and `Func7.Result` states ownership of both arrays with `depthSideL` contents, the preserved input orders array, the exact three allocator globals, page equality, and bytes below the initial heap top.  `Project.ClobDepth.Spec` restates the returned contents through `Model.depthL` and exposes exact modular per-price aggregation with its bounded natural-number interpretation.

## Verification Status and Risks

Every depth module builds through the required constrained scope with `--wfail`.  The largest focused builds are the loop body at 10 seconds and the empty-allocation adapter at 9.1 seconds; every other depth module builds in under seven seconds.  The focused depth gate regenerates the model from the current source and compiler before building the registered specification, so the theorem follows the current artifact.

Earlier constrained builds of `Project.Validate.Spec`, `Project.SharedPair.Spec`, `Project.LebU32.Iter`, and `Project.LebU32.NegIter` recorded no-diagnostic timeouts, and the plan retains their division work in the consolidation phase.  A cold proof setup can rebuild a large dependency graph after Mathlib cache removal; run any such rebuild only through the constrained scope with no concurrent Lean activity.

The aggregate proof gate regenerates all twenty models before building `Project`, and the execution gate runs `node test/run_all.js` under the outer resource scope.  The most recent aggregate and execution results, with dates, are in the development journal; declare the next stable point only when both gates pass and the plan, journal, verification inventory, and this report agree on the evidence.

## Required Lean and Lake Resource Policy

Every direct `lean`, `lake`, Lean compiler, `lean-wasm`, or script that starts one of those commands must run in a resource-limited transient user scope.  The two Talos tools apply these limits to each Lean-based child internally, while `node test/run_all.js` still requires an outer scope.  Do not run two such jobs concurrently, including from separate terminals, because separate scopes can compete for memory and CPU.

```sh
systemd-run --user --scope --quiet --collect \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=1G \
  -p CPUQuota=100% \
  -p AllowedCPUs=0 \
  nice -n 10 ionice -c 3 \
  timeout <duration> <lean-or-lake-command>
```

`MemoryHigh=4G` begins memory-pressure handling at four gibibytes, `MemoryMax=6G` enforces the hard limit, `MemorySwapMax=1G` bounds swap growth, and `CPUQuota=100%` limits the scope to one core in aggregate.  `AllowedCPUs=0` pins the scope to one CPU, which Lake's scheduler reads as its concurrency, so it runs one worker at a time; without it Lake spawns several multi-gibibyte workers into the one scope and they thrash against the memory threshold.  `nice -n 10` and `ionice -c 3` protect interactive work, and `timeout` bounds diagnostic runs.  A timeout without a diagnostic requires proof or module division before another attempt.

The focused proof command starts from `proofs/talos/lean` because its `lakefile.toml` owns the Talos project.  Repository-level scripts start from the repository root, while the two Talos entry points create the wrapper themselves.

```sh
cd /media/hd2/src/leanexe
tools/talos-proof.js check clob_depth
tools/talos-proof.js check --all
```

Do not substitute `ulimit -v`, `prlimit --as`, a background process, or an unbounded bare `lake build` for this policy.  If `systemd-run --user --scope` or any required cgroup property is unavailable, stop rather than running Lean without an enforced memory limit.

## Next Order of Work

The stable-point work after `depth` remains finite but material.  It includes the planned aggregate-proof divisions for the recorded no-diagnostic timeouts, the remaining copy-loop and fresh-array library generalization, release-tree array-kind and shared-interior generalization, and cleanup of proof warnings encountered during substantive bounded rebuilds.  The next stable point requires the aggregate proof object, the complete execution and artifact gates, and agreement among the plan, journal, verification inventory, and this report.
