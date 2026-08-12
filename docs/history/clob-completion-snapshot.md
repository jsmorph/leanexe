# Archived CLOB Completion Snapshot

This archived note records the CLOB proof state at commit `8dd82fc`.  The [Development Plan](../../plan.md) remains the authoritative work queue, while the [Development Status](../status.md) and [Proof Engineering Notes](../plan-notes.md) describe later work.  The snapshot remains available for its exact pickup instructions and historical proof inventory.

## Snapshot

The `clob_depth` proof is complete through commit `8dd82fc`.  Both level-update branches, the function 3 composition, the per-side fold with its loop invariant, and the exported function 7 theorem are committed, the registry carries `complete: true`, the aggregate `Project.lean` imports the depth specification, and the focused gate `tools/talos-proof.js check clob_depth` passed against a regenerated model.  The two recorded `ClobPostOnly` failures are repaired, and the plan, status report, proof notes, and inventory reflect the completion.

| Item | State |
|------|-------|
| Branch | `main` at `8dd82fc`. |
| Lean version | Compiler and Talos proof workspaces both use Lean 4.31.0. |
| Depth artifact | Complete; focused gate passed 2026-07-18. |
| Aggregate proof gate | `tools/talos-proof.js check --all` was launched 2026-07-18; all twenty artifacts regenerated and the aggregate `Project` build was running when this note was last updated.  The result belongs in `devnotes.md`. |
| Execution gate | Not yet rerun; run `node test/run_all.js` under the outer resource scope after the aggregate proof gate completes. |

## First Pickup Action

Confirm the aggregate proof gate result in the journal.  If it failed, repair the first named module through a focused constrained target.  If it passed, run the execution gate, record both results in `devnotes.md`, and declare the stable point per the plan's completion criteria.

```sh
cd /media/hd2/src/leanexe
tools/talos-proof.js check --all
systemd-run --user --scope --quiet --collect \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=1G \
  -p CPUQuota=100% \
  nice -n 10 ionice -c 3 \
  timeout 3600s node test/run_all.js
```

## Lean Process Policy

Every direct `lean`, `lake`, or `lean-wasm` command must run inside the resource-limited user scope shown above.  The scope uses a four-gibibyte memory-pressure threshold, a six-gibibyte hard memory limit, a one-gibibyte swap limit, and a one-core aggregate CPU quota.  Run only one Lean or Lake job at a time, including jobs started from another terminal.  The Talos tools enforce the same limits internally; invoke them from the repository root without an outer scope.

## After the Gates

The consolidation phase retains the planned divisions for the recorded no-diagnostic timeouts in `Project.Validate.Spec`, `Project.SharedPair.Spec`, `Project.LebU32.Iter`, and `Project.LebU32.NegIter`, the copy-loop and fresh-array library generalization, and release-tree generalization.  At the time of this snapshot, `leanclob/` was a separate nested repository outside the LeanExe work.  The repository later tracked this note and archived it here when the stated pickup point became historical.

## Reference Map

| Document | Role |
|----------|------|
| [Development Plan](../../plan.md) | Required results, order, gates, and completion criteria. |
| [Development Status](../status.md) | Detailed current proof state, measured progress, known failures, and resource policy. |
| [Proof Engineering Notes](../plan-notes.md) | Reusable lemmas, close examples, failed approaches, and elaboration guidance. |
| [Talos Proofs](../../proofs/talos/README.md) | Completed theorem inventory, proof architecture, and trusted-base boundary. |
| [Development Journal](../../devnotes.md) | Dated rationale, focused build results, and historical proof increments. |
