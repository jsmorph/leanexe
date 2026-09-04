# TalosFP Euler operating contract

This document is the canonical operating contract for work on
`jsmorph/leanexe` branch `talosfp-euler`, which was created from `talosfp`.
These are project requirements supplied by the user, not disposable session
preferences.  They apply to the primary agent, delegated agents, tools, and
any automated facility used during this work.  Reread this contract after a
context compaction, checkout recovery, or agent handoff.  It is the
branch-specific authority when a generic instruction suggests remote
execution, cleanup, or another action prohibited here.

## Persistent checkout state

- Treat the complete active checkout as persistent, user-owned project data.
  This includes `.git`; tracked, untracked, generated, and ignored files;
  submodules and dependencies; build products and caches; exact WASM/WAT and
  proof artifacts; evidence receipts; temporary-looking directories; and
  partial or failed work.
- The checkout is not a disposable workspace and is not a maintenance or
  reclamation target.  A previous automated workspace-maintenance event
  removed a complete checkout, including `.git`; that was data loss, not an
  authorized project operation.
- Do not run generic maintenance, cleanup, repair, reclamation, cache
  invalidation, pruning, truncation, movement, recursive deletion,
  `git clean`, destructive reset, checkout-overwrite, stash, worktree rewrite,
  or an equivalent operation.  Describing a file as generated, ignored,
  cached, reproducible, stale, or temporary does not authorize removing or
  replacing it.
- If an operation could delete, overwrite, replace, invalidate, truncate,
  move, or broadly rewrite pre-existing checkout state, stop.  It requires a
  fresh user instruction naming the exact target and action.
- The only standing deletion exception is internal removal by a scoped tool of
  one exact fresh task-owned staging path which that same invocation created.
  The path must not have existed before the invocation, and the exception does
  not extend to siblings, prior staging paths, caches, or requested outputs.
- Preserve unrelated and in-progress state.  Never use a cleanup or restore
  command to make the tree look clean.  A dirty tree is information to inspect
  and work around.  If progress would require discarding conflicting state,
  stop and ask the user.

## Mutation protocol

Before every filesystem or Git mutation:

1. Run `git status --short --branch` and inspect the result.
2. Identify the exact paths and the bounded intended change.
3. Preserve every unrelated tracked, untracked, generated, ignored, and
   temporary-looking path.

One status inspection covers one reviewed top-level command boundary,
including the bounded caches or generated outputs that command is expected to
write.  Reinspect status before the next edit, generator, build/test command
that writes local state, staging action, or publication mutation.

After a mutation, inspect the changed paths and diff.  Stage only an explicit,
reviewed path list; never use broad staging as a substitute for review.
Delegated work must be coordinated against the shared checkout, and delegated
agents may edit only specifically assigned non-overlapping paths.  They do not
run Git mutations, Lean, cleanup, or maintenance unless the primary agent
delegates that exact action.  No agent may start a Lean-family process while
another is active.  Preserve useful failed drafts and diagnostics rather than
discarding them to simplify the tree.

## Local-only execution

- There is no `dev` host.  Never invoke, probe, or assume the existence of
  `tools/leanrun-dev` or another remote executor.
- Run Lean, Lake, `lean-wasm`, compiler work, Talos, Node regressions, C builds,
  Wasmtime, artifact preparation, and proof checks locally.  The user has
  explicitly authorized direct local Lean execution.  GitHub is only the
  publication and recovery remote.
- Serialize all Lean-family work globally: exactly one Lean, Lake, compiler,
  verifier, or runner-owned Lean process at a time, including work initiated
  by delegated agents.  Use one Lean thread and an explicit timeout.
- Do not repeat an unchanged target after a timeout that produced no theorem
  diagnostic.  Record the timeout, isolate and build a smaller dependency
  boundary, and retry only after the proof or cache state materially changes.
- Do not run the experimental self-hosted emitter or its gates for this
  project.
- Hash, manifest, release-receipt, cold-checkout, and self-host work are not
  Euler implementation gates unless the current reviewed change explicitly
  touches one of those boundaries.

The pinned direct local command envelope is:

```sh
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  LEAN_NUM_THREADS=1 \
  WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build TARGET
```

`LEANRUN_LOCAL=1` retains the shared lock, pinned toolchain, one-thread limit,
priority controls, and timeout, while explicitly warning that unavailable
systemd cgroup memory/CPU limits are not enforced.

Before the first compiler or proof command in a recovered session, validate
the referenced toolchain, preload, and `wasm-tools` paths and record any
replacement in `journal.md`; never silently substitute a binary.  The current
preload source has SHA-256
`acd79fcf9a4f6589f7ad80b4b423b62154e6f4969a9626650f2bb17ca3d501ef`,
and its current x86-64 shared object has SHA-256
`c19e991bc769852e40c35fb25a3af38014296c6c2bfa132d4a8a2d1b78beaf5b`.
These identify this session workaround; they are not theorem inputs.

Lean 4.34.0-rc2 in this nested PID namespace needs the external compatibility
preload shown above.  It maps numeric `/proc/<pid>/exe` lookups made by the
current process to `/proc/self/exe`.  Keep it outside the repository and never
present it as proof evidence.  Never pass it to `ps` or unrelated process
inspection; the already-recorded read-only `ps` failure must not be repeated.

## Runner and artifact-driver boundaries

- Direct Lean or Lake targets run through the local `tools/leanrun` envelope.
- Invoke a Node driver that calls `tools/leanrun` internally directly under
  the pinned environment.  This includes `tools/talos-artifact.js`,
  `tools/talos-proof.js`, `tools/artifact-proof.js`,
  `tools/artifact-conformance.js`, `tools/artifact-release.js`,
  `node test/run_all.js`, and focused regressions that use
  `tools/run-process.js`.  Do not place an outer `tools/leanrun` around such a
  driver: the non-reentrant nested-runner guard rejects it.
- `tools/talos-artifact.js` creates one fresh uniquely named
  repository-local `tmp/leanexe-talos-*` staging directory for its invocation.
  It may remove only that same newly created, task-owned directory after the
  staged operation finishes.  It must not touch, repurpose, or classify as
  maintenance material any pre-existing `tmp/` entry, generated output,
  dependency, cache, evidence file, or partial work.  No manual staging cleanup
  is authorized.
- An explicitly requested `prepare <case>` run may atomically update only that
  case's named WASM, WAT, and tracked `Program.lean` deliverables after its
  complete staging succeeds.  This is a reviewed deliverable mutation, not
  cleanup authority.  Once produced, those outputs remain persistent project
  state; review their byte/cache changes and do not edit `Program.lean` by
  hand.
- The fixed-step generation run used the fresh task-owned directory
  `tmp/leanexe-talos-jqTrWD` and left the pre-existing directories
  `tmp/leanexe-talos-WauTHs` and `tmp/leanexe-talos-x9h6ML` untouched.  The
  detailed correction and evidence remain in `journal.md`.

## Verification and claim discipline

- No changed Lean proof may introduce `sorry`, `admit`, or a new axiom.
  Public execution and numerical theorems must receive an axiom audit and may
  report only the project's accepted standard logical axioms.
- Exact generated WAT semantics and, where claimed, exact embedded bytes are
  the formal subject.  Native execution, Wasmtime, C numerics, IR inspection,
  and host comparisons are regression or review evidence, not substitutes for
  a Talos execution theorem.
- Inspect emitted WAT and exact binary opcode/call structure; do not infer a
  formal execution claim from matching sample numbers alone.
- Test rejection paths and guard boundaries, including signed zero and
  adjacent encodings when material, while preserving all existing integer and
  floating-point proof cases.
- Hash, manifest, release-receipt, and self-host bookkeeping does not replace
  the theorem input.  Never present a stale receipt as current.

Ask before adding a third-party dependency or materially expanding the trusted
base.  Pin any approved dependency or artifact-producing tool immutably,
document its purpose and trusted-base effect, and add the relevant gate.  Raise
critical design changes for discussion before implementation, and report a
missing required tool instead of silently substituting another approach.

## Detailed records and checkpoints

- Keep `journal.md` append-only as the detailed chronological ledger.  Record
  commands, exact environment and target, elapsed boundaries, outcomes,
  warnings, rejected invocations, failures, timeouts, proof diagnostics,
  corrections, hashes, axiom audits, unresolved proof boundaries, staged path
  intent, commit and tree identities, and publication verification.
- Correct an earlier note by appending an explicit correction; do not erase the
  historical entry.  Distinguish a command rejected before execution, a
  timeout, a theorem failure, and a passing check.
- Keep `devnotes.md` as the concise durable checkpoint record and keep
  `plan.md` plus `plans/euler-rusanov.md` synchronized with actual scope and
  completion.  Commit and push the journal and notes whenever they change.
- Commit and publish every coherent checkpoint promptly.  Label incomplete
  proofs and unchecked work honestly so the remote branch is a recovery
  boundary, never a rationale for discarding local state.
- Send the user a concise update before a long operation, after each material
  result or failure, and at least every 60 seconds while work is ongoing.

## Non-forced GitHub publication

Ordinary HTTPS push authentication is unavailable in this environment.  Use
the authenticated GitHub Git-data API without altering the worktree:

1. Recheck status and review the exact staged path list and staged diff.
2. Upload exact blobs for every changed path.
3. Create a tree from the current remote branch tree.
4. Require the API-created tree identity to equal the staged local
   `git write-tree` identity.
5. Create a commit whose sole parent is the current remote
   `talosfp-euler` tip.
6. Advance `refs/heads/talosfp-euler` with `force: false` only.
7. Fetch the published commit through the ordinary read path.
8. Require the fetched commit, parent, message, and complete tree to match the
   requested values.  Require fetched-tree, local-index, and worktree content
   equality.
9. Only then advance the local branch ref with an exact compare-and-swap
   `git update-ref`, and confirm a clean synchronized status.

Never force-push, rewrite the worktree, reset, checkout, stash, merge, or delete
state as part of publication.  Record the commit SHA, tree SHA, parent, branch
update, fetch, equality checks, and final status in `journal.md`.

Publication records terminate rather than recurse forever: a substantive
checkpoint contains its intent and pre-publication gates; at most one
follow-up receipt commit records that checkpoint's actual publication.  Verify
the receipt commit externally and report it to the user, then record its SHA in
the next substantive journal entry.  Do not create an unbounded chain of
receipt-only commits.
