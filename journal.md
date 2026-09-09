# TalosFP Euler Engineering Journal

This is the append-only engineering journal for the `talosfp-euler` branch.
It records decisions, commands, observed results, proof boundaries, pushed
checkpoints, and unresolved failures.  The normative design remains
[`plans/euler-rusanov.md`](plans/euler-rusanov.md); this file records what was
actually attempted and established.

## 2026-09-04: Branch and scope

The branch `talosfp-euler` was created from `talosfp` revision `73012e1`,
whose next unfinished numerical checkpoint was the guarded quadratic Horner
artifact.  The Euler work therefore starts by completing Horner through the
same source-model, IEEE64, generated-WAT, and exact-execution path that the
Euler kernel will reuse.

The selected first Euler target is a guarded one-dimensional ideal-gas
Rusanov flux over primitive states.  It uses `gamma = 7/5`, fixed
`alpha = 7/4`, raw binary64 `UInt64` arguments, the already supported
binary64 addition and multiplication instructions, and exact sign-bit
toggling for negation.  The normalized input domain is

```text
1/8 <= rho <= 1
1/16 <= p <= rho
|u| <= 1/2
```

This domain contains the canonical Sod left and right states.  Its intended
real proof gives `sqrt((7/5) * p / rho) < 5/4`, hence
`|u| + c < 7/4`; the fixed dissipation parameter is therefore a proved signal
speed bound rather than an unexplained numerical constant.

The scope deliberately excludes the experimental self-hosted emitter,
componentwise reconstruction, native floating-point evaluation as proof
evidence, and release-receipt bookkeeping.  Native execution remains a
regression oracle.  The intended strong claim concerns the exact generated
Wasm program under Talos's modeled IEEE-754 semantics, with explicit guards,
finite results, quantitative roundoff bounds, termination, and store
preservation.  It will not be described as a certified PDE solution without
a separate discretization or convergence argument.

The detailed plan was added to `plans/euler-rusanov.md`, linked from
`plans/README.md`, summarized in `plan.md`, and recorded in `devnotes.md`.
The remote branch was checked by comparing complete Git tree identities.

Pushed checkpoints:

- `8da5b71`: `Plan verified Euler Rusanov artifacts`.
- `8a99e8d`: corrected a truncated `devnotes.md` blob created by the GitHub
  API upload; the cumulative tree was then byte-identical to the local tree.

The ordinary HTTPS Git remote in the first checkout had no credential helper.
The commits were therefore published through the authenticated GitHub Git-data
API and the branch ref was advanced only with non-forced fast-forwards.

## 2026-09-04: Guarded quadratic Horner source checkpoint

Added

```text
horner2CheckedBits x c2 c1 c0
```

to `LeanExe/Examples/Float64Bits.lean`.  On accepted inputs it computes the
explicitly staged expression

```text
(c2 * x + c1) * x + c0
```

using two `f64.mul` and two `f64.add` operations.  Every input must pass the
existing sign-cleared raw-bit `|value| <= 1/2` guard.  Rejection returns status
one and positive-zero result bits without entering the arithmetic branch.

Focused regression coverage in `test/f64_bits.js` includes two accepted exact
bit-pattern results, one rejection at each of the four argument positions,
the lowered-IR operation counts, absence of surviving intrinsic calls, and
the expected generated-WAT arithmetic/reinterpretation counts.

Checks completed before the first checkout disappeared:

```text
node --check test/f64_bits.js
git diff --check
```

Both passed.  Independent JavaScript binary64 calculations confirmed the two
accepted expected result words:

```text
bfd0000000000000
3fd8000000000000
```

This is regression evidence only, not part of the proof boundary.

Pushed checkpoint:

- `d596985`: `Add guarded quadratic Horner source`.

The source checkpoint is intentionally not marked complete in `plan.md` yet.
It still needs a Lean build, compiler execution, generated program, pure
IEEE64 theorem, exact WAT theorem, explicit small-step trace, store theorem,
and axiom audits.

## 2026-09-04: Lean runner failure and direct-run authorization

The repository-mandated command

```text
tools/leanrun --timeout 180s lake build LeanExe.Examples.Float64Bits
```

failed before invoking Lean:

```text
Failed to connect to bus: No medium found
```

Diagnostics showed that this execution container has no systemd user bus and
no `/run/user/0`; systemd is not running in the container.  No attempt was
made to weaken or bypass `tools/leanrun` until the user explicitly authorized
running Lean directly.  Following that authorization, direct Lean/Lake work
will remain serialized, use `LEAN_NUM_THREADS=1`, and use explicit timeouts.
The experimental self-host path remains excluded.

The first direct attempt used the `lake` elan shim:

```text
env LEAN_NUM_THREADS=1 NO_COLOR=1 timeout 300s \
  lake build LeanExe.Examples.Float64Bits
```

It failed immediately with:

```text
error: could not detect the configuration of the Lake installation
```

`elan which lake` nevertheless resolved the exact requested toolchain binary:

```text
/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lake
```

The next diagnostic will invoke that exact binary directly, avoiding the elan
shim while preserving the pinned Lean version.

## 2026-09-04: Scratch workspace pruning and recovery

Automated workspace maintenance removed the entire first local checkout,
including `.git`, between turns.  This was not a repository command and was
not initiated by the user.  No branch work was lost because all coherent
changes had already been pushed through `d596985`.

The repository was restored by cloning the remote `talosfp-euler` branch.
The recovered checkout is clean at `d596985`; `git fsck --no-dangling`
completed successfully.  Because the scratch filesystem is not durable, every
coherent future checkpoint will be committed and pushed promptly.  Unchecked
work will be identified explicitly rather than silently presented as proved.

## Next actions

1. Run the focused source build with the exact Lake binary and then execute
   `node test/f64_bits.js`.
2. Add and check the reusable binary64 half-bound and two-stage Horner
   numerical lemmas.
3. Register and prepare `f64_horner2_checked_bits`, allowing the compiler to
   generate `Project/F64Horner2CheckedBits/Program.lean`.
4. Prove total exact WAT behavior, store preservation, the accepted numerical
   result, and the explicit small-step trace; audit public axioms.
5. Mark Horner complete, update this journal and the plans, commit, and push.
6. Add the separate guarded Euler/Rusanov source module and focused Wasm tests.

## 2026-09-04: Local-only Lean execution restored

The user clarified that this environment has no `dev` host and that every
Lean-related command must run locally.  This is now an explicit project rule:

- do not invoke or probe `tools/leanrun-dev`;
- do not claim that a remote runner is available;
- run Lean, Lake, `lean-wasm`, Node regressions, and Wasmtime locally;
- use GitHub only to publish the requested branch checkpoints.

A brief attempted `tools/leanrun-dev` invocation before that clarification
failed at DNS resolution and produced no repository change.  It will not be
retried.

The direct Lean/Lake failure was traced to the executor's nested PID namespace.
The process sees its namespace PID from `getpid()`, while the mounted `/proc`
belongs to the parent namespace.  Lean 4.34 resolves its executable using a
path of the form `/proc/<getpid()>/exe`; that path does not exist here even
though `/proc/self/exe` does.  This explains both earlier direct-run errors:

```text
Lean: failed to locate application
Lake: could not detect the configuration of the Lake installation
```

For this scratch session only, a small local `LD_PRELOAD` shim intercepts a
failed `readlink("/proc/<pid>/exe", ...)` and retries
`readlink("/proc/self/exe", ...)`.  The shim and the wrapper scripts live
under `/tmp`, are not project source, and are not part of the trusted result.
They only make the pinned local executable discover its own installation.

The repaired local toolchain reports:

```text
Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu,
commit 6a10ac8c22beadecabdbb0919c2b50214762f91d)
```

All Lean-family runs remain serialized with `LEAN_NUM_THREADS=1` and explicit
timeouts.  With the local shim active, the focused source build succeeded:

```text
lake build LeanExe.Examples.Float64Bits
Build completed successfully (3 jobs).
```

The full local compiler build also succeeded:

```text
lake build lean-wasm
Build completed successfully (58 jobs).
```

Only pre-existing deprecation warnings were emitted by that build.

## 2026-09-04: Local Horner Wasm regression passes

The restored scratch checkout did not initially contain the ignored Wasmtime
tools.  `tools/download-wasmtime.sh` downloaded the pinned Wasmtime 44.0.0
archives and verified their repository-recorded SHA-256 digests.  The first
extraction encountered an ownership-change error in this container; rerunning
with `TAR_OPTIONS=--no-same-owner` completed the local installation.  These
downloaded tools remain ignored scratch build products.

`tools/run-process.js` routes executables whose basename is `lean`, `lake`, or
`lean-wasm` through `tools/leanrun`.  To exercise the unmodified regression
locally under the user's direct-run authorization, the test was given a
temporary `/tmp` symlink to the locally built `lean-wasm` with a different
basename.  A temporary PATH wrapper applies the same local `/proc/self/exe`
shim when `lean-wasm` starts its Lean subprocess.  No repository test harness
or runner policy was changed.

Static inspection subsequently established the cleaner setting for future
runs.  `Lean.findSysroot` checks `LEAN_SYSROOT` before falling back to a
literal `lean --print-prefix` subprocess.  Setting

```text
LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2
```

therefore avoids that subprocess entirely; the temporary PATH wrapper is not
needed when `LEAN_SYSROOT` is present.  The outer `lean-wasm` still needs a
non-guarded temporary basename because `tools/run-process.js` otherwise sends
it through the unavailable systemd runner.  `test/wasmtime_host.js` locates
the local host through `LEANEXE_WASMTIME_HOST` or its checked default under
`build/tools`; it does not consume a `WASMTIME` environment variable.

The complete focused regression then passed locally:

```text
node test/f64_bits.js
checked Float64 bit-pattern execution, lowering, emission, annotations, and image rejection
```

This exercises `horner2CheckedBits` through source compilation, lowering,
binary and text Wasm emission, Wasmtime execution, annotation checks, expected
instruction counts, guard rejection, and the expected `compile-image`
rejection for unsupported f64 image instructions.  It establishes a tested
source/Wasm checkpoint, but it is still not the Talos exact-code theorem or
the numerical error proof.

The next implementation step is the reusable binary64 half-bound/Horner
numerical lemma layer, followed by Talos case registration and generated
program proofs.

## 2026-09-04: Local Talos proof environment restoration

The replacement scratch checkout had no ignored
`proofs/talos/lean/.lake/packages` directory.  A local `lake update` checked
out the exact revisions already pinned by `lake-manifest.json`, including
Talos/CodeLib `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`, Iris, Mathlib, Batteries,
Qq, Plausible, LeanSearchClient, ImportGraph, ProofWidgets, Aesop, and Cli.
It then failed in Mathlib's post-update cache hook with:

```text
leantar not found in Lean sysroot
```

The binary was present in the pinned toolchain.  The cache hook itself runs a
literal `lean --print-prefix`, so this was another consequence of the local
`/proc/<pid>/exe` problem, not an absent `leantar`.  Placing the temporary
local Lean wrapper first in `PATH` fixed that discovery step.

An unqualified rerun of the post-update hook requested 8,747 Mathlib cache
files.  It was interrupted after 149 files because that was needlessly broad
for this checkpoint.  The focused local command

```text
lake exe cache get Mathlib.Tactic
```

downloaded and decompressed the 2,959 files in the actual transitive import
set in 334.107 seconds.  Dependency sources and cache products are ignored
local build state; the manifest did not change.

The first combined build of the two new modules and compatibility layer
reached its 300-second limit after compiling interpreter dependencies through
`Interpreter.Wasm.Semantics`, without reaching the new sources.  Following
the repository's timeout guidance, the unchanged target was not repeated.
The build was divided at reusable module boundaries:

- `CodeLib.Numerical.ErrorComposition` completed in 3.2 seconds;
- `CodeLib.IEEE64.Operations` first reached a 300-second limit below that
  module, still without a source diagnostic;
- the isolated `CodeLib.IEEE64.Roundoff` target revealed and completed the
  cold bottleneck: `Interpreter.Wasm.SmallStep` took 350 seconds, followed by
  IEEE32 and IEEE64 roundoff in 6.2 and 5.3 seconds;
- the direct IEEE64 rounders and Float64 example dependencies then completed
  in 17.1 seconds;
- `CodeLib.IEEE64.Operations` completed in 5.4 seconds;
- `CodeLib.Numerical.Kernels` completed in 4.9 seconds.

All of those commands ran locally and serially with the pinned toolchain,
`LEAN_NUM_THREADS=1`, the local executable-discovery shim, and explicit
timeouts.  The only dependency warnings were pre-existing deprecations and
linters.

## 2026-09-04: Reusable binary64 Horner numerical proofs

Added `Project.ProofKit.F64Bounds`.  It owns the raw sign-bit-clearing
half-unit guard and proves that every accepted word is finite with modeled
real magnitude at most `1/2`.  The proof is the existing integer IEEE-754
argument extracted from the dot-product case; it does not evaluate native
floating point.  `Project.F64Dot2CheckedBits.Bounds` now provides thin
compatibility aliases, and rebuilding the existing dot numerical theorem
confirms that the extraction did not break that accepted source proof.

Added `Project.ProofKit.F64Numerical` with:

- `hornerStepBits`, the modeled binary64 multiply-then-add stage;
- `horner2Bits`, two explicitly rounded stages;
- `horner64_step_real_error`, proving a finite result and a local `2ε`
  absolute-error bound from finite unit-bounded operands and product;
- `horner2_real_error_of_half`, proving the guarded quadratic result finite
  and within `3ε` of `(c₂*x + c₁)*x + c₀`.

The quadratic proof reserves explicit headroom at every operation.  The first
exact product is at most `1/4`; its rounded product remains within one.  The
first exact multiply-add target is at most `3/4`; its rounded result remains
within one.  Multiplying that rounded accumulator by `|x| ≤ 1/2` gives the
second product headroom.  Finally, `CodeLib.Numerical.horner_two_step`
attenuates the first `2ε` stage error by `1/2` before adding the second `2ε`,
which yields the sharp `3ε` bound.  This is why a generic unit-interval
argument, which would only yield `4ε`, was not used.

The first elaboration found three addition-orientation mismatches in proof
terms using `add_le_add_right`.  Replacing those with componentwise
`add_le_add` fixed the proof; no statement or numerical budget changed.

Focused local builds now pass for:

```text
Project.ProofKit.F64Bounds
Project.ProofKit.F64Numerical
Project.F64Dot2CheckedBits.Numerical
```

The two new public numerical theorems and the extracted guard theorem report
only the standard logical axioms `propext`, `Classical.choice`, and
`Quot.sound`.  No `sorryAx` appears.  This checkpoint supplies the pure-model
numerical layer; the guarded source contract and generated-WAT execution proof
remain the next work.

Both modules were added to the canonical `leanexegen` ProofKit allowlist and
source-identity list, and their supported interfaces were documented in the
ProofKit catalog.  This makes them available to an exact-artifact proving task
without granting unrestricted imports; the generated proof still has to match
the frozen decoded program independently.

The ProofKit/tooling and maintained-document checks passed:

```text
node test/leanexegen.js
leanexegen Codex protocol, package, publication, and exit tests passed

node tools/check-docs.js
Checked 90 maintained Markdown files

node --check tools/leanexegen-lib.js
git diff --check
```

`plan.md` now records this verified intermediate state without marking the
quadratic Horner artifact complete; generated-program execution, the explicit
trace, and exact-byte closure are still outstanding.

## 2026-09-04: Standing operating protocol

The following rules consolidate the user's operational directions and remain
in force for all subsequent `talosfp-euler` work:

- The work happens in the local checkout on branch `talosfp-euler`, which was
  created from `talosfp`.  There is no `dev` host.  Do not invoke, probe, or
  imply the availability of `tools/leanrun-dev` or any other remote executor.
- Run Lean, Lake, `lean-wasm`, Node regressions, Wasmtime, artifact generation,
  and proof checking locally.  Lean-family processes must be serialized, use
  `LEAN_NUM_THREADS=1`, and have explicit timeouts; do not launch concurrent
  Lean builds.
- The existing `tools/leanrun` cannot create its required systemd user scope
  in this container.  The user explicitly authorized direct local Lean.  Use
  the exact pinned Lean 4.34.0-rc2 binaries and `LEAN_SYSROOT`, together with
  the session-local executable-discovery shim when required.  Do not silently
  pretend that unavailable cgroup limits were applied.  Any repository runner
  adaptation must be an explicit, documented local-only mode that preserves
  locking, timeouts, `nice`, and `ionice` where possible.
- GitHub is a publication boundary, not a compute host.  Because ordinary
  HTTPS Git credentials are unavailable in this checkout, publish local
  commits through the authenticated GitHub Git-data API using non-forced
  fast-forward ref updates.  After each publication, fetch the remote branch,
  reconcile the local commit, compare complete Git tree identities, and check
  that the worktree is clean.
- Treat the active checkout as persistent, user-owned project state.  External
  workspace maintenance already deleted the first checkout, including `.git`;
  it was not initiated by the user or by a repository command.  Do not run
  workspace cleanup or delete, reset, or overwrite user files.  Inspect
  repository status before mutations, preserve unrelated changes, and commit
  and push every coherent checkpoint promptly so another external prune cannot
  erase accepted work.
- Keep this journal detailed and append-only.  Record decisions, relevant
  commands and environment workarounds, timings or timeouts, warnings,
  failures, proof boundaries, axiom reports, commit identifiers, remote tree
  verification, and the precise next incomplete step.  Never promote a native
  or Wasmtime regression result into proof evidence.
- The experimental self-hosted emitter is outside this branch's validation
  path.  Hash, manifest, release-receipt, and self-host bookkeeping are not
  gates here.  Exact generated program bytes remain proof inputs whenever an
  exact-artifact theorem is claimed.

These rules supersede the generic runner wording in repository documentation
where that wording assumes a working systemd user bus.  They do not weaken the
mathematical, generated-WAT, exact-byte, no-`sorry`, or axiom-audit gates.

## 2026-09-04: Guarded Horner source-model contract

Registered `f64_horner2_checked_bits` as an incomplete Talos case and added its
source-facing contract under `Project.F64Horner2CheckedBits`.  The accepted
branch fixes status zero, the two-stage pure IEEE64 Horner result, finiteness,
and the sharp `3 * 2^-52` real absolute-error bound.  The rejected branch fixes
status one and positive-zero result bits.  Registration remains incomplete so
the absent generated-WAT theorem cannot be mistaken for finished evidence.

The focused local build used the pinned toolchain directly, with
`LEAN_SYSROOT`, the session-local `/proc/self/exe` shim,
`LEAN_NUM_THREADS=1`, and a 300-second timeout:

```text
lake build Project.F64Horner2CheckedBits.Numerical
Build completed successfully (3068 jobs).

lake build Project.F64Horner2CheckedBits.Spec
Build completed successfully (3069 jobs).
```

The targets themselves built in 3.2 and 2.9 seconds after replaying cached
dependencies.  The public theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` appears.  `Program.lean`, generated-WAT execution,
the explicit trace, store preservation, and exact-byte closure remain pending.

The durable checkpoints published after the original Horner source commit
were:

- `5f2987d`: `Add TalosFP Euler engineering journal`;
- `e592f25`: `Journal local Lean execution and Horner regression`;
- `da6f3a3`: `Add reusable f64 Horner numerical proofs`.

The current published baseline before this checkpoint is
`da6f3a3cc1dc7b9a8365e5228444508cb65ca2b7`, whose complete local and remote
tree is `db4587db2dc08ef2f76a6d36d1adaa68943ab1f7`.

`tools/talos-artifact.js` currently reaches `tools/leanrun` through
`tools/talos-lib.js`.  That path fails before Lean because this container has
no systemd user bus.  Before preparing the Horner artifact, add or use an
explicit opt-in local execution route that retains serialization,
`LEAN_NUM_THREADS=1`, explicit timeouts, and the available lock, `nice`, and
`ionice` controls.  Do not use a remote runner and do not impersonate a
successful systemd scope.  The exact route and its checks must be recorded
before claiming artifact preparation passed.

Registration before program generation deliberately leaves several aggregate
checks open: runtime checks cannot import and pin the absent generated
`Program.lean`, artifact identity has no tracked program yet, and the declared
WAT behavior theorem does not exist.  The self-host corpus also expects a
registry artifact for every case, but self-host validation is excluded from
this branch.  None of these open gates is being reported as a pass; they close
only after local artifact generation and the execution proof.

Current next actions are:

1. Publish this registered, locally checked source-contract checkpoint and its
   consolidated operating rules.
2. Resolve the local artifact-runner path explicitly and generate, rather than
   handwrite, `F64Horner2CheckedBits/Program.lean`.
3. Prove all five generated-WAT paths, exact results, store preservation, the
   transferred `3 * 2^-52` result, and an explicit small-step trace.
4. Close the exact-byte package and only then mark the Horner case complete.
5. Begin the separately registered Euler/Rusanov source and Wasm regression.

## 2026-09-04: Explicit local `leanrun` mode

The source-contract and operating-rules checkpoint was published as
`570d7eb1b517ed0a27b3123ac4b7d0e99eeea4b2`.  The remote and reconciled local
trees both equal `a2cf08a555eb0c7d02c0b00981131d2b3ad230a6`, and the worktree was
clean after fetch and rebase.

Added an explicit `LEANRUN_LOCAL=1` mode to `tools/leanrun` for the user's
authorized local-only execution environment.  Standard behavior is unchanged
and still fails closed through `systemd-run`.  The local mode validates its
opt-in value, selects the pinned toolchain, exports `LEAN_NUM_THREADS=1`, takes
the existing machine-wide `flock`, and runs under the requested timeout,
`nice -n 10`, and `ionice -c 3`.  It prints a conspicuous warning that the
unavailable cgroup CPU, memory, and swap limits are not enforced; it never
activates automatically.

The local child receives an internal marker.  If it invokes `tools/leanrun`
again, the nested runner fails immediately with an explanatory error instead
of waiting on the parent's non-reentrant lock.  Runner-calling repository
drivers must therefore be invoked directly with `LEANRUN_LOCAL=1` in their
environment.  `tools/talos-lib.js` already forwards the environment to each
sequential child, so the artifact driver requires no special-case code.  This
mode does not use or inspect `tools/leanrun-dev`.

Added `test/leanrun_local.js` with a temporary fake toolchain and a fake
`systemd-run` sentinel.  Without running Lean, it proves that explicit local
mode reaches the requested command, exports the one-thread and cache settings,
does not call `systemd-run`, rejects an invalid mode with status two, enforces
the child timeout with status 124, preserves the standard-mode `systemd-run`
path, and rejects nesting with status one.  It is
registered in `test/run_all.js` immediately after the existing runner-routing
test.  The focused checks pass:

```text
sh -n tools/leanrun
node --check test/leanrun_local.js
node test/leanrun_local.js
checked leanrun opt-in local execution, standard-mode preservation, validation, timeout enforcement, and nesting rejection
```

The first real proof check through the new route also passed locally:

```text
LEANRUN_LOCAL=1 tools/leanrun --timeout 120s \
  lake -d proofs/talos/lean --no-ansi build \
  Project.F64Horner2CheckedBits.Spec
leanrun: LEANRUN_LOCAL=1; cgroup CPU, memory, and swap limits are not enforced
Build completed successfully (3069 jobs).
```

The environment also supplied the exact `LEAN_SYSROOT` and the session-local
`/proc/self/exe` compatibility shim described earlier.  The next action is to
invoke `tools/talos-artifact.js prepare f64_horner2_checked_bits` directly with
this local mode, inspect the exact emitted program, and add its runtime pins.

## 2026-09-04: Official `wasm-tools` version compatibility

The first local Horner artifact preparation attempt stopped before any build
or output replacement because the restored scratch checkout had no
`wasm-tools` executable.  No tracked or generated artifact was changed:

```text
talos-artifact.js: wasm-tools 1.251.0 was not found; install it or set WASM_TOOLS
```

Downloaded the upstream Bytecode Alliance
`wasm-tools-1.251.0-x86_64-linux.tar.gz` release into temporary/local ignored
tool storage.  Its SHA-256 matched the digest published on the immutable
GitHub release:

```text
08d523676ec71d9afbae05aa4255041ce91bf2d325d87b7e722d190d558be689
```

The official executable reports:

```text
wasm-tools 1.251.0 (a1a178a02 2026-05-28)
```

That exposed a repository checker bug: the configured version was correct,
but `tools/check-wasm-tools-version.sh` and the conformance driver accepted
only the shorter `wasm-tools 1.251.0` spelling.  Updated both checks to accept
either that exact compact line or the official release's strictly shaped
lowercase commit-hash/date suffix.  The numeric version must still equal the
repository pin; arbitrary suffixes, multiple lines, and wrong versions remain
rejected.

Added `test/wasm_tools_version.js` and extended the conformance parser test.
They cover the compact form, the actual official metadata form, a wrong
version, and malformed trailing data.  The focused checks pass:

```text
node test/wasm_tools_version.js
checked wasm-tools exact and official release versions plus wrong and malformed rejection

node test/artifact_conformance.js
checked conformance parsing, known issues, official validator cases, and file selection

WASM_TOOLS=build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  tools/check-wasm-tools-version.sh
checked wasm-tools 1.251.0
```

The downloaded archive and extracted executable are ignored local scratch
products, not repository sources or proof evidence.  Artifact preparation is
ready to retry after this compatibility checkpoint is published.

## 2026-09-04: Local-only operating record and first generated Horner program

The following rules are standing instructions for all remaining work on
`talosfp-euler`, not optional preferences:

1. The active checkout must not be subjected to cleanup, workspace
   maintenance, pruning, reset, checkout-overwrite, or recursive deletion by
   the assistant.  One prior scratch checkout, including its `.git` directory,
   was already removed by external workspace maintenance.  That event does not
   authorize deletion of this checkout, including its ignored caches.  Every
   coherent source or proof checkpoint is journaled, committed, and pushed
   promptly.  Unrelated user changes are preserved.
2. There is no `dev` host.  Do not invoke or probe `tools/leanrun-dev`.  Lean,
   Lake, `lean-wasm`, Node, Wasmtime, artifact preparation, and proof checking
   run locally.  GitHub is only the publication and recovery boundary.
3. The user explicitly authorized direct local Lean.  Use the opt-in
   `LEANRUN_LOCAL=1` path with the pinned sysroot, shared `flock`,
   `LEAN_NUM_THREADS=1`, `nice`, `ionice`, and an explicit timeout.  Its warning
   that systemd cgroup CPU, memory, and swap limits are unavailable is factual
   and must not be hidden.  Never nest `tools/leanrun` under a local runner.
4. Only one Lean/Lake process may run at once.  Delegated proof tasks share the
   same serialized slot.  After a timeout, do not rerun the unchanged target;
   first split or build a dependency boundary and record what changed.
5. Self-host validation, hashes, manifests, and release receipts are not phase
   gates.  Exact program bytes remain theorem inputs whenever exact-artifact
   behavior is claimed.

The local commands in this environment use the following essential shape:

```text
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  tools/leanrun --timeout <seconds>s lake ...
```

The session-local preload is required because Lean 4.34.0-rc2 discovers its
executable through `/proc/<getpid()>/exe`, while this container is inside a
nested PID namespace.  The first shim redirected that path only when the raw
`readlink` returned `ENOENT`.  That was insufficient: if the same numeric PID
existed in the outer namespace, the lookup succeeded but named the wrong
executable, producing intermittent `failed to locate application` errors.
The corrected temporary shim always maps numeric `/proc/<digits>/exe` requests
to `/proc/self/exe`.  Both `lean --version` and `lake --version` then passed.
The shim is an untracked environment workaround, not repository source or
proof evidence.

The official upstream `wasm-tools` release used for artifact generation is
version `1.251.0`; its executable reports
`wasm-tools 1.251.0 (a1a178a02 2026-05-28)`.  The downloaded archive matched
the official SHA-256
`08d523676ec71d9afbae05aa4255041ce91bf2d325d87b7e722d190d558be689`.
The extracted ignored executable is
`build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools`.  It passes the fixed
strict version checker committed in `416b0fa`.

The first Horner artifact-generation attempt with that tool completed the
pinned Talos verifier's cold build.  The verifier completed 53 jobs; compiling
`Verifier.Emit:c.o` alone took approximately 440 seconds.  The subsequent root
source/compiler build stopped once with
`could not detect the configuration of the Lake installation`, so the
transactional staging directory did not replace any generated artifact.  The
exact root build command was then isolated under the same local runner and
environment and passed in 0.7 seconds.  One full artifact-generation retry was
therefore made; its verifier build completed 52 cached jobs, its root build
completed 59 jobs, and preparation passed for the single registered Horner
case.  It generated, rather than hand-authored:

```text
proofs/talos/lean/Project/F64Horner2CheckedBits/Program.lean
proofs/talos/.generated/f64_horner2_checked_bits/program.wasm
proofs/talos/.generated/f64_horner2_checked_bits/program.wat
```

The latter two paths are ignored working products.  Independent inspection
gave these identities:

```text
program.wasm  1237 bytes  sha256 8c665a1634643065c35e3ed7a81bf8538e4a8e264cb240fcc1ad3494b41757bd
program.wat  11383 bytes  sha256 df55f1f5370319078cfa07ce9b2a78b515fb9ed770ba0a33164e878390c0712d
Program.lean 11369 bytes  sha256 1c88282f23c425b18972901cefbfdebd8ab3774993a409b2a08ac9d82fdea9c8
```

`wasm-tools validate` accepted the binary, and `wasm-tools print` reproduced
the retained WAT text exactly.  The module has no imports, table, start, data,
elements, or custom sections.  Function zero is the one-local finite-and-half-
unit guard; function one is the four-argument/two-result Horner entry; functions
two through five are the existing allocation, reset, retain, and release/free
runtime helpers.  Runtime pins now name those exact definitions.

The source parameter order is `(x, c₂, c₁, c₀)` and the host result order is
`(status, bits)`.  Talos receives the top-first stack `[c₀, c₁, c₂, x]` and
returns `[bits, status]`.  Four guard calls short-circuit in that order.  The
guard accepts exactly when
`(bits & 0x7fff_ffff_ffff_ffff) <=ᵤ 0x3fe0_0000_0000_0000`.
The accepted body contains exactly two `f64.mul`, two `f64.add`, eight
`f64.reinterpret_i64`, and four `i64.reinterpret_f64` instructions and computes
the staged DAG `(c₂*x+c₁)*x+c₀`, with a raw-bit round trip after every
operation.  No fused multiply-add or reassociation occurs.  Every rejection
returns status one and positive-zero bits.

The first aggregate `Project.Runtime.Checks` build exposed the intermittent
wrong-executable behavior of the original preload shim.  After correcting the
shim, a fresh 300-second run progressed through roughly 2,490 cold Mathlib
modules with no runtime-pin or theorem diagnostic, then reached its declared
timeout.  This is recorded as a timeout, not a pass.  In accordance with the
no-unchanged-retry rule, the next runtime check will first build a smaller
dependency boundary before revisiting the aggregate.

At this documentation checkpoint, the generated program and runtime pins are
present locally, and a draft big-step/WP execution proof is undergoing its
first focused serialized build.  No execution-proof pass is claimed here.
The case remains registered with `complete: false`; the explicit small-step
trace and exact-byte package remain open after the big-step proof.

## 2026-09-04: Generated-WAT Horner execution proof

The preceding operating record was published first as the documentation-only
commit `a24b1348f840990f7f184f7c96270da660ebaf17`.  Its complete Git tree is
`dcfd6ebfc97d521fd4fb3f32b33db12fb15b9a90`; local `HEAD`, the remote
`talosfp-euler` ref, and that tree were checked equal without rewriting the
in-flight proof worktree.

The first focused `Project.F64Horner2CheckedBits.Execution` build reached its
300-second timeout while still continuously compiling cold Mathlib imports at
approximately 2,594 modules.  It emitted no Horner diagnostic, so this was
recorded as an infrastructure/dependency timeout rather than a proof result.
The target was not repeated unchanged.  The smaller dependency boundary was
built first:

```text
lake -d proofs/talos/lean --no-ansi build \
  Project.F64Horner2CheckedBits.Numerical
Build completed successfully (3068 jobs).
```

That cached build took approximately 2.6 seconds and continued to report only
`propext`, `Classical.choice`, and `Quot.sound` for the numerical theorem.  A
single Execution retry then filled the additional cold WP/Tactic frontier,
reached the generated Horner module at roughly job 3,361 of 3,366, and exposed
five identical proof-structure errors rather than timing out.  In each guard
path, a final conditional boundary copied from the older dot proof had already
been consumed by `wp_run` under the current Talos compatibility layer.

The first correction removed only the redundant `wp_iff_cons`; the next
8.5-second build showed that its associated final `rw [if_*]` and `wp_run`
pair was also redundant.  Removing exactly those five endpoint pairs while
retaining every earlier control refinement produced the passing proof:

```text
lake -d proofs/talos/lean --no-ansi build \
  Project.F64Horner2CheckedBits.Execution
Build completed successfully (3366 jobs).
```

The final build took 8.9 seconds, with approximately 6.2 seconds on the target.
It proves the exact helper result, fuel-independent total execution of all five
entry paths, the reversed Talos input/output stack convention, exact staged
Horner result bits, complete store preservation, and the transferred finite
result plus `3 * 2^-52` real absolute-error contract.  Axiom reports for
`func0_exact`, `horner2CheckedBits_exact`, and
`horner2CheckedBits_wat_real_error` are each exactly the standard logical
axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.

This is a big-step/WP checkpoint, not case completion.  The generated program,
the passing execution proof, its public import, and the generated-program audit
are ready to publish together.  Runtime-pin aggregate checking, the separately
drafted explicit small-step trace, and exact-byte closure remain pending, so
the registry remains `complete: false`.

## 2026-09-04: Horner runtime-helper pins

The generated-program and big-step/WP execution checkpoint was published as
`fd1ed79b2fb26ed211aeb4470f9b9c9a11e5a300`.  Its complete local and remote
Git tree is `c2d1b2e412d3f6ea5933f55d356188cabc163c30`.

The earlier cold `Project.Runtime.Checks` timeout was not repeated unchanged.
After the Horner execution dependencies had been built, the runtime definition
boundary was checked first under the same serialized local runner:

```text
lake -d proofs/talos/lean --no-ansi build Project.Runtime.Defs
Build completed successfully (3341 jobs).
```

The target took approximately 3.6 seconds and the full command approximately
6.2 seconds; only existing deprecation warnings were replayed.  The aggregate
was then retried once against that materially warmed dependency state:

```text
lake -d proofs/talos/lean --no-ansi build Project.Runtime.Checks
Build completed successfully (3366 jobs).
```

The aggregate spent approximately 96 seconds compiling its pinned generated
Program dependencies, then checked its target in approximately 3.3 seconds.
There were no pin or proof errors.  The Horner module is therefore checked to
reuse exactly `allocFuncDef`, `resetFuncDef`, `retainFuncDef`, and
`releaseFuncDef 5` at function indices two through five, after erasing only the
module-local type index.  This closes the generated-runtime-helper boundary;
the explicit small-step trace and exact-byte gate remain open.

## 2026-09-04: Explicit Horner small-step trace

The runtime-helper checkpoint was published as
`68b0020ab424040c0c206d04b9b556417453aeaf`, with identical local and remote
tree `bd3bf322345ba8ac1d5366afaef4a10f5dc672aa`.

Added an independent 801-line relational trace for the generated Horner entry.
It does not reuse the big-step/WP execution result.  A generalized private
helper proves the exact twelve transitions of each call to the generated
raw-bit guard across arbitrary caller continuations, value tails, control
frames, and call frames.  The public trace then enumerates every generated
instruction and administrative transition on all five semantic paths:

| Path | Exact transitions |
| --- | ---: |
| reject `x` | 47 |
| reject `c₂` | 64 |
| reject `c₁` | 81 |
| reject `c₀` | 98 |
| accept | 118 |

The accepted path visibly contains all four helper calls and all 24 arithmetic
body instructions; its floating steps use Talos's modeled scalar unary and
binary transitions.  The rejection paths visibly short-circuit the remaining
guards and execute no floating arithmetic.  Every path finishes with the
modeled `[bits, status]` stack and the complete initial machine store.

The first focused build reached `Trace.lean` in 6.5 seconds and failed after
9.1 seconds total because the dependent `.call` step had not fixed its callee
to the exact generated `func0Def`, and the generalized helper's caller state
was not inferable at its composed call sites.  Making those caller arguments
implicit and instantiating the exact helper function removed all entry-path
composition errors.  The second focused build failed after 12.4 seconds only
inside the helper: its `leUI64` result needed an explicit raw-bit guard
comparison, and return needed explicit normalization of the one-parameter
`List.drop`.  Those two local normalizations produced the passing build while
leaving every trace definition and path length unchanged:

```text
lake -d proofs/talos/lean --no-ansi build \
  Project.F64Horner2CheckedBits.Trace
Build completed successfully (3365 jobs).
```

The passing command took 12.8 seconds, including approximately 10 seconds on
the target.  `horner2CheckedBits_steps`,
`horner2CheckedBits_smallStep_exact`, and
`horner2CheckedBits_smallStep_real_error` each report only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.  The public proof
root now imports both the big-step execution proof and this trace, and its
focused integration build also passes:

```text
lake -d proofs/talos/lean --no-ansi build \
  Project.F64Horner2CheckedBits.Spec
Build completed successfully (3368 jobs).
```

That integration command took 5.74 seconds, including approximately 3.2
seconds on the target.  Exact-byte closure is now the only remaining Horner
case-completion gate; the registry intentionally remains `complete: false`.

## 2026-09-04: Horner completion boundary corrected and focused gate passed

The explicit-trace checkpoint was published as
`5379c580236d093946a54c06742219466430ae0a`, with identical local and remote
tree `e5061cb147b8a6ca4bd8d0800125897d9cbfe3e1` and a clean worktree.

Before creating a frozen Horner package, the exact-artifact registry, all three
previous completed f64 cases, the migration generator, and the checked-in Euler
plan were audited together.  That audit corrected the final sentence of the
preceding entry: Horner's established completion boundary is source-driven
generated-WAT semantics, exactly like `F64MulBits`, `F64Dot2CheckedBits`, and
`F64DotCheckedBits`.  None of those cases has an `Artifact*.lean` package or an
entry in `proofs/artifacts/registry.json`.  `plans/euler-rusanov.md` explicitly
reserves the first f64 exact-byte package for the Euler flux so that the actual
deliverable, rather than the phase-7 calibration kernel, exercises the full
decoder/validator/translation path.

`tools/artifact-migrate.js migrate f64_horner2_checked_bits` was therefore not
run.  A preliminary manual package draft was stopped before it changed the
shared checkout.  This avoids both silently moving the planned exact-byte
milestone and falsely suggesting that the current twenty-package aggregate is
ready under the new FP Talos pin: those historical manifests still describe
the pre-FP verifier inputs and require a separate migration if their aggregate
gate is revived.  No cleanup, deletion, reset, or worktree rewrite was used.

Horner was instead marked complete in `proofs/talos/cases.json` and its public
`Spec` was added to `Project.lean` in the same change.  JSON parsing and the
static aggregate-import check passed, with 24 completed source-driven cases.
The case README and phase plans now distinguish this regenerated-WAT theorem
from the first frozen f64 package still required for Euler.

The focused source-driven gate was invoked directly so that its child runner
could take the single local lock:

```text
LEANRUN_LOCAL=1 \
LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
WASM_TOOLS=build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
tools/talos-proof.js check f64_horner2_checked_bits
```

It accepted official `wasm-tools` 1.251.0, rebuilt 52 cached verifier jobs and
59 compiler/source jobs, regenerated the 1,237-byte WASM and WAT in
transactional staging, required the emitted `Program.lean` to equal the
tracked generated cache, and rebuilt the 3,368-job public specification.  It
finished with:

```text
Build completed successfully (3368 jobs).
Talos proof passed: f64_horner2_checked_bits
```

The tracked program did not change, so the audited WASM digest remains
`8c665a1634643065c35e3ed7a81bf8538e4a8e264cb240fcc1ad3494b41757bd`.
Only existing deprecation/linter warnings were replayed.  The 24-case aggregate
source-driven gate remains to be run after this focused completion checkpoint
is published; no aggregate pass is claimed yet.

## 2026-09-04: First 24-case aggregate attempt split at its time boundary

The Horner completion checkpoint was published as
`0b8aa0a50bb7be3d495f225bde787b4cd9705df7`, with identical local and remote
tree `dcaacc7cb8219656f25281a9c3d02565d3cf0ab0` and a clean worktree.  The
24-case source-driven aggregate was then started locally with the pinned
toolchain, corrected PID-namespace preload, official `wasm-tools` 1.251.0,
`LEANRUN_LOCAL=1`, and the driver-managed single Lean slot:

```text
LEANRUN_LOCAL=1 \
LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
WASM_TOOLS=build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
tools/talos-proof.js check --all
```

All twenty-four registered cases were compiled and regenerated serially.  Each
candidate `Program.lean` was required to equal its tracked generated cache, and
all twenty-four comparisons passed before the aggregate proof build began.
The cold `Project` build then progressed without a theorem diagnostic through
3,442 of an eventually discovered 3,719 jobs.  Its last completed target was
`Project.ClobQuote.Epilogue`; Lake then stopped because the aggregate driver's
declared 20-minute `tools/leanrun` limit expired:

```text
talos-proof.js: aggregate Talos proof build: tools/leanrun failed with exit status 124
```

This is a timeout, not a proof failure and not an aggregate pass.  The only
diagnostics before it were existing deprecation and linter warnings.  The
worktree remained clean; no cleanup, maintenance, deletion, reset, or
checkout-overwrite was performed.  In accordance with the standing operating
rule, the identical aggregate target will not be repeated against unchanged
dependency state.  The remaining cold specification boundary will be split
and built through focused local targets first; only the resulting materially
warmed cache permits one later aggregate retry.

## 2026-09-04: Focused F64Dot2 integration repair

The aggregate-timeout record was published as
`0da4a31ae0aac4e697b55e6b8da880f7f1c8b0f2`, with identical local and remote
tree `1887610e3694672b87c4eb5bec7b7f48c40e3eaf`.  The first missing numerical
boundary was then built separately rather than repeating the aggregate:

```text
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build \
  Project.F64Dot2CheckedBits.Spec
```

That focused build reached `F64Dot2CheckedBits.Execution` and exposed a real
integration regression.  The earlier shared-bounds refactor changed the
case-local `Bounds.f64AbsBits` and `Bounds.boundedByHalfBits` definitions into
one-layer `abbrev` compatibility aliases.  The execution proof's old simp
sets still named those aliases.  Elaboration had already reduced them to the
canonical `Project.ProofKit.F64Bounds` constants, so the generated raw mask
expression and Boolean guard were not unfolded.  Lean reported two direct
type mismatches followed by four unsolved branch endpoints.  This first run is
a proof failure, not a pass.

The repair changes only those seven simp-set references to name the canonical
ProofKit definitions: two `f64AbsBits` uses in the generated helper proof and
five `boundedByHalfBits` uses closing the accepted/rejected entry paths.  It
does not change a theorem statement, generated program, modeled arithmetic,
or branch structure.  An independent read-only audit reached the same patch.
Because the proof source materially changed, the focused target was rebuilt:

```text
Build completed successfully (3366 jobs).
```

The passing run took approximately 11 seconds, with 5.7 seconds on the repaired
execution module and 2.5 seconds on the public specification.  Axiom reports
for `func0_exact`, `dot2CheckedBits_exact`, and
`dot2CheckedBits_wat_real_error` contain exactly `propext`,
`Classical.choice`, and `Quot.sound`; the transient failed build's `sorryAx`
reports are gone.  Only existing deprecation and linter warnings remain.

## 2026-09-04: Local-only operating contract after workspace loss

An earlier scratch checkout disappeared during workspace maintenance outside
the repository workflow.  That event deleted files and is not an authorized
part of this project.  The recovered `talosfp-euler` checkout and every file in
it are treated as user-owned persistent project state.  The active checkout is
not disposable even if an enclosing service labels its filesystem as scratch.
No workspace maintenance, cleanup, reclamation, pruning, file
deletion, `git clean`, destructive reset, checkout-overwrite, stash, or other
worktree-rewriting shortcut may be used.  Existing and unrelated changes must
be inspected and preserved.  If a conflict cannot be worked around safely,
work stops for user direction rather than discarding anything.

There is no `dev` host in this workflow.  It must not be invoked, probed, or
silently substituted.  Every Lean, Lake, compiler, WAT, WASM, Node, Wasmtime,
and artifact command runs directly on the local machine.  Lean commands use
one serialized process, `LEAN_NUM_THREADS=1`, an explicit timeout,
`LEANRUN_LOCAL=1`, the pinned local Lean 4.34.0-rc2 sysroot, and the corrected
PID-namespace preload shim.  The repository runner retains its machine lock,
`nice`, and `ionice` controls.  GitHub is used only to publish and recover
committed repository state; it is not a build executor.

A no-diagnostic timeout is censored timing evidence, not a proof error and not
a pass.  The identical target is not rerun against unchanged dependency state.
The next action must divide it at a smaller module or theorem boundary; the
parent can be retried only after that boundary has passed and materially
warmed the local cache.  Only one Lean process may run at a time, including
through subagents.  All command outcomes, elapsed slow boundaries, warnings,
axiom audits, and failed attempts are recorded here.

The branch is inspected before every edit.  Each coherent change is committed
and pushed promptly because the checkout can disappear again.  Publication is
complete only after the remote ref is fetched and local and remote commit trees
are identical.  Publishing must not reset, clean, stash, or rewrite the
worktree.  These rules apply to the remaining aggregate-cache recovery and to
all Euler implementation phases.

## 2026-09-04: Focused aggregate-cache ledger through TradeAllocAppend

The F64Dot2 repair checkpoint was published as
`36547bf44409e92d750c85a12d330ae724601760`; local and remote tree
`6e8509b61efd85e50d0295caca550152138a912b` matched and the worktree was
clean.  Aggregate recovery then continued locally and serially through focused
public specification targets.  No source changed during the successful cache
warming runs.

- `Project.F64DotCheckedBits.Spec` passed all 3,372 jobs.  Its execution module
  took approximately 13 seconds and its public specification approximately 2
  seconds.  The advertised theorem audit again contained only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `Project.LebU32.Spec` passed all 3,366 jobs.  The largest freshly built
  boundaries were `Iter` at approximately 60 seconds and `NegIter` at 28
  seconds.
- `Project.ClobQuote.Spec` passed all 3,348 jobs.  `Step` took approximately 36
  seconds and the root specification 13 seconds.
- `Project.ClobCancel.Spec` passed all 3,351 jobs; its root specification took
  approximately 63 seconds.
- `Project.ClobFindBest.Spec` passed all 3,349 jobs.  The material cold costs
  were `Helpers` at approximately 191 seconds and `Loop` at 468 seconds.

The first focused `Project.ClobPostOnly.Spec` run reached 3,364 of 3,366 jobs
and then exhausted its explicit 15-minute limit after
`Project.ClobPostOnly.AppendOrderFinish`.  It emitted no theorem diagnostic, so
it is a timeout rather than a failure.  Inspection of the generated `.olean`
frontier identified `Append` and the root `Spec` as the remaining boundaries.
`Project.ClobPostOnly.Append` was therefore built separately and passed all
3,363 jobs, with its target taking approximately 29 seconds.  The now
materially warmed `Project.ClobPostOnly.Spec` retry passed all 3,366 jobs; its
root took approximately 3.2 seconds.  The unchanged cold target was never
repeated.

The first focused `Project.ClobMatchFuel.Spec` run likewise reached its
15-minute limit without a theorem diagnostic, after warming through
`BookAllocSearch`.  Its cold dependency path included the already observed
`FindBest` and `Helpers` costs, approximately 471 and 198 seconds, plus an
`EarlyExit` boundary of approximately 51 seconds.  Rather than repeating the
root, its missing chains were split further:

- `Project.ClobMatchFuel.BookAlloc` passed all 3,357 jobs.  `BookAllocFit` took
  approximately 221 seconds, `BookAllocBump` 93 seconds, and the final prepare
  and root boundaries about 6 seconds each.
- `Project.ClobMatchFuel.BookReplaceFinish` passed all 3,361 jobs.  The store,
  erase-prefix, and copy boundaries took approximately 4.8, 7.4, and 9.0
  seconds; the finish boundary took approximately 40 seconds.
- `Project.ClobMatchFuel.PartialBookPrepare` passed all 3,370 jobs.
  `PartialBookAllocFit` took approximately 219 seconds,
  `PartialBookAllocBump` 91 seconds, `Update` 30 seconds, and the final prepare
  boundary 11 seconds.
- `Project.ClobMatchFuel.TradeAllocAppend` passed all 3,372 jobs.
  `TradeAllocSearch`, `TradeAllocPrepare`, and `TradeAlloc` each took about 6
  seconds; `TradeAllocFit` took 215 seconds; `TradeAllocBump` 92 seconds;
  `TradeAppendCopy` 8.3 seconds; `TradeAppendStore` 3.6 seconds;
  `TradeAllocCopy` 10 seconds; `TradeAppendFinish` 33 seconds; and the root
  `TradeAllocAppend` boundary 27 seconds.

All commands in this ledger used the local-only runner envelope above.  No
remote executor, concurrent Lean process, maintenance action, deletion, reset,
or worktree rewrite was used.  The next proof action must continue splitting
the still-cold higher-level MatchFuel chains before any retry of its unchanged
root specification.

## 2026-09-04: MatchFuel behavioral specification fully warmed and passed

The operating-contract checkpoint was published as
`3abe93b48b33be460caf31929b9d0c284fecded9`, with identical local and remote
tree `7b56fb79f5730405b3554406c399c88f1fb9eecc` and a clean worktree.  The
remaining `Project.ClobMatchFuel.Spec` import closure was then built as a
sequence of focused local targets.  A read-only import and `.olean` frontier
audit confirmed that the separate `Artifact*` modules are not behavioral
`Spec` dependencies, so no exact-artifact work was charged to this recovery.

The partial-fill composition closed first:

- `PartialTradePrepare` passed 3,381 jobs in approximately 10 seconds on its
  target; `PartialFinish` then passed 3,382 jobs in 3.4 seconds.
- A focused `MemoryFrame` build passed `ReleaseFrame` in 3.8 seconds and
  `MemoryFrame` in 3.0 seconds, completing 3,358 jobs.
- `PartialTradeUpdate` passed 3,385 jobs in approximately 31 seconds.
- `BranchPost` passed 3,344 jobs in 3.3 seconds and `PartialBookControl` passed
  3,373 jobs in 5.2 seconds.
- With those exact prerequisites current, `PartialBranch` passed all 3,389
  jobs in approximately 31 seconds.

The full-fill path was divided at its independent leaves before joining them:

- `BookEraseSuffix` passed 3,357 jobs in approximately 12 seconds.
  `BookAllocErase` then took 14 seconds and `FullBookUpdate` 23 seconds in a
  successful 3,362-job build.
- `FullTradePrepare` passed 3,373 jobs in 10 seconds.  The independent
  `ReleaseOld` target passed 3,358 jobs in 8.5 seconds, after which
  `FullTradeFinish` passed 3,376 jobs in 5.4 seconds.
- The focused `FullStep` build passed all 3,389 jobs.  Its remaining material
  boundaries were `FullTransition` at 77 seconds, `FullTradeUpdate` at 54
  seconds, `FullBranch` at 62 seconds, `FullReleaseTransition` at 4.1 seconds,
  and `FullStep` itself at 58 seconds.

The recursive loop closure was then warmed from the leaves upward:

- `Budget` passed 3,350 jobs in 3.7 seconds; `LoopControl` passed 3,386 jobs in
  9.4 seconds; `Iteration` passed 3,407 jobs in 32 seconds;
  `Initialization` passed 3,408 jobs in 4.8 seconds; and `LoopInvariant` passed
  3,410 jobs in 5.5 seconds.
- A focused `Loop` build passed all 3,417 jobs.  The newly built boundaries
  were `LoopBounds` at 5.9 seconds, `LoopProgress` at 3.6,
  `LoopCompletion` at 5.7, `LoopAdvance` at 6.2, `LoopBranches` at 6.2,
  `LoopIteration` at 3.0, and `Loop` at 3.8 seconds.
- `Correct` then passed all 3,421 jobs, building `LoopInitial` in 6.1 seconds,
  `LoopResult` in 4.1, `Entry` in 3.2, and `Correct` in 6.2 seconds.
- The independent source-model `Properties` leaf passed 3,347 jobs in 3.9
  seconds.

At that point every behavioral import was current, materially changing the
dependency state since the earlier timeout.  The permitted retry completed:

```text
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build \
  Project.ClobMatchFuel.Spec
Build completed successfully (3424 jobs).
```

The final root took approximately 3.1 seconds.  Every run used the pinned
local-only envelope with one Lean process.  Output contained existing
deprecation warnings but no theorem diagnostic, new warning class, remote
execution, cleanup, deletion, reset, or worktree rewrite.  The cold root was
not repeated until its entire import closure had been divided and passed.
The remaining aggregate recovery frontier is `ClobLimit`, `ClobMarket`, and
`ClobDepth`, followed by one materially warmed aggregate retry.

## 2026-09-04: ClobLimit behavioral specification fully warmed and passed

The MatchFuel recovery and operating-contract notes were published as
`60ca3730505d22e3135986bf073cd65b76f5ddba`; the local and
`origin/talosfp-euler` refs and tree
`754062c326bc468e5a4889dcfc8f83057b2f3d66` were identical before this work
started.  The worktree was clean.  A read-only import audit established the
behavioral `Project.ClobLimit.Spec` closure and confirmed that the separate
`Artifact*` modules are not dependencies of that specification.

Every build below ran directly on the local machine, one Lean process at a
time, with `LEANRUN_LOCAL=1`, `LEAN_NUM_THREADS=1`, the pinned Lean
4.34.0-rc2 sysroot, the PID-namespace preload shim, local wasm-tools 1.251.0,
and an explicit 15-minute runner timeout.  No `dev` host was invoked or
probed.  No maintenance, cleanup, reclamation, pruning, deletion, reset,
checkout-overwrite, stash, or other worktree rewrite occurred.

The model, validity, search, and internal transition leaves were warmed first:

- `Project.ClobLimit.ValidOrder` passed 3,353 jobs.  `Model` took about 3.5
  seconds and `ValidOrder` 9.6 seconds.
- `Project.ClobLimit.Invalid` passed 3,356 jobs.  `Allocation` took about 3.4
  seconds and the target 38 seconds.
- `Project.ClobLimit.FindBestWrapper` passed 3,358 jobs.  Its freshly built
  boundaries included `FunctionRegion.NoTail` at 15 seconds, `Step` at 1.5,
  `Exec` at 0.732, `SearchRegion` at 9.8, `FindBest` at 3.0, and the wrapper
  at 3.4 seconds.
- `InternalEarlyExit` passed 3,359 jobs in 21 seconds and
  `InternalIteration` passed 3,359 jobs in 29 seconds.
- `InternalBookBump`, `InternalFullBookBump`, and `InternalTradeBump` each
  passed 3,347 jobs and each took approximately 93 seconds.

The partial-fill path was then divided at its allocation and update joins:

- `InternalPartialBookPrepare` passed 3,346 jobs in 12 seconds and
  `InternalPartialBookControl` passed 3,348 jobs in 5.1 seconds.
- `InternalPartialBookAlloc` passed 3,349 jobs, building `AllocPrepare` in
  6.1 seconds and `Alloc` in 5.9 seconds.
- `InternalPartialBookUpdate` passed 3,366 jobs.  `Copy` took 9.1 seconds,
  `Finish` 42 seconds, and `Update` 21 seconds.
- `InternalPartialTradePrepare` passed 3,367 jobs in 10 seconds.
  `InternalPartialTradeAlloc` passed 3,370 jobs, building `AllocPrepare` in
  6.6 seconds and `Alloc` in 5.8 seconds.
- `InternalPartialTradeUpdate` passed 3,378 jobs.  `Copy` took 8.6 seconds,
  `Finish` 34 seconds, and `Update` 20 seconds.
- `InternalPartialBranch` passed 3,384 jobs.  Its final boundaries were
  `PartialFinish` at 3.4 seconds, `PartialTradeBranch` at 17 seconds, and the
  target at 196 seconds.

The full-fill path and loop closure passed from their leaves upward:

- `InternalFullBookPrepare` passed 3,347 jobs in 7.0 seconds.
  `InternalFullBookUpdate` passed 3,363 jobs, with `AllocPrepare` at 6.0
  seconds, `Alloc` at 5.2, `Prefix` at 7.5, `Suffix` at 10, and `Update` at
  11 seconds.
- `InternalFullTradeFinish` passed 3,365 jobs, building its prepare boundary
  in 10 seconds and finish boundary in 4.0 seconds.
  `InternalFullTradeUpdate` passed 3,398 jobs in 18 seconds;
  `InternalFullBookTrade` passed 3,401 jobs in 15 seconds;
  `InternalFullTransition` passed 3,399 jobs in 3.0 seconds; and
  `InternalFullBranch` passed 3,403 jobs in 11 seconds.
- `InternalLoopControl` passed 3,409 jobs in 9.5 seconds and
  `InternalLoopInvariant` passed 3,411 jobs in 4.5 seconds.
- `InternalLoop` passed all 3,418 jobs.  Its newly built boundaries were
  `Bounds` at 5.6 seconds, `Progress` at 3.2, `Completion` at 4.4,
  `Advance` at 4.0, `Branches` at 4.3, `LoopIteration` at 3.1, and the loop
  at 3.5 seconds.
- `InternalCorrect` passed all 3,424 jobs.  `LoopInitial` took 4.4 seconds,
  `LoopResult` 3.5, `Initialization` 3.2, `InternalEntry` 3.4, and the target
  4.0 seconds.

The public run-match wrapper passed next:

- `RunMatchEmptyAlloc` passed 3,358 jobs in 60 seconds.  It replayed only the
  existing deprecation warnings and the existing unused-simp-argument lints
  at `RunMatchEmptyAlloc.lean:536`.
- `RunMatchEntry` passed 3,359 jobs in 3.6 seconds.
- `RunMatchAllocations` passed 3,361 jobs, with `Prepare` at 5.8 seconds and
  the target at 7.5 seconds.
- `RunMatchCorrect` passed 3,434 jobs, building `Call` in 6.6 seconds,
  `Result` in 3.2, and the target in 5.0 seconds.

The exported limit-order path began with `LimitEntry` at 3,435 jobs and 4.0
seconds.  `LimitRunMatchResult` passed 3,441 jobs, building `ValidEntry` in
3.7 seconds, `RunMatchCall` in 3.3, and its target in 4.1 seconds.
`LimitFilled` then passed 3,443 jobs in 9.6 seconds.

The residual-order path was deliberately divided around its two cold memory
boundaries:

- `LimitResidualStatus` passed 3,443 jobs in 3.7 seconds and
  `LimitResidualPrepare` passed 3,444 jobs in 6.3 seconds.
- The focused `LimitResidualBump` build first built
  `LimitResidualAllocPrepare` in 4.8 seconds, then passed all 3,446 jobs with
  92 seconds on the bump target.
- `LimitResidualAlloc` passed 3,447 jobs in 5.9 seconds;
  `LimitResidualAllocFacts` passed 3,448 jobs in 4.1 seconds; and
  `LimitResidualCopyInvariant` passed 3,449 jobs in 3.8 seconds.
- `LimitResidualAllocCopy` passed all 3,452 jobs.  The newly built
  `LimitResidualBounds`, `LimitResidualCopy`, and root boundaries took 3.7,
  4.9, and 3.0 seconds respectively.
- The focused `LimitResidualFinish` build passed all 3,456 jobs, building
  `LimitResidualFinishFacts` in 5.2 seconds and the target in 39 seconds.
- `LimitResidualBook`, `LimitResidualResult`, and `LimitResidualBranch` each
  passed in 3.4 seconds, at 3,457, 3,458, and 3,459 jobs respectively.
- The independent `LimitResult` target passed 3,457 jobs in 3.6 seconds.
  `LimitResidualExport` passed 3,459 jobs in 3.9 seconds and
  `LimitResidual` passed 3,462 jobs in 5.1 seconds.

With the complete behavioral closure current, `LimitCorrect` passed all 3,465
jobs in 5.2 seconds and the public root completed:

```text
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build \
  Project.ClobLimit.Spec
Build completed successfully (3466 jobs).
```

`Project.ClobLimit.Spec` itself took approximately 3.3 seconds.  Every target
completed without a theorem diagnostic or source repair; output was limited to
the repository's existing deprecation and linter warnings.  The remaining
aggregate recovery frontier is now `ClobMarket` and `ClobDepth`, followed by
one materially warmed aggregate retry.

## 2026-09-04: ClobMarket behavioral specification fully warmed and passed

The ClobLimit recovery ledger was published as
`5249e0cd72a4a0d58f65cadf879c6271b6bfcd94`.  The local and remote refs and
tree `a21c323e91e7032242c2ad78f44f5013ae70cbf0` matched, and the worktree was
clean before ClobMarket recovery began.  The read-only import audit had found
a 135-module behavioral closure with no `Artifact*` dependency.

The shared execution spine passed first:

- `Project.ClobMarket.Model` passed 3,350 jobs in 3.3 seconds.
- `MatchRegion` and `ExportRegion` each passed 3,347 jobs, taking 20 and 4.5
  seconds respectively.
- `RunMatch` passed 3,437 jobs in 4.3 seconds, using the already current
  `Project.ClobLimit.RunMatchCorrect` chain.
- `Helpers` passed 3,361 jobs in 3.4 seconds and `Entry` passed 3,444 jobs in
  3.7 seconds.

The valid-order branch passed as a sequence of focused targets:

- `ValidEntry` passed 3,445 jobs in 3.9 seconds.
- An attempted `Project.ClobMarket.ValidPrice` target was rejected immediately
  by Lake at 2 of 2 jobs because no such source file exists.  This was a target
  naming error, not a theorem diagnostic; it changed no source or proof state.
  A directory listing confirmed that the actual module is
  `Project.ClobMarket.Price`.
- `Price` passed 3,447 jobs in 4.7 seconds; `Call` passed 3,448 jobs in 3.7
  seconds; `ValidResult` passed 3,449 jobs in 4.1 seconds; and `Valid` passed
  3,450 jobs in 4.4 seconds.

The invalid-order branch was then warmed from its leaves upward:

- `InvalidEntry`, `InvalidPrepare`, and `InvalidSearch` passed 3,445, 3,446,
  and 3,447 jobs in 3.9, 5.4, and 4.1 seconds respectively.
- The focused `InvalidBump` memory proof passed all 3,448 jobs in 90 seconds.
- `InvalidFinish` passed 3,449 jobs in 3.9 seconds; `InvalidPost` passed 3,450
  jobs in 3.7 seconds; `InvalidProgram` passed 3,451 jobs in 4.6 seconds;
  `InvalidResult` passed 3,452 jobs in 3.6 seconds; and `Invalid` passed 3,453
  jobs in 5.3 seconds.

With both branches current, `Project.ClobMarket.Correct` passed all 3,460 jobs
in 4.9 seconds.  The public root then completed:

```text
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build \
  Project.ClobMarket.Spec
Build completed successfully (3461 jobs).
```

The `Spec` target took approximately 3.3 seconds.  All successful builds used
the serialized pinned local-only envelope.  No `dev` host, cleanup, deletion,
reset, stash, maintenance, or worktree rewrite was used.  Apart from the
explicit nonexistent-target invocation above, output contained only existing
deprecation warnings and no theorem diagnostic.  `ClobDepth` is now the sole
remaining focused case before one materially warmed aggregate retry.

## 2026-09-04: ClobDepth missing-level branch passed

The ClobMarket recovery ledger was published as
`7377cdfc7ed6fa533ff709f7ecec915c5040624d`; the local and remote refs and
tree `49e4ee0a7bed5746df408e8d6a46387bc99f4455` matched, and the worktree was
clean before the serialized ClobDepth builds began.  This checkpoint was made
without any source or proof edit: it records the exact local build evidence
accumulated in the existing Lake cache.

The shared depth model and scan spine passed first:

- `Project.ClobDepth.Model` passed 3,345 jobs in 3.3 seconds.
- `Properties`, `Representation`, and `LevelCopyInvariant` passed 3,346,
  3,346, and 3,347 jobs in 4.0, 4.3, and 3.5 seconds respectively.
- `Entry` passed 3,342 jobs in 5.4 seconds and `Scan` passed 3,350 jobs in
  7.0 seconds.

The missing-level branch was then warmed strictly from its leaves upward:

- `MissingFields`, `MissingPrepare`, and `MissingSearch` passed 3,351, 3,352,
  and 3,353 jobs in 3.8, 3.9, and 3.8 seconds respectively.
- The focused `MissingBump` memory proof passed all 3,355 jobs in 91 seconds.
- `MissingFinish` passed 3,356 jobs in 4.9 seconds;
  `MissingCopyInvariant` passed 3,358 jobs in 3.7 seconds; and `MissingCopy`
  passed 3,359 jobs in 6.2 seconds.
- `MissingStoreFacts` passed 3,360 jobs in 6.4 seconds and `MissingStore`
  passed 3,361 jobs in 15 seconds.
- `MissingBranchFacts` passed 3,362 jobs in 3.7 seconds and `MissingBranch`
  passed 3,363 jobs in 7.4 seconds.

Every command used the documented pinned local-only Lean envelope, with one
Lean process at a time.  Output contained only the repository's existing
deprecation warnings and no theorem diagnostic.  No `dev` host, cleanup,
deletion, reset, stash, maintenance, or worktree rewrite was used.  The next
frontier is the found-level branch, followed by `Func3`, the `Func6` loop,
`Func7`, and the public ClobDepth root.

## 2026-09-04: ClobDepth behavioral specification fully warmed and passed

The missing-level checkpoint was published as
`7c59cac4aace13299a84fa9dd4bea7754197f296`; local and remote refs and tree
`bf7eb44a3a758bce817a78ff7c52ac59a0f63d57` matched before the found-level
branch began.

The found-level memory path passed leaf by leaf:

- `FoundFinish` passed 3,357 jobs in 4.8 seconds;
  `FoundCopyInvariant` passed 3,360 jobs in 3.7 seconds; and `FoundCopy`
  passed 3,361 jobs in 5.8 seconds.
- `FoundStoreFacts` passed 3,364 jobs in 6.0 seconds and `FoundStore` passed
  3,365 jobs in 14 seconds.
- `FoundBranchFacts` passed 3,366 jobs in 3.6 seconds.
- `FoundPrepare` passed its 3,365-job closure.  Its exact target timing scrolled
  beyond the deliberately short captured output tail; this is recorded rather
  than reconstructed.  `FoundAllocPrepare` then passed 3,366 jobs in 3.9
  seconds and `FoundBranch` passed 3,373 jobs in 9.2 seconds.

The exported function spine then closed:

- `Func3` passed 3,374 jobs in 6.9 seconds.
- The first `Func6Alloc` invocation crossed the command runner's 30-second
  output yield, so no other Lean process was started.  A read-only process
  check showed that exact local target still running; it completed at roughly
  40 seconds wall time.  An immediate serialized replay confirmed its
  3,375-job closure.  This runner-output bookkeeping event did not alter the
  worktree or proof state.
- `Func6Fold` passed its 3,376-job closure.  As with `FoundPrepare`, the exact
  target timing was outside the retained short output tail and is not guessed.
- `Func6Loop` passed 3,377 jobs in 21 seconds; `Func6` passed 3,378 jobs in
  6.9 seconds; and `Func7` passed 3,379 jobs in 5.8 seconds.

The public root then completed:

```text
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build \
  Project.ClobDepth.Spec
Build completed successfully (3380 jobs).
```

`Project.ClobDepth.Spec` itself took 3.1 seconds.  Every successful target used
the documented pinned local-only envelope with one Lean process at a time.
Output contained only existing deprecation/linter warnings and no theorem
diagnostic; no source repair was required.  No `dev` host, cleanup, deletion,
reset, stash, maintenance, or worktree rewrite was used.  All focused cases
that were selected to recover the behavioral aggregate are now current.  The
next and only aggregate action is one materially warmed `Project` retry.

## 2026-09-04: warmed Talos aggregate passed

The completed ClobDepth recovery ledger was published as
`89d7cdd3a84923cb5461fc8bb7ae270c710f1ad1`; local and remote refs and tree
`860a80140b6b392943d6773502131ba055b50af5` matched, with a clean tracked
worktree, before the aggregate attempt.

The one planned materially warmed aggregate command was then run under the
same pinned, serialized, local-only envelope:

```text
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project
Build completed successfully (3719 jobs).
```

The `Project` aggregate target itself took 3.4 seconds and the complete command
took approximately 6.1 seconds wall time.  It replayed the warmed dependency
closure and emitted only the repository's existing deprecation/linter
warnings.  There was no theorem diagnostic, timeout, or source repair.  This
resolves the earlier cold aggregate timeout at 3,442 of 3,719 jobs: it was a
resource/cache-warming problem, not evidence of a failing theorem.

No second aggregate retry was made.  No `dev` host, cleanup, deletion, reset,
stash, maintenance, or worktree rewrite was used.  The existing TalosFP proof
baseline is now demonstrated green immediately before Euler implementation.

## 2026-09-04: guarded Euler Rusanov source checkpoint

The green inherited aggregate ledger was published as
`8734a86d13eb833229e8f10a6bc37aa1ab958d40`; local and remote refs and tree
`389fda745b60d74246b96cc1f3acf642538ad07b` matched, with a clean tracked
worktree, before the first Euler source edit.

The new `LeanExe.Examples.EulerRusanov.rusanovFluxCheckedBits` entry takes six
raw binary64 words and returns `{status, mass, momentum, energy}` as four
`UInt64` words.  The integer-only guard enforces `1/8 <= rho <= 1`,
`1/16 <= p <= rho`, and sign-cleared `|u| <= 1/2` independently on both
primitive states.  Rejection returns status one and three positive-zero words.

The accepted operation graph computes the exact-real `gamma = 7/5`, fixed
`alpha = 7/4` Rusanov formula in a dyadic order selected for proof headroom:
`5/2 * p` is `(p + p) + p/2`, `7/2 * p` adds another `p`, and `alpha/2`
times a jump is the sum of separately rounded `jump/2`, `jump/4`, and
`jump/8`.  On the guarded domain this keeps exact products below two and exact
sums below four, the ranges already supported by the pinned IEEE64 rounders.

The first direct `lean-wasm compile` probe omitted the required pinned local
sysroot environment and exited immediately with compiler status 3 and
`failed to locate application`; it created no accepted result and was not a
source failure.  Re-running with the documented local sysroot and compatibility
preload produced the WASM, WAT, and IR normally.

Focused local verification then passed:

- `lake --no-ansi build LeanExe.Examples.EulerRusanov` passed three jobs, with
  402 milliseconds on the new module.
- `lake --no-ansi build LeanExe` passed all 51 jobs, including the new root
  import, in approximately 17.1 seconds wall time.
- `node test/euler_rusanov.js` completed in approximately 0.7 seconds.  The
  Wasmtime C host matched fixed words for equal left/right states, canonical
  and reversed Sod interfaces, a midpoint state, and both extreme guarded
  interfaces.  Signed zero was accepted.  Adjacent-bit violations of the rho,
  pressure, pressure-versus-rho, and velocity bounds on both sides, plus
  representative NaNs, all returned `[1, 0, 0, 0]`.
- The extracted IR contains exactly 22 `f64MulBits`, 27 `f64AddBits`, and
  three `bitXor` operations, with zero surviving `LeanExe.Float64` intrinsic
  calls.  The exported WAT body contains exactly 22 `f64.mul`, 27 `f64.add`,
  three `i64.xor`, 98 `f64.reinterpret_i64`, and 49
  `i64.reinterpret_f64` instructions.
- `node test/no_js_wasm_execution.js` passed, confirming that the new
  regression uses the pinned Wasmtime host rather than JavaScript's WASM API.

All commands ran locally; no `dev` host, maintenance, cleanup, deletion,
reset, stash, or worktree rewrite was used.  Generated `.lake/build` products
remain ignored.  The next checkpoint registers this source as an initially
incomplete Talos case and generates its proof-visible program.

## 2026-09-04: Euler Talos program registered and pinned

The guarded source checkpoint was published as
`99fcfa1f51d5b2346c8cac11fc74ed6a2aea11dc`; local and remote refs and tree
`de4b75aee7b0cfc96af67bc8a8a3284fcd4e486f` matched, with a clean tracked
worktree, before registration.

`proofs/talos/cases.json` now registers `euler_rusanov` with source module
`LeanExe.Examples.EulerRusanov`, the fully qualified scalar entry, Lean proof
module `EulerRusanov`, and the intended exact-execution and WAT-error theorem
names.  It is explicitly `complete: false`; consequently `Project.lean` does
not import the new Spec and no completed-proof claim is made.

The pinned local command

```text
node tools/talos-artifact.js prepare euler_rusanov
```

built the verifier and compiler inputs, compiled the source, translated it,
and emitted `Project/EulerRusanov/Program.lean`.  The generated source is 996
lines and 17,720 bytes.  Its input WASM is 1,808 bytes with SHA-256
`145230bc0f956df81283fb37227c303de2c92e68842d38b985325dca467f6546`.
The ignored generated WASM is not yet the frozen exact-artifact package; that
separate identity boundary follows the behavioral theorem.

Inspection of the generated program established the actual indices rather
than assuming them: the six-argument, four-result Euler entry is `func0`, and
`func1`, `func2`, `func3`, and `func4` are respectively alloc, reset, retain,
and release.  `Project.Runtime.Checks` now imports the Euler Program and pins
all four helpers to the shared runtime definitions.  The focused builds passed:

- `Project.Runtime.Checks` passed 3,367 jobs, building the new Program in 3.0
  seconds and the runtime-check root in 3.3 seconds.
- The deliberately minimal `Project.EulerRusanov.Spec` root passed 3,342 jobs
  in 3.1 seconds.
- `node tools/talos-proof.js check euler_rusanov` regenerated and matched the
  tracked Program, rebuilt the same 3,342-job target, and reported
  `Talos incomplete case target built: euler_rusanov`.
- A direct registry/import-set check confirmed that `Project.Runtime.Checks`
  imports every registered Program while `Project.lean` imports exactly the
  24 completed Specs and excludes the incomplete Euler root.

Output was limited to existing deprecation warnings.  No `dev` host,
maintenance, cleanup of the active checkout, deletion of user files, reset,
stash, or worktree rewrite was used.  The next proof boundary is the pure
IEEE64 Euler model and the raw-bit guard/domain bridge.

## 2026-09-04: pure Euler IEEE64 and real model passed

The Talos registration checkpoint was published as
`6775846ab94da6c1327b15f5e717be515abd6e21`; local and remote refs and tree
`679bccb4b57ca820596f0d2f19621c790afbe57d` matched before the model edit.

`Project.EulerRusanov.Model` now defines, without importing the generated
Program or evaluating native Lean `Float`:

- the exact raw constants and ten-condition integer guard;
- the ordered per-side Talos `Wasm.IEEE64` intermediates;
- sign-toggle subtraction, rounded mean, dyadic `7/8` dissipation, and the
  three accepted result words;
- the total checked result, source-order words, and reversed Talos value stack;
  and
- independent real primitive, conservative, physical Euler flux, and fixed
  `alpha = 7/4` Rusanov definitions over decoded input values.

The guard was kept in the source's exact left-associated condition order so
later execution proofs can relate each short-circuit path without treating
Boolean associativity as generated-code evidence.  The focused local build

```text
tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build \
  Project.EulerRusanov.Model
```

passed all 3,058 jobs, with 3.2 seconds on the new target and approximately
5.6 seconds wall time.  Output contained only existing dependency warnings and
the standard accepted CodeLib axiom reports.  No `sorry`, `admit`, or new axiom
declaration is present.  No `dev` host, active-checkout cleanup, deletion,
reset, stash, maintenance, or worktree rewrite was used.

## 2026-09-04: Canonical operational notes checkpoint

This section consolidates the user's standing directions.  If an older entry
calls the checkout or workspace disposable, this section supersedes that
wording.  The rules are part of the project record rather than transient chat
context.

1. The active `talosfp-euler` checkout is persistent, user-owned project state.
   That includes `.git`, tracked sources, untracked drafts, generated files,
   ignored artifacts, dependency trees, and build products.  No agent,
   subagent, workspace service, or helper is authorized to perform maintenance,
   cleanup, reclamation, pruning, deletion, `git clean`, destructive reset,
   checkout-overwrite, stash, or any other worktree rewrite.  Reproducibility
   does not make a local file eligible for deletion.  Deleting any exact target
   requires fresh, explicit user authorization.
2. Inspect `git status` before mutations and preserve all pre-existing,
   unrelated, and in-progress work.  If a safe edit cannot avoid a conflict,
   stop for user direction; never resolve it by discarding files.  The current
   untracked `Bounds.lean` and `ScaledRoundoff.lean` files are delegated proof
   drafts and must remain intact until reviewed and checked.
3. There is no `dev` host.  Do not invoke it, probe for it, mention it as an
   available executor, or substitute any other remote compute service.  Lean,
   Lake, `lean-wasm`, Node, Wasmtime, artifact generation, and proof checking
   all run locally.  GitHub is only the branch-publication and recovery remote.
4. The user explicitly authorized direct local Lean execution.  Lean-family
   commands remain serialized globally: exactly one Lean/Lake/compiler process
   at a time, including work delegated to subagents.  Use the pinned Lean
   4.34.0-rc2 sysroot, `LEAN_NUM_THREADS=1`, an explicit timeout, and the local
   PID-namespace compatibility preload.  The current preferred repository
   envelope is `LEANRUN_LOCAL=1 tools/leanrun`, which retains the machine lock,
   `nice`, and `ionice`; direct invocation of the pinned local binary is also
   authorized when a focused diagnostic requires it.  Never claim unavailable
   systemd cgroup limits were applied.
5. A timeout without a Lean diagnostic is neither a theorem failure nor a
   pass.  Record it as censored timing evidence.  Do not repeat the identical
   target against unchanged proof and dependency state; first check a smaller
   boundary or make a material, reviewed change.  Preserve failed drafts and
   diagnostics.
6. Keep `journal.md` as the detailed chronological ledger.  Record material
   decisions, exact command shapes and environment workarounds, elapsed times,
   job counts, warnings, failures, successful checks, axiom audits, artifact
   identities, commit identities, remote publication checks, and the next open
   boundary.  Keep `devnotes.md` as the concise durable checkpoint record.
   Both files are committed and pushed whenever changed.
7. Commit coherent checkpoints frequently and push them promptly.  A publish
   is complete only after a non-forced fast-forward update of
   `origin/talosfp-euler`, a fetch of that ref, and equality of the complete
   local and remote Git trees.  The authenticated GitHub Git-data API is used
   because the checkout lacks ordinary HTTPS credentials.  Ref alignment may
   update only Git references after tree equality is established; it must not
   reset, clean, overwrite, or otherwise rewrite the worktree.
8. Native Lean evaluation and Wasmtime tests are regression evidence, not
   formal proof evidence.  Public claims require the pure Talos IEEE model,
   generated-WAT execution theorem, quantitative numerical theorem, accepted
   axiom audit, and eventually the frozen exact-byte artifact boundary stated
   in this plan.  No `sorry`, `admit`, or new axiom may be hidden in a checked
   milestone.
9. The experimental self-hosted emitter, release receipts, and unrelated hash
   or manifest bookkeeping are outside this branch's validation path.  Do not
   invoke them as gates.  Exact program bytes remain theorem inputs whenever
   exact-artifact behavior is claimed.

This is a documentation-only checkpoint.  The two newly delivered proof
drafts are deliberately excluded from this commit until each has been reviewed
and passed through the single local Lean slot.

`git diff --check` passed, and `node tools/check-docs.js` checked all 90
maintained Markdown files.  The intended commit contains only `plan.md`,
`plans/euler-rusanov.md`, `journal.md`, and `devnotes.md`; no Lean build is
required for this notes-only change.  The next action after remote publication
and tree verification is a read-only review followed by serialized focused
builds of the preserved proof drafts.

## 2026-09-04: Euler guard, signal, and scaled-roundoff foundations passed

The canonical operating-notes checkpoint was published as
`154d32095104449fcd150a0ebfcbe236fa567151`.  The non-forced remote update was
fetched, and both local and `origin/talosfp-euler` resolved to complete tree
`524d6faf4abb948276f69b98638a7734c6d2a7c0`.  Ref reconciliation changed only
the local Git reference after tree equality was established.  The two
untracked proof drafts remained intact.

Two delegated agents had created only
`Project/EulerRusanov/Bounds.lean` and
`Project/EulerRusanov/ScaledRoundoff.lean`; neither agent ran Lean or edited
another file.  Two separate agents then performed read-only reviews.  They
found the statements mathematically sound and identified casts, large powers,
and sign-bit normalization as the likely elaboration boundaries.  All actual
Lean checks below ran through the one serialized local slot.

The first `Project.EulerRusanov.Bounds` build reached the new target and failed
in 3.8 seconds with explicit diagnostics, not a timeout.  Lean exposed five
local proof-shape problems: the ten-condition executable guard had not been
regrouped into the two three-part state guards; the positive sign proof left a
literal `2^63` inequality; the equal-exponent monotonicity branch had not
rewritten the right exponent; the velocity proof needed an explicit equality
between the two definitionally identical mask guards; and the namespaced
`StateBounds.signalSpeed_le_alpha` method resolved its unqualified helper name
as a recursive call.  The transient axiom reports consequently contained
`sorryAx` and were not accepted.

The repair expanded the Boolean definitions at the guard bridge, converted the
sign goal with `decide_eq_false_iff_not`, rewrote the equal exponent, named the
velocity-guard equality, and fully qualified the real signal-speed theorem.
The materially changed target then passed:

```text
Project.EulerRusanov.Bounds
Build completed successfully (3067 jobs).
new target: 4.1 seconds
complete command: approximately 6.5 seconds
```

The checked module now proves positive-normal raw-word finiteness and value
bounds, monotonicity of real binary64 values under unsigned word order on the
guarded interval, the complete left/right `StateBounds`, and

```text
abs velocity + sqrt ((7 / 5) * pressure / density) <= 7 / 4.
```

The first `Project.EulerRusanov.ScaledRoundoff` build also failed explicitly,
in 3.6 seconds.  Its diagnostics were proof elaboration issues: a `ring` ran
after `field_simp` had already closed a goal; a generic strict-multiplication
lemma selected the wrong typeclass interface; raw XOR normalization did not
reduce the sign-mask literal; the bit-vector sign-XOR endpoint remained; an
unqualified `Finite` was ambiguous; and the final real division needed an
explicit algebraic normalization.  Those repairs reduced the next build to
two concrete constant-folding goals for `UInt64.toNat 0x8000000000000000`.
The second failed target took 3.5 seconds and again was not accepted.

The final repair proves the sign-mask word identity through
`UInt64.toNat_ofNat_of_lt` and reuses it for the most-significant-bit fact.
After that material change the focused target passed:

```text
Project.EulerRusanov.ScaledRoundoff
Build completed successfully (3059 jobs).
new target: 3.7 seconds
complete command: approximately 6.0 seconds
```

Its public layer supplies finite-result and absolute-error theorems for an
addition whose exact sum has magnitude below four and a multiplication whose
exact product has magnitude below two.  Both bounds are `2^-52`.  It also
proves that integer XOR with the binary64 sign mask preserves exponent,
fraction, magnitude, and finiteness while negating the scaled integer and real
values exactly, including the signed-zero encodings.

`Project.EulerRusanov.Spec` now imports both foundations.  Its first combined
build passed all 3,366 jobs; the final ScaledRoundoff rebuild took 3.6 seconds,
the Spec root took 3.2 seconds, and the command took approximately 9.4 seconds.
That replay exposed two non-failing `unnecessarySeqFocus` warnings in Bounds.
They were removed by replacing the broad tactic sequencing with explicit
`all_goals` blocks.  The materially changed combined target passed again with
Bounds at 3.0 seconds, the Spec root at 3.2 seconds, and approximately 9.7
seconds for the command.  The advertised Bounds and ScaledRoundoff theorems
report exactly `propext`, `Classical.choice`, and `Quot.sound`; no accepted
report contains `sorryAx`, and the final output contains only existing
dependency warnings.  No `dev` host, cleanup, deletion, reset, stash,
maintenance, concurrent Lean process, or worktree rewrite was used.

This checkpoint completes the raw guard and characteristic-speed row in the
Euler plan.  It does not claim the full componentwise Euler error theorem: the
next numerical layer must propagate these primitive bounds through all 49
rounded operations and retain strict `< 4` headroom for the largest correlated
energy-flux sum.  Exact generated-WAT execution remains independently open.
The intended commit is `Prove Euler guard and scaled roundoff foundations` and
contains the two checked proof modules, their Spec imports, the completed plan
row, and these journal/devnotes records.

## 2026-09-04: exact Euler execution and proof-to-data work in progress

Before further mutation, the local branch and fetched publication ref were
checked again.  Both `talosfp-euler` and `origin/talosfp-euler` resolved to
`b270b0e85ea201feb0f95da25da858831caa53d1`, and both complete trees resolved
to `07d0fc323b4f961daf429c2af6c86c523723c451`; the worktree was then clean.
The already published operating contract remains in force.  No workspace
maintenance, cleanup, deletion, reset, stash, checkout overwrite, remote
executor, or `dev` host was used.

A read-only audit of generated `EulerRusanov.func0` established the exact ABI
and proof shape.  The exported function is index zero, has six i64 parameters
and 42 i64 locals, returns four i64 words, and has no calls, memory accesses, or
global accesses.  Talos's top-first input stack is
`[pR, uR, rhoR, pL, uL, rhoL]`; the returned stack is
`[energy, momentum, mass, status]`, exactly `Model.resultValues`.  Ten ordered
raw-word predicates form eleven semantic paths: the first failed predicate
short-circuits through the common rejection tail, or all ten pass and 49
floating-point operations execute.  Two compiler Boolean-bookkeeping
conditionals sit between the guard ladder and final accepted/rejected selector.

A delegated draft of `Project/EulerRusanov/Execution.lean` was handed back
without being built by the delegate.  It states fuel-independent termination
for arbitrary host environment and initial store, complete store preservation,
and exact equality with the pure model on all accepted and rejected inputs.
All actual Lean invocations were then serialized through the single local slot
with `LEANRUN_LOCAL=1`, the pinned rc2 sysroot, the readlink preload,
`LEAN_NUM_THREADS=1`, the pinned `wasm-tools`, and a 15-minute wall timeout.

The first focused `Project.EulerRusanov.Execution` build reached the new target
and failed explicitly in 3.2 seconds, approximately 5.6 seconds for the full
command.  Its sole proof diagnostic was the default recursion limit during the
initial 42-local `wp_run`.  Raising this module's `maxRecDepth` to 8192 was a
material proof-state change; the transient axiom report contained `sorryAx`
and was not accepted.

The second focused build reached the new target in 18 seconds, approximately
21.1 seconds for the full command.  It exposed two concrete issues: the
accepted 49-operation tail exhausted the default simplifier step budget, and
the rejection finalizers had unfolded the model guard without retaining an
explicit false equality.  Several outer tactic frames then exhausted the
default 200,000 heartbeat allowance.  The repair constructed a local
`eulerGuard = false` fact in every first-failure branch, used that fact without
expanding the guard in the final model reduction, and supplied an explicit
larger heartbeat allowance.  This was another diagnostic failure, not a
timeout or accepted theorem.

The third focused build reached the new target in 26 seconds, approximately
29.6 seconds for the command.  Every rejection path now closed; the only
remaining diagnostic was the default step limit inside the accepted tail's
ordinary `wp_run`.  The next material change replaced only that call with the
repository's fixed WP rewrite set and a ten-million-step simplifier budget.

That monolithic accepted-path attempt then ran for 481 seconds and ended on the
explicit 8,000,000-heartbeat limit while reducing weak-head normal form.  It
produced no semantic counterexample and did not reach an accepted axiom report,
but it is deterministic capacity evidence and is not counted as a pass.  The
unchanged target will not be repeated.  The active repair is to factor the
accepted arithmetic tail at named local-frame boundaries so each portion is
separately elaborated and cached.  The complete draft and diagnostics remain
preserved in the checkout.

In parallel, a source-order numerical audit resolved the only serious range
question.  Write `delta = 2^-52`, ideal energy
`E = (5/2) p + (1/2) rho u^2`, and ideal energy flux
`G = ((7/2) p + (1/2) rho u^2) u`.  The guard gives
`0 <= E <= 21/8` and `|G| <= E`.  Independent triangle bounds for the final
energy addition are unusable because `29/16 + 147/64 = 263/64 > 4`.
Regrouping the exact result as

```text
((1/2) G_L + (7/8) E_L) + ((1/2) G_R - (7/8) E_R)
```

instead bounds its exact magnitude by `231/64`.  Including the audited mean
and dissipation errors gives `231/64 + 25 delta <= 3721/1024 < 4`, leaving
`375/1024` strict headroom for the final checked addition.  The audit derives
component budgets of 12, 15, and 26 multiples of `delta` for mass, momentum,
and energy; a uniform `32 delta` theorem is therefore conservative.  A local
continuous optimization sanity check, explicitly not formal proof evidence,
found extrema approximately `+/-3.111328125`, consistent with the analytic
headroom.  A delegated `Numerical.lean` draft is preserved unbuilt pending
handoff and serialized local checking.

The plan now also inserts an early `euler-rusanov-interface-v1` dataset after
exact-byte registration and before the finite-volume stencil.  It will invoke
the registered scalar WASM on eight frozen raw-word cases and emit a stable CSV
covering Sod interfaces, consistency, guard extremes, and rejection.  Exact
returned tuples will be Lean theorem instances.  Host looping, serialization,
plots, native/Wasmtime checks, digests as identity plumbing, and C comparisons
remain regression-only.  A same-operation-order fixed-alpha C mirror may be
required to agree bitwise; Lanyon's pinned dynamic-speed C is reported
side-by-side without an equality requirement because it computes a different
dissipation speed with division, square root, and `fmax`.

## 2026-09-04: pure Euler IEEE64 numerical contract completed

The delegated `Project/EulerRusanov/Numerical.lean` draft was inspected and
then checked only through the serialized local Lean slot.  It introduces a
small internal `Approx` record carrying finiteness, absolute approximation
error, rounded-value magnitude, and independent exact-target magnitude.  Its
addition and multiplication combinators call the proved scale-aware wrappers
from `ScaledRoundoff`; negation uses the exact sign-XOR theorem.  Per-state
certificates then follow the source operation graph exactly through conserved
state, physical flux, jumps, dyadic `7/8` dissipation, and the three final
Rusanov components.

The first focused build reached all 3,069 jobs and failed with explicit
elaboration diagnostics after approximately 10.8 seconds.  Broad algebraic
`convert` blocks had left reflexive rational inequalities, one sequencing
step made no progress, and the public mass target needed an explicit rewrite.
There was no timeout and this was not accepted proof evidence.  The repair
used named equalities, `ring_nf`, and direct public-target rewrites.

The second focused build again reached all 3,069 jobs in approximately 11.0
seconds.  It reduced every substantive goal to reflexive inequalities that
`ring_nf` normalized but did not close.  Each such endpoint was changed to an
explicit `le_rfl`; this was a material proof-script change before the next
run.  The third build reached all 3,069 jobs, spent approximately 8.1 seconds
in the target and 10.6 seconds in the complete command, and left only the
three exact literal certificates for one half, one quarter, and one eighth.

An initial literal repair unfolded the binary64 fields directly.  Its focused
build reached all 3,069 jobs but failed after 7.9 target seconds and about 10.3
command seconds because `norm_num` stopped at the three word equalities
`n = UInt64.ofNat n`.  The final repair identifies each literal as
`Wasm.IEEE64.encodeFinite false e 0` for `e = 1022, 1021, 1020`, closes the
word identity by definitional reduction, obtains finiteness from
`CodeLib.IEEE64.finite_encodeFinite`, obtains the scaled integer from
`scaledValue_encodeFinite`, and normalizes the dyadic real quotient.  This
avoids trusting native floating-point evaluation or a native decision axiom.

After that change the focused target passed:

```text
Project.EulerRusanov.Numerical
Build completed successfully (3069 jobs).
new target: 8.4 seconds
complete command: approximately 10.8 seconds
```

The public contract proves all three output words finite and bounds their
absolute errors against the independently defined exact-real fixed-speed
Rusanov flux by `10 * 2^-52`, `14 * 2^-52`, and `25 * 2^-52` for mass,
momentum, and energy.  These implementation proofs sharpen the earlier
source-order audit's conservative coefficients `12`, `15`, and `26`.  For the
energy endpoint they prove the tighter correlation `|G| <= (7/10) E`, giving
an exact final-expression bound `1029/320`; accumulated operand error still
leaves the strict `< 4` premise needed by the last addition theorem.

The three advertised theorems
`rusanovBits_real_error_of_stateBounds`,
`rusanovBits_real_error_of_guard`, and
`checkedFluxBitsModel_real_error_of_guard` report exactly `propext`,
`Classical.choice`, and `Quot.sound`.  No accepted theorem contains `sorryAx`,
an admission, or a native-decision axiom.  No `dev` host, cleanup, deletion,
maintenance action, reset, stash, checkout overwrite, concurrent Lean process,
or worktree rewrite was used.  The exact-execution draft remained untracked
and untouched by this numerical checkpoint.

One non-semantic follow-up renamed the intentionally unused dissipation-bound
parameter with a leading underscore, removing the only new-file linter warning.
The required materially changed rerun again passed all 3,069 jobs, with 8.0
seconds in the target and approximately 11.4 seconds in the complete local
command; the same three-axiom reports were reproduced.

## 2026-09-04: exact generated-WAT execution completed

After the numerical checkpoint was published and local/remote tree equality
was verified, the preserved `Project/EulerRusanov/Execution.lean` draft was
handed off from its editing agent and inspected.  It contains no admission,
axiom declaration, unsafe definition, or native decision.  The accepted path
is factored into seven private weakest-precondition lemmas for constant setup,
left state, right state, mass, momentum, energy, and output assembly.  Each
lemma takes an opaque continuation so normalization cannot enter the remaining
instruction tail.  The stages cover generated locals 6 through 47 and the
source bodies contain exactly 8, 77, 77, 55, 55, 55, and 8 instructions.

The first build of this staged repair reached all 3,357 jobs and failed
explicitly after 18 target seconds and approximately 21.4 command seconds.
Unlike the earlier 481-second monolithic attempt, it reached every small stage
and exposed only proof-normalization omissions: the restricted stage simp sets
did not reduce concrete natural additions/comparisons/subtractions and list
updates, the accepted endpoint retained the trivial four-result length goal,
and the accumulated rejection finalizers reached the default 200,000 heartbeat
limit.  This was diagnostic output, not a pass.

The next material change added the established concrete-frame reducers
`List.set`, `reduceIte`, `Nat.reduceAdd`, `Nat.reduceLT`, and `Nat.reduceSub` to
each bounded stage; expanded the accepted endpoint only enough to discharge
the four-result length; and raised this proof module's heartbeat allowance to
one million.  That second staged build again reached all 3,357 jobs in 18
target seconds and approximately 21.4 command seconds.  Constant setup,
accepted completion, and every rejection path now closed.  The remaining
stage errors were literal-list reads such as `[...][29]?`, because `simp only`
did not include the `getElem?` recursion rules.

Adding exactly `List.getElem?_cons_zero`, `List.getElem?_cons_succ`, and
`List.getElem?_nil` to each stage was the final semantic-neutral repair.  The
focused exact-execution target then passed:

```text
Project.EulerRusanov.Execution
Build completed successfully (3357 jobs).
new target: 19 seconds
complete command: approximately 21.9 seconds
```

The theorem `Project.EulerRusanov.Spec.rusanovFluxCheckedBits_exact` quantifies
over arbitrary `HostEnv Unit`, initial store, and all six raw binary64 input
words.  It proves fuel-independent termination of generated function zero,
equality of the final and initial complete stores, and exact top-first result
stack equality with `Model.resultValues`.  Thus it covers all ten first-failed
guard paths plus the fully accepted 49-operation path; rejection reaches no
floating-point instruction, while acceptance matches the pure IEEE64 graph
operation for operation.

A final mechanical edit replaced deprecated local aliases with their current
names (`ite_eq_left`, `ite_eq_right`, `ite_true`, and `ite_false`) and imported
both `Numerical` and `Execution` from the Euler Spec root.  The materially
changed combined build passed all 3,369 jobs: Execution took 19 seconds, the
Spec root took 2.0 seconds, and the complete local command took approximately
25.0 seconds.  The exact-execution theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or native-decision
axiom.  Output warnings are inherited from dependencies, not the new execution
file.  No workspace cleanup, deletion, maintenance, reset, stash, checkout
overwrite, remote host, `dev` probe, concurrent Lean process, or worktree
rewrite occurred.

## 2026-09-04: WAT-level Euler numerical transfer completed

`Project/EulerRusanov/WasmNumerical.lean` now defines the accepted-input
`RealErrorSpecFor` boundary expected by the artifact manifest.  It quantifies
over arbitrary host environment, complete initial store, and all six raw
binary64 interface words.  Given the exact raw-word guard, its termination
postcondition combines complete store preservation and exact
`Model.resultValues` stack equality with status zero and
`Numerical.FluxRealError` for the three returned payload words.

The proof is deliberately only a composition boundary.  It applies
`TerminatesWith.mono` to `rusanovFluxCheckedBits_exact`, substitutes the exact
final store and result stack, and supplies
`checkedFluxBitsModel_real_error_of_guard`.  It does not rerun, approximate, or
trust host floating-point arithmetic and adds no operation-specific axiom.

The new file was imported by the Euler Spec root and passed on its first local
serialized build:

```text
Project.EulerRusanov.WasmNumerical: 3.3 seconds
Project.EulerRusanov.Spec: 2.0 seconds
Build completed successfully (3370 jobs).
complete command: approximately 8.8 seconds
```

`Project.EulerRusanov.Spec.rusanovFluxCheckedBits_wat_real_error` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`.  Together with exact
execution, it proves that every accepted generated-WAT call returns the exact
modeled words, all three are finite, and their absolute errors against the
independently defined real fixed-speed Euler--Rusanov flux are bounded by
`10 * 2^-52`, `14 * 2^-52`, and `25 * 2^-52`.  Rejection behavior remains
covered by the total exact-execution theorem rather than making a physical
error claim about rejected payloads.  No cleanup, deletion, maintenance,
remote execution, `dev` access, concurrent Lean invocation, or worktree
rewrite occurred.

## 2026-09-04: first exact-byte f64 artifact registered

The completed Euler case was promoted through a deliberately focused path.
`proofs/talos/cases.json` changed only `euler_rusanov.complete` from false to
true, and the aggregate `Project.lean` gained only
`Project.EulerRusanov.Spec`.  The local command
`node tools/talos-proof.js check euler_rusanov` regenerated only that case and
passed all 3,370 Lean jobs.  It accepted both
`rusanovFluxCheckedBits_exact` and `rusanovFluxCheckedBits_wat_real_error`,
whose axiom reports remain exactly `propext`, `Classical.choice`, and
`Quot.sound`.

The separate focused preparation command completed successfully and reproduced
an exact 1,808-byte module with SHA-256
`145230bc0f956df81283fb37227c303de2c92e68842d38b985325dca467f6546`.
No bulk preparation or migration command was used.  The first invocation of
`node tools/artifact-migrate.js migrate euler_rusanov` exited before writing
any migration output.  A direct diagnostic of `DumpRaw.lean` showed that the
failure was not a binary-decoder rejection: `lean --run` could not find the
unbuilt `Project.Artifact.Binary.Decode.olean`.  Git status confirmed that the
failed migration left only the two intentional registration edits.

The prerequisite was then built locally and serially:

```text
Project.Artifact.Binary.Syntax
Project.Artifact.Binary.Cursor
Project.Artifact.Binary.Leb
Project.Artifact.Binary.Primitives
Project.Artifact.Binary.Decode
Build completed successfully (6 jobs, approximately 4.2 seconds).
```

With that materially changed build state, the same named migration completed
and wrote only the Euler schema-three package, registry row, embedded bytes,
raw cache, decoded cache, decode equality, validation evidence, translation
equality, and external-file lookup.  The packaged `program.wasm` again measured
1,808 bytes and matched the same digest.  Its manifest records exact Lean
4.34.0-rc2, Talos revision `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`,
the two concrete behavior theorems, and an empty host-assumption list.

The independent focused command
`node tools/artifact-proof.js check <frozen-program.wasm>
Project.EulerRusanov.ArtifactTranslation` then passed in approximately 197
seconds.  It checked the package identity, matched all 1,808 external bytes to
the embedded Lean byte array, proved executable decoding and raw-cache
equality, proved validation and `CoreValid`, and proved that translation of the
validated module equals the five-function Talos execution cache.  It then
rebuilt and accepted the complete Euler behavioral specification.

The final declaration audit reported only the standard logical axioms for both
Euler behavior theorems.  The closed artifact identity uses the artifact
format's permitted theorem-local `native_decide` certificates for byte-array
decoding, raw-cache equality, and validation; it contains no `sorryAx` and no
unlisted axiom.  Thus the exact frozen bytes, rather than compiler trust or a
host floating-point run, now carry the total execution and quantitative
real-error claims.  No workspace cleanup, deletion, reclamation, maintenance,
reset, stash, checkout overwrite, worktree rewrite, remote execution, `dev`
probe, or concurrent Lean process occurred.

The cold-cache diagnostic exposed a real driver defect: artifact migration
assumed that an unrelated earlier build had already produced the source
runner's imported object files.  A separate focused follow-up will make the
migration driver build its own `Project.Artifact.Binary.DumpRaw` target once
before decoding, without deleting or invalidating any active-workspace cache.

## 2026-09-04: cold-cache artifact migration repaired

`tools/artifact-migrate.js` now builds the leaf target
`Project.Artifact.Binary.DumpRaw` exactly once after resolving the selected
cases and existing registry and before decoding any selected artifact.  It
uses the repository's locked local `tools/leanrun` envelope with a 15-minute
timeout.  Building the leaf rather than a transitive imported module lets Lake
maintain the complete runner closure when `DumpRaw.lean` changes and avoids one
redundant build per case under a future multi-case invocation.

The source runner now permits 64 MiB of captured raw-module output instead of
Node's default buffer.  On spawn errors, signals, or nonzero exits it relays
both stdout and stderr before reporting the distinct failure, so a missing
object diagnostic cannot again be hidden as an apparent decoder rejection.
All of these checks still happen before transactional artifact outputs are
installed.

The focused `test/artifact_migrate.js` check passed.  It now pins the exact
runner path, timeout, proof-workspace path, leaf target, inherited local
environment, one-time invocation, spawn-error message, nonzero-exit message,
and signal message in addition to its existing transactional-write and
immutable-binary checks.
An actual local invocation of the repaired driver then built all seven
`DumpRaw` jobs (422 ms for the leaf), migrated only `euler_rusanov`, and
completed in approximately 2.5 seconds.  Git status afterward contained only
the driver and test edits: the registered Euler bytes, manifest, registry,
cache, and proof modules were unchanged byte-for-byte.  No cache was deleted
or invalidated to simulate a cold checkout.

## 2026-09-04: frozen verified Euler interface dataset

The first public data product is now `euler-rusanov-interface-v1`.  Its CSV has
the frozen source-order columns
`rho_l_bits,u_l_bits,p_l_bits,rho_r_bits,u_r_bits,p_r_bits`, followed by a
decimal status and the three raw output words.  The eight stable rows are equal
left Sod, equal right Sod, both Sod interface orientations, a moving equal
state, both guard extremes, and a quiet-NaN rejection in `rhoL`.  Binary64
words are lowercase fixed-width hexadecimal without `0x`; the Sod right
pressure is the exact word `3fb999999999999a`, not an implicit rational
replacement for one tenth.

`Project.EulerRusanov.InterfaceData` defines those same eight rows as literal
`UInt64` words.  One named model theorem per row is checked with kernel
`decide`; none uses `native_decide`.  The seven accepted rows also have closed
guard theorems, and the NaN row has a closed false-guard theorem.  The first
expanded closed-model build passed all 3,390 jobs in 9.3 target seconds.  It
reported only reduction-threshold warnings for exponents 2,092 through 2,096,
so the module threshold was raised from 2,048 to 4,096 before the public
contract was added; this was a successful but intentionally superseded
warning-bearing check, not a failure.

The public `AcceptedSpecFor` packages the concrete true guard, zero expected
status, left and right `StateBounds`, both proved characteristic-signal bounds,
and fuel-independent execution preserving the complete store and returning the
exact frozen top-first Talos tuple together with `FluxRealError` for those
same three payload words.  `RejectedSpecFor` packages the false NaN guard and
exact store-preserving rejection tuple.  `InterfaceV1SpecFor` contains all
seven accepted rows and the one rejected row.  Its proof reuses the universal
generated-WAT real-error and exact-execution theorems, weakening their
postconditions only after rewriting by each kernel-checked closed model result.

`artifact_interfaceV1` applies `Artifact.artifact_correct_of` to that complete
eight-row property.  It therefore states that the same exact embedded
1,808-byte artifact decodes, validates, satisfies `CoreValid`, translates, and
realizes every frozen row.  The completed focused build passed all 3,390 jobs
in 9.4 target seconds.  `interfaceV1_generated` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`.  `artifact_interfaceV1` adds only the
three already permitted theorem-local native-decision certificates used by the
artifact package for closed byte decoding, raw-cache equality, and validation;
the row computations themselves add no native-decision axiom.  Importing the
new module from the Euler Spec root passed all 3,391 jobs, and the warmed full
Talos `Project` aggregate passed all 3,748 jobs with 3.3 seconds reported for
the root target.  Warnings were inherited deprecations and lints in existing
dependencies.

The host generator initially used Node's direct `WebAssembly` API.  A
pre-commit repository-policy audit caught that design, and the untracked draft
was revised before publication.  The final JavaScript performs no module
execution.  `tools/wasmtime-host.js` invokes the existing external
`leanexe-wasmtime-host` C runner with four result slots; the generator makes
exactly one such call per frozen row.  Host iteration and CSV serialization
remain regression plumbing, while the Lean theorem supplies the semantic
claim.  The helper validates unsigned decimal results, rejects values above
`2^64 - 1`, and never silently wraps malformed host output.

Before invoking the artifact, the generator uses the repository's shared
registry loader and schema-three manifest validator, then pins the Euler case,
digest, 1,808-byte length, and empty host assumptions.  `check` is the default
and is read-only; `write` must be explicit.  Changed dataset files are written
to unique same-directory exclusive temporary files and installed by atomic
rename, while byte-identical files are left untouched.  Narrow `.gitattributes`
rules pin LF for the exact CSV, data manifest, generator, and host helper.

The CSV is 1,444 bytes with SHA-256
`65ff256da20d19544366083596f20b53c4fb37798209c1e7e16c2cfcee4d3808`.
The manifest records its schema and byte length, row order, word and status
encodings, artifact identity, `gamma = 7/5`, `alpha = 7/4`, rounding mode,
formal module and theorem, and a domain-separated identity covering both
generator sources.  That composite generator digest is
`d47e334f8eb8f63bbbc4af87266e6d2465535ad5a51fa81c439d84ffdf43261d`;
the resulting 2,408-byte manifest has SHA-256
`fa39e7314a5c0709c7e8636df63731cd1649709f7e97c5ee700f9ef89d624118`.

The following focused gates passed locally:

```text
node --check tools/wasmtime-host.js
node --check tools/euler-rusanov-interface.js
node --check test/euler_rusanov_interface.js
node tools/euler-rusanov-interface.js check
node test/euler_rusanov_interface.js
node test/no_js_wasm_execution.js
node tools/talos-proof.js check euler_rusanov
node tools/check-docs.js
lake -d proofs/talos/lean build Project.EulerRusanov.InterfaceData
lake -d proofs/talos/lean build Project.EulerRusanov.Spec
lake -d proofs/talos/lean build Project
git diff --check
```

The dataset test is registered immediately after the existing Euler source
regression in `test/run_all.js`.  It checks exact CSV bytes, field counts, row
order, unique encodings, statuses, payloads, manifest identities, and the host
parser's upper boundary.  The focused Talos gate regenerated the program in a
task-local workspace, rebuilt all 3,391 proof jobs, reproduced the axiom
reports above, and passed.  No `sorry`, `admit`, or new axiom declaration is
present.  The maintained-documentation checker accepted all 90 files.

All commands used the serialized local-only execution contract.  No `dev`
host or other remote executor was invoked or probed.  No cleanup, maintenance,
reclamation, pruning, deletion, cache invalidation, reset, stash,
checkout-overwrite, or worktree rewrite was performed.  Generated and ignored
outputs remain part of the preserved active checkout.  The next independent
checkpoint is regression-only C comparison tooling; it will keep a bit-exact
same-operation-order mirror separate from Lanyon's dynamic-speed flux and will
not be represented as formal evidence.

Publication used the authenticated GitHub Git-data API because ordinary HTTPS
push credentials are not configured.  Every uploaded blob except the first
`devnotes.md` attempt immediately matched the local Git blob identity.  That
first attempt incorrectly used the decoded Unicode character count as a byte
offset while reconstructing the append-only file, producing an unreferenced
blob `1b3cb15d1361ee3ef1f5acbc2a9923cd98ed7feb`.  No tree or ref referenced it.
Using `git cat-file -s` for the exact 1,086,591-byte parent boundary produced
the required local blob `0c38e91b84469538a764b8fbfd447353f5ab5987`.

The API-created tree exactly matched the checked local tree
`4107838828a0c75d3f24082e4040980bda52d48c`.  A non-forced fast-forward moved
`origin/talosfp-euler` from `87b47d0f8f56107d9cc54150330d45bc401e8102`
to the published commit `847d780fed9d2b89cf670eb18b0893e54c861212`
(`Publish verified Euler interface data`).  A subsequent fetch confirmed the
remote tree, after which only the local branch reference was aligned from the
equivalent local commit; the worktree was not rewritten.  Local and remote
commits and trees then matched exactly, and `git status` was clean.

## 2026-09-04: pinned Euler C regression comparison

This checkpoint adds only regression tooling around the already proved
`euler-rusanov-interface-v1` data.  It does not change a Lean definition,
theorem, generated WAT, exact WASM byte, or artifact proof.  The authoritative
claim remains `Project.EulerRusanov.InterfaceData.artifact_interfaceV1`; every
C result described here is explicitly classified as regression-only.

The first comparison program,
`test/fixtures/euler-rusanov-c/fixed-alpha-mirror.c`, reproduces the verified
kernel's raw unsigned-word guard and its exact accepted arithmetic graph.  It
performs 22 binary64 multiplications, 27 binary64 additions, and three exact
sign-word XORs in the source/WAT order.  Its add and multiply helpers
materialize every result through `volatile double`.  With the declared
conservative flags it matched all eight frozen rows exactly, including status
one and three zero payloads for the raw-guard-rejected NaN row.

The second program, `test/fixtures/euler-rusanov-c/lanyon-driver.c`, includes
the unmodified public 1D source in the same translation unit after renaming
its placeholder `main`.  The upstream repository is pinned at commit
`a736aa5f8b17efd225c4692404e2442361d06729`, tree
`373f81b54f06e4bca04d06999e95882e42428ad7`.  The vendored source is 27,229
bytes, Git blob `fbd70a9407d02ce2e49b6d6f37152c70ca679de4`, and SHA-256
`f1f284f550d790c88f293e1d67a91434dc9b8c6187f88caed0f776c5039cf756`.
The 1,070-byte MIT license is Git blob
`16b2ed3f9bee8eeb7bd7291ea6dfef76675b7e32` with SHA-256
`cfa90e3adf9a116fe3959a57353acdf5b6a783d3442d0e5a0834627990370116`.
`upstream.json` records those identities and their GitHub paths.  The
generator now independently recomputes the Git blob SHA-1 framing as well as
the byte lengths and SHA-256 values and checks the pinned commit tree.

The exact upstream C source contains trailing whitespace and lacks a final
newline.  During initial untracked preparation, the file-writing patch added
one extra final newline to both fetched upstream files.  That was immediately
detected by their authoritative byte lengths and corrected only at those two
known byte boundaries before staging.  The final staged source and license
have the exact upstream Git blob identities above.  A narrow `.gitattributes`
rule marks the source `-text -whitespace`: this prevents checkout-time line
normalization and lets `git diff --check` ignore the upstream whitespace
without weakening checks for other files.

The adapter named `verified-dyadic-conservative-v1` converts each accepted
primitive tuple to `(rho, momentum, totalEnergy)` in the verified dyadic
operation order, then calls Lanyon's physical-flux, dynamic-speed, and left
and right fluctuation functions.  It publishes both reconstructions,
`F_L + D^-` and `F_R - D^+`; it never averages or selects between them.
They are algebraically the same flux, but Lanyon independently recomputes and
rounds the paths.  The two paths differ by one or two ulps in components of
the guard-extreme rows, which the focused test requires to remain visible.

Lanyon is not executing the verified algorithm.  It recovers pressure from a
rounded conservative state and computes a dynamic speed with division,
square root, `fabs`, and nested `fmax`, whereas the verified artifact uses the
globally certified fixed speed `7/4` and only its admitted add/multiply graph.
Lanyon's parameter expression is C `7.0 / 5.0`; the driver checks that its
supported-host value is raw binary64 word `3ff6666666666666`.  That is an
approximation to, not equality with, the exact real rational `7/5` in the
proof.  The compiler and system `libm` are intentionally not proof inputs, so
the exact Lanyon words are labeled a supported-host snapshot rather than
portable numerical truth.  There is no Lanyon equality gate or formal-proof
field.  The rejected NaN row is not passed to upstream C at all; the generator
emits thirteen empty fields and the test separately confirms that a direct
driver call exits two, emits no standard output, and names the adapter in its
diagnostic.

Both fixtures compile as C11 with `cc`, `-O0`, `-Wall`, `-Wextra`,
`-Wpedantic`, `-Werror`, `-fno-fast-math`, `-ffp-contract=off`,
`-frounding-math`, `-fno-associative-math`, `-fno-reciprocal-math`,
`-fno-finite-math-only`, `-fno-unsafe-math-optimizations`,
`-fexcess-precision=standard`, and `-lm`.  Runtime checks require an advertised
IEC 60559 environment, eight-bit bytes, 64-bit `uint64_t` and `double`, the
binary64 exponent and significand dimensions, `FLT_EVAL_METHOD == 0`, the
expected word layout for `1.0`, and confirmed `FE_TONEAREST`.  These checks
make the local snapshot explicit but do not turn C execution into proof
evidence.

`tools/euler-rusanov-c-compare.js` first rebuilds and validates the already
published exact-WASM interface dataset through its external Wasmtime host.
It then compiles the two C programs under `build/tests/euler-rusanov-c`, calls
the mirror exactly eight times, and calls Lanyon exactly seven times.  Its
default command is read-only `check`; `write` is explicit and installs only
changed CSV/manifest files by an exclusive temporary file and same-directory
atomic rename.  JavaScript does not execute WebAssembly.  The regression CSV
has 31 columns and eight rows: verified input/output words, exact-mirror
words, an explicit mirror relation, a Lanyon evaluation marker, six adapted
conservative-state words, dynamic alpha, and both three-component Lanyon flux
reconstructions.  It is 4,119 bytes with SHA-256
`21a95065f98f8f3e88962f7545af27b7e7fe8dca9084dfefba048e2d40e78a7e`.
The final 11,629-byte manifest has SHA-256
`617371152767fab7b6b96a0ba8b23c3f74a704617d590ebb4ae9037a05c2b58c`.

The first no-JavaScript-WASM policy run found an identifier in the new test's
own regular-expression literal.  The test was not executing WebAssembly, but
the repository policy correctly rejects that code identifier everywhere
except its policy checker.  The test now constructs the probe identifier from
two string fragments, the unchanged generator contains no direct API call,
and the policy gate passes.  Pre-commit review also caught and corrected the
initial ambiguous `gamma = 7/5` wording, the README's singular `build/test`
path and incomplete flag list, commit-tree/blob validation, and the need for
the narrow `-text` vendor rule.  No incorrect version was committed.

The focused local commands that passed are:

```text
node --check tools/euler-rusanov-c-compare.js
node --check test/euler_rusanov_c.js
node tools/euler-rusanov-c-compare.js write
node tools/euler-rusanov-c-compare.js check
node tools/euler-rusanov-c-compare.js
node test/euler_rusanov_c.js
node test/euler_rusanov_interface.js
node test/no_js_wasm_execution.js
node tools/check-docs.js
git diff --cached --check
```

An independent read-only review repeated the syntax, generator, focused test,
no-JavaScript-WASM, and diff checks and found no remaining blocker.  Direct
Lean was not needed for this checkpoint because no Lean or artifact theorem
changed.  All execution was local.  No `dev` host or other remote executor
was invoked or probed.  No cleanup, maintenance, reclamation, pruning,
deletion, cache invalidation, reset, stash, checkout overwrite, worktree
rewrite, or concurrent Lean process occurred.  Generated and ignored build
outputs remain preserved in the active checkout.

The next theorem checkpoint will state the Euler derivative in conservative
coordinates `U = (rho, momentum, totalEnergy)`.  The standard eigenbasis is
not the eigensystem of the current primitive-coordinate helper.  The plan now
requires an independent conservative flux, its derivative for `rho != 0`, an
agreement bridge at primitive-derived states, `A * R = R * Lambda`, and
`det R != 0`.  Its `H` is specific total enthalpy `(E + p) / rho`, not the
existing IEEE-side field named `enthalpy`, which represents the density
`E + p`.

## 2026-09-04: Artifact inventory, FP verifier pins, and operating contract

This checkpoint restates the complete operating contract at the user's
request and records the artifact-inventory repair discovered after registering
Euler.  It begins from synchronized local and remote commit
`f92983d15b8a3b0a5908b4b01c75532a0ec60683`, tree
`7493cb77f23844e2ce4bd355269902f7da8d0f55`, on branch
`talosfp-euler`.  The intended checkpoint commit message is
`Reconcile FP artifact release inputs`.

### Non-negotiable checkout and execution rules

1. The active checkout is persistent user-owned project state.  This includes
   `.git`, tracked and untracked sources, generated outputs, ignored files,
   dependency trees, compiler products, caches, and evidence receipts.  No
   cleanup, workspace maintenance, reclamation, pruning, deletion,
   cache invalidation, `git clean`, destructive reset, checkout overwrite,
   stash, worktree replacement, or equivalent rewrite is authorized.  A file
   being reproducible does not authorize its removal.  Any deletion requires a
   new user instruction naming the exact target.
2. `git status` is inspected before mutation.  Existing and unrelated changes
   are preserved.  Agents may edit only their assigned files and may not run
   Git mutation, Lean, cleanup, or maintenance unless the root task explicitly
   delegates that exact operation.  No worktree repair may discard a draft.
3. There is no `dev` host.  It is never invoked or probed, and no remote
   compute substitute is assumed.  Lean, Lake, the compiler, artifact tools,
   Node, C compilation, Wasmtime, and conformance execution all run locally.
   GitHub is only the branch publication and recovery remote.
4. The user authorizes direct local Lean.  Lean-family work is nevertheless
   globally serialized to one process.  The exact local command envelope is:

   ```sh
   env LEANRUN_LOCAL=1 \
     LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
     LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
     LEAN_NUM_THREADS=1 \
     WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
     tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build TARGET
   ```

   The same environment is supplied to Node drivers that spawn Lean.  The
   preload maps numeric `/proc/<pid>/exe` reads to `/proc/self/exe` in the
   nested PID namespace.  It is a local execution workaround, not theorem
   evidence.  `tools/leanrun` retains the shared lock and priority controls;
   its warning correctly says that unavailable cgroup CPU, memory, and swap
   limits are not enforced.
5. A timeout with no Lean diagnostic is neither pass nor theorem failure.  It
   is recorded as censored timing evidence and is not repeated unchanged.
   Work proceeds by warming or splitting an identified target boundary, or by
   making a reviewed material proof change.  Failed diagnostics and drafts are
   retained.
6. `journal.md` is the detailed chronological ledger.  It records exact
   commands, environment constraints, warnings, elapsed boundaries, failures,
   passes, axiom reports, byte identities, release receipts, commit intent,
   publication identities, and the next open boundary.  `devnotes.md` is the
   concise durable checkpoint record.  Both are committed and pushed whenever
   changed.
7. Coherent checkpoints are committed and published frequently.  Ordinary
   HTTPS credentials are unavailable, so publication uses the authenticated
   GitHub Git-data API.  Each changed local Git blob is uploaded exactly, a
   tree is created over the current remote tree, its identity must equal the
   complete local tree, a commit is created with the current remote tip as its
   parent, and `talosfp-euler` is advanced with `force: false`.  The ref is
   fetched and the complete remote and local trees are compared.  Only after
   equality may the local ref be aligned; the worktree is never reset or
   rewritten.
8. Native, Wasmtime, and C outputs are regression evidence only.  Formal
   claims come from the pure Talos model, checked generated-WAT execution,
   explicit numerical theorems, accepted axiom audits, and exact frozen bytes
   where an artifact claim is made.  No `sorry`, `admit`, or new axiom is
   accepted.

A read-only documentation search during this checkpoint accidentally placed a
Markdown backtick inside a double-quoted shell argument.  The local shell tried
to execute a command literally named `dev`, returned `command not found`, and
continued the search.  It did not contact or probe any host and made no file or
Git change.  Subsequent shell arguments avoid interpolated backticks.  This is
recorded because the local-only rule includes command-construction hygiene.

### Inventory and pin reconciliation

Adding Euler exposed a metadata inconsistency rather than a binary change.
The twenty pre-Euler frozen manifests still named pre-FP Talos revision
`fda69ca67a81ea4f1fa4e376bdc5861d9fe5479a` and verifier-source SHA-256
`2b59dec86b72be48a2bb63b5fc1efabbf2e61397a7042907823d0a4e6d5fcb01`.
The current exact verifier uses immutable FP Talos revision
`87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47` and verifier-source SHA-256
`bf03d3f47fb11563c947224601a21afa95c62fc88df81f493de821e69de9d1e7`.
Each of the twenty manifests changes exactly those two fields.  Euler's
manifest is unchanged.  No `.wasm`, `.wat`, generated Talos `Program.lean`,
embedded byte module, source case, artifact-registry entry, or handwritten Lean
theorem changes in this checkpoint.  The bulk migration command was not run,
because it would regenerate or add unrelated packages.

The exact post-repair manifest SHA-256 identities are:

| Package | Manifest SHA-256 |
|---|---|
| `append_bang` | `9c59d472abfda776ad3399b121ecd764a680a81a200aa827634f6e1b06c34c0c` |
| `assoc_list` | `256b23c0efed4cb362d45e3c7b738940184f36b9c6206e699eb98d5fc40dd617` |
| `box_free` | `09314433c9423d72373cc345b90bc643d10889565adfdb7d3da771eb52f29db8` |
| `clob_cancel` | `d64f41f86cd431b45aa2cb85debcb7b518f62ab4fcb220ffc1d8c63bffb89592` |
| `clob_depth` | `a5a0598c99d152928933513ea35eff4110841215467a24632544e93c00554cc2` |
| `clob_find_best` | `ad4be889530bbd24fdfb3a3a9415a34a71bdefd28d7109318f65f54ec8b7896c` |
| `clob_limit` | `142c54f1420a9d5bc6c963ab7b6ac353eb607c5e935e5ba77039ec8f7b736f` |
| `clob_market` | `fa8d9eb0ba483bce4b6b0e41be2962d374450861750ae2bed547fd4e6dad06c9` |
| `clob_match_fuel` | `082274c350142506d03ec3d2e1c3f5e6f08382b82cf17847239bf80085bbe9e1` |
| `clob_post_only` | `ddb5e993fb59ccd9f1330d9aea19665dbc4c7bc02f31d04c4ff8b45b791d3934` |
| `clob_quote` | `6472e3ff494eba89bd8fe9a3c045557a29f4f0be3cefde9f3d8498c88d3d131e` |
| `fold_sum` | `f9d7438bcfa759e956c342ada739a15a44a1a26c0b76b1114f5c051e5c78cfdf` |
| `gcd` | `2bf285395d50f29e928ab720987a5188f5c3ca9436ff7f055f2670e3bc9e120d` |
| `leb_u32` | `de84ec5028a577e4819276115bafc10602e0220900821653892db8729e951dd9` |
| `order_book` | `b62252f15d8e9ed85561d60dc3482aa07191c3d3aefd27423d2d12cc812637c4` |
| `pair_free` | `f8cd613742633bb53e44e3419facaf0436cc029036ac131e0c83e107c4be62ba` |
| `push_size` | `04d909a7ca2b75e4cd70ef36c9d5565440563ab46d75b6538293e1b77afba789` |
| `push_twice` | `db0312ddb0a7556854c42210dbc0b029d7c7f68d7941eb7477fc8eeeb8cb2fbf` |
| `shared_pair` | `101437e85f5bf4b95feabaa12e271163941dd66f2c895e8635fbb6fe2d3aaa66` |
| `validate` | `437927d34b0d0c487fe887e5edf001f8148a392b1e647b7a55a5413e794301bf` |

The inventory has three deliberately different counts: twenty-five
source-driven cases, twenty-five tracked `Program.lean` caches, and twenty-one
registered frozen exact-artifact packages.  Four floating-point source cases
remain source-driven only; Euler is the first floating-point exact package.
All twenty-one `program.wasm` hashes still equal their content-addressed
directory names.  Euler remains exactly 1,808 bytes at SHA-256
`145230bc0f956df81283fb37227c303de2c92e68842d38b985325dca467f6546`.

`proofs/artifacts/release.json` was regenerated from, rather than hand-edited
against, these inputs.  Before current warm receipts it correctly validates as
a twenty-one-package draft with release-input SHA-256
`bbc645be04edcae73d6d36958a01b85bfa0a24f7660fc0ccb801ac6e133711a3`,
artifact-registry SHA-256
`3bcc91129e242bf7ed0576ba3c9f8c15f2b715ff4e251d93d04fd2b452031bec`,
and conformance-config SHA-256
`b96c3386c340a6bd55762bcee3a077deda03a7dced2cbe3bc62440a6b9a93d16`.
It has four honest blockers: immutable source revision, current aggregate
artifact-proof receipt, current semantic-conformance receipt, and cold-checkout
receipt.  `sourceRevision` remains null and the draft is not release-ready.

The focused migrated GCD exact-artifact gate passed every identity, decode,
validation, translation, behavior, manifest-declaration, and axiom check.
Behavioral declarations reported only `propext`, `Classical.choice`, and
`Quot.sound`; closed artifact certificates used only the format's accepted
theorem-local decision certificates.  These non-Lean checks also passed before
this notes cut:

```text
node --check test/artifact_identity.js
node --check test/artifact_release.js
node test/artifact_identity.js
node test/artifact_migrate.js
node test/artifact_conformance.js
node test/artifact_release.js
node tools/check-docs.js
git diff --check
```

An initial aggregate `artifact-proof.js check-all` process was deliberately
interrupted after the final `conformance.json` wording change altered the
derived release input while it was still near the beginning of the package
list.  The interruption superseded a now-stale receipt; it was not a proof
failure and changed no tracked file.  One replacement aggregate then began
under the exact serialized local envelope above.  At the 10:26 UTC notes cut,
it had passed every emitted target so far, including Euler artifact translation
and multiple later behavioral specifications, with only inherited deprecation
warnings.  It remained the sole Lean-family process.  Its final result and
receipt will be recorded in a separate immediate checkpoint, followed by the
serialized conformance gate, release refresh, and the two remaining release
blockers.  Committing these notes while the check runs changes Git metadata
only; it does not alter any source or proof input seen by that process.

The documentation audit corrected current-versus-historical wording without
rewriting dated 2026-08-26 evidence.  Current prose now distinguishes the 25
source caches from the 21 exact packages, marks the restricted binary64 plan
active, reports the refreshed draft rather than a pre-migration draft, and
keeps the source-driven 25-case aggregate separate from release inspector
receipts.  Historical twenty-package and self-host measurements remain dated
and unchanged.

## 2026-09-04: current aggregate receipt and conformance cache warm-up

This checkpoint began from published commit
`d71a24110869d23348f87a164fd8c8836093dfa1`, whose complete tree is
`7bd896dc8f54ff3de0532943d785741b934eeea3`.  Local `HEAD` and
`origin/talosfp-euler` agreed and `git status --short --branch` was clean before
the evidence commands.  The standing operating contract did not change:

- the complete checkout, `.git` database, untracked and ignored dependencies,
  compiler caches, generated evidence, and partial build products are
  persistent user-owned state;
- no cleanup, maintenance, reclamation, pruning, cache invalidation, stash,
  destructive reset, checkout overwrite, worktree rewrite, or deletion is
  authorized;
- there is no `dev` host, and no command may invoke or probe one;
- all compiler, Lean, Lake, Node, C, Wasmtime, and artifact work is local;
- only one Lean/Lake/compiler process may run at a time;
- a timeout without a semantic diagnostic is neither a pass nor a failure, and
  an unchanged timed-out boundary is not repeated;
- `journal.md` is the detailed command ledger, `devnotes.md` is the concise
  durable checkpoint, and both travel in each coherent commit and push.

The local driver envelope remained:

```sh
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  LEAN_NUM_THREADS=1 \
  WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  <local command>
```

The preload maps numeric `/proc/<pid>/exe` reads made by Lean in the nested PID
namespace to `/proc/self/exe`.  It is an environment workaround, not proof
evidence.  Direct local Lean remains explicitly authorized; no self-hosted
emitter or remote execution path was used.

### Twenty-one-package aggregate result

The serialized replacement `node tools/artifact-proof.js check-all` completed
with exit status zero.  It passed all twenty-one packages through exact package
identity, embedded-byte equality, decoder evidence, validator evidence, Talos
translation equality, behavioral specifications, manifest declarations, and
the final declaration/axiom audit.  The emitted receipt is exactly:

```json
{
  "schemaVersion": 1,
  "date": "2026-09-04",
  "result": "passed",
  "artifactCount": 21,
  "releaseInputSha256": "bbc645be04edcae73d6d36958a01b85bfa0a24f7660fc0ccb801ac6e133711a3"
}
```

The audit reported the expected standard logical axioms and the artifact
format's accepted theorem-local `native_decide` or `bv_decide` certificates for
closed artifact facts.  It found no `sorryAx`, `sorry`, `admit`, or newly
introduced axiom.  The ignored receipt at
`build/evidence/artifact-proof.json` is machine evidence; the refreshed tracked
release record is its durable binding.

### Pinned testsuite initialization

The first serialized `node tools/artifact-conformance.js check` attempt exited
before execution with:

```text
WebAssembly testsuite revision mismatch: expected
9233a0a8d5920a8d32358ee915a3662ff3385029, found
87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47
```

This was not a Talos or WebAssembly result.  The read-only submodule status
showed `-9233a0a8d5920a8d32358ee915a3662ff3385029 vendor/testsuite`: the pinned
gitlink existed but its checkout was uninitialized, so revision discovery from
that directory escaped to the parent CodeLib repository.  The missing pinned
data checkout was initialized in place with:

```sh
git -C proofs/talos/lean/.lake/packages/CodeLib \
  submodule update --init vendor/testsuite
```

Git cloned the configured WebAssembly testsuite submodule and checked out exact
revision `9233a0a8d5920a8d32358ee915a3662ff3385029`.  Parent CodeLib remained at
`87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`.  No existing checkout, cache, or
file was removed, replaced, reset, or cleaned.  The initialized dependency is
ignored project state and remains preserved in the active checkout.

### Current conformance attempt

The conformance command was rerun under the same serialized local envelope.
`Project.Artifact.Binary.ClassifyFile` built, and all fifteen selected official
`assert_invalid` and `assert_malformed` modules matched their configured exact
decoder or validator classification.  This partial observation is not a
conformance receipt.

The next stage began building the pinned Talos testsuite runner.  The driver
reads 366 `public import` declarations from the checked-out
`Mathlib/Tactic.lean` and prewarms them in twenty-three serial chunks: twenty-two
chunks of sixteen targets and one chunk of fourteen, each through
`tools/leanrun --timeout 30m`.  It then builds the exact
`Interpreter.Testsuite.Exec` and `testsuite` targets separately.  The displayed
Lake graph advanced through approximately 2,005 jobs during the first broad
cache-warm boundary, without an emitted Lean error, before that boundary exited
with status `124` at its configured thirty-minute limit.  The outer conformance
driver consequently exited nonzero and wrote no
`build/evidence/artifact-conformance.json` receipt.

The broad closure is expected under the current pin and is not caused by the
WAST data submodule or the Euler source.  `Interpreter.Testsuite.Exec` imports
the `Interpreter.Wasm` umbrella, which imports twenty runtime, proof, and host
modules; `Wasm.Wp.Defs` reaches `Mathlib.Tactic`, and the random host reaches
Mathlib probability and numerical tactics.  Static read-only inspection
estimated roughly 2,930 non-core modules below `Mathlib.Tactic` and roughly
3,235 package modules below the current executable.  The command already names
the narrow executable target, so changing only the Lake target cannot prune
source imports.

Every completed object and dependency cache from the timed-out attempt remains
in place.  The no-repeat rule means the cold boundary will not simply be rerun
as though nothing changed.  A later resume is materially different because it
can consume the preserved cache.  A genuinely narrower permanent runner would
require a reviewed immutable CodeLib change removing only the redundant
`import Interpreter.Wasm` umbrella from `Interpreter/Testsuite/Exec.lean` while
retaining its explicit `Wasm.SmallStep`, `Wasm.Decoder.Wat`, `Wasm.Validate`,
and `Lean.Data.Json` imports, followed by identical suite results under the new
pin.  No local dirty dependency edit was made in this checkpoint.

During the long run, one read-only process-list diagnostic was attempted:

```sh
ps -eo pid,etimes,args | rg 'artifact-conformance|leanrun|lake' | rg -v 'rg '
```

Because that diagnostic inherited the process-path compatibility preload, it
returned `fatal library error, lookup self`.  It performed no mutation and was
not retried while the conformance process was active.  This is recorded both as
a diagnostic incident and as a reminder to remove the Lean-specific preload
from unrelated `/proc` inspection.  It did not invoke or probe any host.

### Refreshed release state

After the timed-out process had exited, and only after another status
inspection, the tracked release record was regenerated and inspected:

```text
Artifact release evidence refreshed: 21 packages, 3 blockers
Artifact release record is draft: 21 packages, 3 blockers
blocker: No immutable source revision records the current proof implementation.
blocker: The conformance gate has not passed under the selected toolchain.
blocker: The release gates have not passed from a cold checkout of the recorded source revision.
```

`proofs/artifacts/release.json` now records the passing 2026-09-04 aggregate
artifact receipt and its exact release-input digest.  Its conformance fields
remain pending and zero-valued because no receipt exists; the record does not
invent or copy the fifteen classifier observations into a full-suite result.
The blocker count decreased honestly from four to three.  The release is still
a draft and no readiness claim is made.

### Reviewed mathematical implementation boundary

Four concurrent reviews were deliberately read-only: they made no checkout or
Git change and ran no Lean/Lake process.  They converged on the following module
sequence for the next implementation checkpoints:

1. `RealConservative.lean` defines conservative state vectors, density,
   momentum, total energy, pressure, velocity, specific enthalpy, physical
   flux, admissibility, and exact bridges to the existing primitive `Model`.
2. `RealMatrices.lean` defines the explicit conservative flux Jacobian and its
   denominator-free reduced `(u,H)` form.
3. `RealJacobian.lean` proves `HasFDerivAt physicalFlux (jacobianCLM U) U` when
   density is nonzero, then exposes the matrix action as the derivative.
4. `RealEigenbasis.lean` constructs characteristic values `u-c`, `u`, `u+c`,
   all three right eigenvectors, the matrix equation `A * R = R * Lambda`, a
   nonzero positive determinant, strict ordering, and an actual `Basis` of
   Mathlib `HasEigenvector` certificates for admissible states.
5. `RealGuardBridge.lean` transports existing raw-word `StateBounds` and guard
   facts to real admissibility and a strict spectral-radius bound below the
   fixed `7/4` Rusanov speed.
6. `RealStencil.lean` proves an exact-real three-cell update, a transmissive
   two-cell Sod specialization, admissibility under strict CFL, and exact total
   balance with the correct physical boundary-flux term.
7. `StencilNumerical.lean` and `StencilArtifact.lean` propagate the already
   certified componentwise errors for exact artifact rows `sodLL`, `sodLR`, and
   `sodRR` through a decoded-real update and balance theorem.

The scope distinction is mandatory.  The present 1,808-byte artifact executes
the three interface-flux calls.  Lean may assemble their certified decoded
values over the reals and bound the resulting cell update, but that does not
prove the update subtraction and scaling executed in WebAssembly.  The name
`decodedTransmissiveStep` will mark this intermediate layer.  A claim called a
WASM stencil is reserved for the later compiled one-step artifact and its own
IEEE operation graph.  Native, Wasmtime, and C comparisons remain regression
evidence only.

This checkpoint commits the refreshed three-blocker release record, maintained
status prose, plan split, and both note ledgers before any new mathematical
source is introduced.  The next mutation begins with the small
`RealConservative.lean` boundary and a focused serialized local build.

The pre-publication non-Lean gates all passed: `git diff --check` was silent,
`node tools/check-docs.js` checked 90 maintained Markdown files,
`node test/artifact_release.js` checked release identities, receipts, pins,
results, and blockers, `node tools/artifact-release.js audit-kernel-scope`
passed the recorded project and two local LeanExe import roots, and a final
`node tools/artifact-release.js inspect` reproduced the exact twenty-one-package,
three-blocker draft above.  A targeted stale-wording search found no maintained
claim that the current twenty-one-package artifact aggregate remains pending.

## 2026-09-04: conservative Jacobian implementation checkpoint

Work resumed from published commit
`c0c9627ec8ac3985ea357440e79b3de101f32f72`, whose complete tree is
`029a0a06742bfc724d0cdb8b43a6c4b3ce991953`.  A status inspection showed that
the branch and its GitHub tracking ref were aligned and the only worktree
changes were the three new, initially untracked Euler theorem modules described
below.  No cleanup, deletion, cache invalidation, stash, destructive reset,
checkout overwrite, worktree rewrite, remote-host probe, or parallel Lean job
was performed.  A process-list check inherited the already documented
Lean-specific `/proc` compatibility preload and returned `fatal library error,
lookup self`; it was not retried.  This diagnostic made no mutation and did not
contact any host.

All compiler invocations in this checkpoint used one serialized local process
and the exact standing envelope:

```sh
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  LEAN_NUM_THREADS=1 \
  WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build TARGET
```

`RealConservative.lean` introduces the independent exact-real conservative
state `Vec3 = Fin 3 -> Real`, density, momentum, total energy, velocity,
internal energy, pressure, specific enthalpy, squared sound speed, the
primitive-to-conservative map, and the expanded conservative Euler flux for
`gamma = 7/5`.  It proves coordinate bridges to the existing independent
primitive `Model`, exact pressure and flux identities, the open admissible set,
and the enthalpy/sound-speed relation used by the eigensystem.  The first
focused build passed in 5.8 seconds over 3,059 jobs but reported two local
linter findings: a density-nonzero argument was unnecessary for the internal
energy identity, and a trailing `ring` after the flux-vector `simp` was
unreachable.  The identity was strengthened by removing the unnecessary
hypothesis from both internal-energy and pressure bridge theorems, and the
unreachable tactic was removed.

The first rebuild after that strengthening exited nonzero because one caller in
`primitiveToConservative_admissible` still supplied the removed argument:

```text
Project/EulerRusanov/RealConservative.lean:206:8:
Function expected at pressure_primitiveToConservative q
```

That exact call site was corrected.  The next focused build passed in 5.8
seconds over 3,059 jobs with no local source warning.  The failed build deleted
nothing and its completed cache state was retained.

`RealMatrices.lean` introduces the displayed three-by-three conservative flux
Jacobian in coordinates `(rho,m,E)`, the denominator-free reduced matrix in
terms of velocity `u` and specific total enthalpy `H`, and proves their equality
when density is nonzero.  Its first focused local build passed in 7.1 seconds
over 3,060 jobs.

`RealJacobian.lean` gives the matrix a semantic calculus meaning.  It turns the
matrix into a continuous linear map, constructs the three component
derivatives from coordinate, reciprocal, product, and power rules, proves the
row map equals matrix multiplication, and exports:

- `hasFDerivAt_conservativeFlux`;
- `fderiv_conservativeFlux`;
- `fderiv_conservativeFlux_apply`.

The first derivative build populated previously uncached Mathlib calculus and
analytic dependencies for about five minutes, then exited with two parser
errors at the scoped matrix-vector notation and two local linter observations
in the row-map simplification.  The completed dependency objects were
preserved.  Adding `open scoped Matrix`, removing the unused
`Matrix.mulVecLin_apply` simplifier, and removing the unreachable `ring` were
the complete repair.  The warm rerun passed in 7.6 seconds over 3,146 jobs.

Explicit `#print axioms` audits were then added for the central bridge,
admissibility, thermodynamic, reduced-matrix, derivative, and derivative-action
theorems.  A final serialized build of the derivative target passed in 14.8
seconds over 3,146 jobs.  Each audited theorem depends only on Lean's expected
logical infrastructure `propext`, `Classical.choice`, and `Quot.sound`; no
project axiom, `sorry`, or `admit` appears in the checkpoint.

The checkpoint intentionally proves the Jacobian of the exact conservative
flux, rather than differentiating the existing primitive-coordinate helper or
using native/C output as proof.  It changes no WAT, WASM, artifact bytes,
release manifest, dependency pin, or generated evidence.  Adding these project
sources changes the aggregate release-input digest, so the previously passing
aggregate receipt must not be represented as current after this commit; the
release record will be refreshed before publication and will honestly restore
the aggregate-proof blocker for the new source tree.

The release record was then refreshed locally.  Its new release-input SHA-256
is `fd356f40d91ab595660cc307745e0e2f7f390ced16f43ead9bf5cc9140525104`.
Inspection reports twenty-one packages and exactly four blockers: immutable
source revision, aggregate artifact proof for this new input, semantic
conformance, and the cold-checkout gate.  This is the expected honest
transition from the prior three-blocker record; no old receipt was reused for
the changed source digest.

Pre-publication checks passed: `git diff --check`; the 90-file maintained
documentation check; release identity, receipt, pin, result, and blocker tests;
the recorded kernel-scope audit; and final release inspection reproducing the
twenty-one-package, four-blocker draft.  A targeted scan of the three new
modules found no `sorry`, `admit`, or axiom declaration.

### Publication of the conservative Jacobian checkpoint

The six explicitly staged blobs were uploaded through the GitHub Git-data API
and each returned the exact local Git object identity:

```text
07d26f232f76a70956ddb7d9017affac259dfce5  devnotes.md
ceda9da4f2f7dbca89f0c8956d30c23e532ff4b4  journal.md
56a89295843cdcd9bfbb0e8eafc0ef2675f4df09  proofs/artifacts/release.json
9e3c1a07e0669e6a3c4d89b8cf90009d54c5e022  RealConservative.lean
14952cb14550180ccf25802bf50d23b30758662d  RealJacobian.lean
b53c91825cee41fd16301f7b2ec9ef0d658c8b8d  RealMatrices.lean
```

The API tree based on remote parent tree
`029a0a06742bfc724d0cdb8b43a6c4b3ce991953` was exactly the staged local tree
`25e96e0af09398cb2b7a38444caa462c724f0f48`.  A second remote comparison
confirmed branch `talosfp-euler` was still identical to parent
`c0c9627ec8ac3985ea357440e79b3de101f32f72`.  GitHub created commit
`868a130d1174389c4ddc20b2ea87a5b9ffc9de07` with that sole parent and moved the
branch through a non-forced update.  A local fetch then independently reported
the same commit, parent, and complete tree; only after that equality check did
`git update-ref` advance the local branch.  Local and tracking refs aligned,
and the sole remaining worktree item was the isolated untracked eigenbasis
draft.  No checkout, reset, merge, stash, worktree rewrite, or file removal was
used during publication.

## 2026-09-04: complete conservative Euler eigenbasis

`RealEigenbasis.lean` now supplies an actual strict-hyperbolicity certificate,
not merely three expressions of type `Real`.  Its parameterized algebraic
layer defines eigenvalues `(u-c,u,u+c)`, the diagonal characteristic matrix,
and the right-eigenvector columns

```text
(1,u-c,H-u*c), (1,u,u^2/2), (1,u+c,H+u*c).
```

It first computes the complete residual of `A*R-R*Lambda` as a matrix whose
only nonzero symbolic factor is
`(2/5)*(H-u^2/2)-c^2`.  The acoustic relation therefore yields the exact matrix
eigenrelation and each column equation.  It proves
`det R = 2*c*(H-u^2/2)`, strengthens this to `5*c^3` under the acoustic
relation, obtains nonzero determinant and linear independence for `c != 0`,
constructs an actual `Basis (Fin 3) Real Vec3`, and packages each column with
Mathlib's nonzero `Module.End.HasEigenvector` predicate.  Positive `c` gives
strict ordering.

The physical specialization takes
`c = sqrt (gamma*p/rho)`.  Conservative admissibility proves `c > 0` and the
acoustic relation.  The explicit conservative Jacobian then satisfies the
full matrix/column equations, its right-eigenvector determinant is
`7*c*p/rho > 0`, and `exists_strict_complete_eigenbasis` returns three
strictly ordered real characteristic values together with a spanning basis of
genuine eigenvectors.

The first focused build exited nonzero after 11.8 seconds.  It identified two
definitions involving real division that needed a noncomputable section; the
scoped `*ᵥ` notation was not open; matrix residual simplification left nine
`Matrix.vecMul ... (Matrix.diagonal ...)` terms; `Basis` and `HasEigenvector`
needed their pinned namespaces; and the physical matrix relation needed
`eigenvalueMatrix` unfolded.  This was a source/API-shape failure, not an
accepted theorem, and no generated object or cache was removed.

The repair opened the Matrix scope, made the section noncomputable, used the
pinned targeted `Matrix.vecMul_diagonal` lemma, wrote
`Module.End.HasEigenvector` explicitly, and unfolded `eigenvalueMatrix` at the
specialization bridge.  The second build, 7.2 seconds, confirmed that every
algebraic residual and eigenvector equation was solved; its remaining errors
were the unqualified `Module.Basis` name and dependent cascades.  Opening
`Module` left only the explicit `[Decidable (Nonempty (Fin 3))]` requirement of
`basisOfPiSpaceOfLinearIndependent` on the third build, 7.1 seconds.  Opening
the pinned `Classical` scope supplied that construction instance.  The fourth
build passed in 7.2 seconds over 3,063 jobs and reported only two no-op `change`
tactics.  Removing those tactics and adding axiom audits produced a clean final
focused build in 7.4 seconds over 3,063 jobs.

The five explicit audits cover the parameterized matrix relation, determinant
identity, physical matrix relation, positive physical determinant, and final
complete eigenbasis theorem.  Each reports only `propext`,
`Classical.choice`, and `Quot.sound`.  There is no source `sorry`, `admit`, or
new axiom.

`RealMathematics.lean` now provides the deliberate umbrella for
`RealJacobian` and `RealEigenbasis`, with an explicit note that exact-real
matrix and square-root operations are not claimed to execute in the current
artifact.  `Project.lean` imports that umbrella.  The umbrella target passed
in 5.0 seconds over 3,150 jobs, and the complete `Project` root passed in 6.2
seconds over 3,803 jobs.  Its voluminous output consists of existing replayed
dependency/project deprecation and linter warnings; the new eigenbasis target
itself has no local warning after cleanup.

The root and Euler plan checklists now mark the conservative derivative and
complete eigendecomposition milestone done.  The next active milestone is the
exact-real and decoded transmissive finite-volume step; it retains the hard
scope boundary that current WebAssembly proves the three flux calls, not the
update arithmetic.

Refreshing release evidence for the integrated source tree preserves the
twenty-one-package draft and its four honest blockers.  The new release-input
SHA-256 is `c84b3584020f82336922d30d54eb4edff52607c5fe0f13ea2e91216213f066c9`;
no previous aggregate receipt is treated as current for this changed input.

Pre-publication checks passed for this checkpoint: whitespace/diff validation;
the 90-file maintained documentation check; release identity, receipt, pin,
result, and blocker tests; kernel-scope audit; final four-blocker inspection;
and a targeted source scan finding no `sorry`, `admit`, or axiom declaration in
the eigenbasis or umbrella modules.

## 2026-09-04: local-only and no-maintenance contract restated

The user required every operational constraint to be written down and
published before implementation continues.  This is a documentation-only
checkpoint.  Its intended commit message is
`Restate local-only workspace operating contract`.

The starting state was inspected before mutation.  Local `HEAD` and
`origin/talosfp-euler` were both
`c4243339b7db0dfc21c0146f911136587715a0e1`, with complete tree
`867d1ea797ed60bb1537017c8ba2ddb0835f2866`.  The worktree contained exactly
two untracked implementation drafts:

- `proofs/talos/lean/Project/EulerRusanov/RealGuardBridge.lean`;
- `proofs/talos/lean/Project/EulerRusanov/RealStencil.lean`.

They are persistent project data.  Neither draft is edited, staged, moved,
discarded, or otherwise changed by this checkpoint.  Only `plan.md`,
`journal.md`, and `devnotes.md` are eligible for its explicit staging set.

The complete current operating contract is:

1. The checkout is persistent user-owned data, not disposable scratch space.
   This protection includes `.git`, tracked files, untracked drafts, generated
   outputs, ignored files, submodules and dependency trees, compiler products,
   build directories, caches, evidence receipts, and partially completed work.
   The earlier automated removal of a complete checkout was data loss, not a
   valid maintenance operation and not precedent for deleting this checkout.
2. No assistant, delegated agent, automation, or generic workspace facility is
   authorized to perform cleanup, maintenance, reclamation, pruning, deletion,
   truncation, cache invalidation, `git clean`, destructive reset, checkout
   overwrite, stash, worktree replacement, recursive removal, or an equivalent
   rewrite.  Calling an action "maintenance", "cleanup", "repair", or
   "reproducible" does not authorize it.  Any operation that might delete,
   replace, invalidate, move, or rewrite project state must stop for a fresh
   user instruction that names the exact target.  No broad path, glob, or
   unresolved environment variable may stand in for that target.
3. Inspect `git status` before every mutation.  Preserve all unrelated and
   in-progress changes.  Stage only explicitly reviewed paths.  A failed build,
   timeout, stale receipt, or reproducible dependency is never permission to
   discard a file or cache.  Retain useful partial build state and diagnose in
   place.
4. There is no `dev` host.  Never invoke it, probe it, test for it, or fall back
   to it.  Lean, Lake, the LeanExe compiler, Talos proof checks, artifact
   preparation, Node tests, C regression programs, Wasmtime, wasm-tools, and
   conformance execution all run locally.  GitHub is used only as the branch
   publication and recovery boundary.
5. Direct local Lean execution is explicitly authorized.  Only one
   Lean/Lake/compiler process may run at a time across the whole task, including
   delegated work.  The standard command envelope is:

   ```sh
   env LEANRUN_LOCAL=1 \
     LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
     LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
     LEAN_NUM_THREADS=1 \
     WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
     tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build TARGET
   ```

   Use the same local envelope for proof-driving tools that spawn Lean.  The
   runner provides the shared lock, pinned toolchain, one-thread setting,
   priority controls, and explicit timeout; its warning that cgroup resource
   limits are unavailable is accurate and must remain visible.  Do not nest
   `tools/leanrun` and do not use the self-hosted emitter or its gates.
6. The session-local preload is only a nested-PID-namespace compatibility
   workaround.  It redirects numeric `/proc/<pid>/exe` reads made by Lean to
   `/proc/self/exe`; it is not repository source or theorem evidence.  Do not
   inherit it into unrelated diagnostics.  A previous read-only `ps` command
   under the preload returned `fatal library error, lookup self`, changed
   nothing, and is not to be retried in that environment.
7. A timeout without a Lean diagnostic is censored timing evidence, neither a
   success nor a theorem failure.  Record it and do not rerun the unchanged
   target.  Retry only after a material proof change, a reviewed dependency
   split, or materially changed preserved cache state.  Compiler diagnostics,
   failed attempts, warnings, timings, and repairs belong in this journal.
8. `journal.md` is the detailed append-only chronological ledger.  It records
   commands, environment, results, failures, proof boundaries, axiom audits,
   byte and manifest identities, commit intent, publication identities, and
   next work.  `devnotes.md` is the concise durable checkpoint summary.
   `plan.md` retains the scope, gates, and operating rules.  Update, commit, and
   publish these records at every coherent checkpoint.
9. Commit and push coherent work frequently.  Because ordinary HTTPS write
   credentials are not assumed, publish through the authenticated GitHub
   Git-data API: upload exact staged blobs; build on the current remote parent
   tree; require the API tree to equal the complete staged local tree; create a
   commit with the current remote tip as its sole parent; move
   `talosfp-euler` with `force: false`; fetch it; require commit, parent, and
   full-tree equality; and only then align the local ref.  Publication must not
   reset, check out, merge, stash, clean, or rewrite the worktree.
10. Formal claims require exact reviewed Lean/Talos/WAT/WASM evidence at their
    stated boundary.  Native, C, and Wasmtime outputs remain regression
    evidence.  No `sorry`, `admit`, or new axiom is accepted.  The current
    1,808-byte artifact proves three interface-flux calls only; an exact-real or
    decoded finite-volume update must not be described as an executed WASM
    stencil until a separate compiled one-step artifact exists.

After this documentation checkpoint is published and independently fetched,
implementation resumes locally with the two preserved drafts.  Their first
Lean checks remain serialized; failures will be journaled and no build or
dependency state will be cleaned in response.

A separate read-only audit checked the canonical journal contract and the
shorter plan and development-note summaries.  It found the collective record
complete and identified two phrases that were only implicit in the shorter
summaries: inspect `git status` before every mutation, and explicitly preserve
dependency, build, cache, and evidence-receipt state.  Both summaries now state
those requirements literally.  The audit ran no Lean, Git mutation, cleanup,
or file edit.

Pre-publication validation passed: `git diff --check` emitted no diagnostic and
`node tools/check-docs.js` accepted all 90 maintained Markdown files.  A fresh
status inspection still showed only the three intended modified documentation
paths and the same two untouched untracked drafts.

## 2026-09-04: exact-real transmissive stencil passes

After publication of the operating-contract checkpoint as
`d72d25be352412dccb53713cc3f2e406acf7c220`, complete tree
`301d3e80cd18e35acef7b650472e3766eeec8d9b`, local and tracking refs were
identical.  The only worktree paths were the two preserved untracked Lean
drafts.  The first implementation target was
`Project.EulerRusanov.RealStencil`.

The pre-checkpoint diagnostic build of the original draft exited nonzero after
about 6.6 seconds over a 3,060-job target.  It gave four precise source
diagnostics:

1. `sodRight` used real division in a computable definition;
2. left-cell pressure positivity reduced to
   `9 / 1150 < ![207 / 256, 9 / 80, 257 / 128] 2`;
3. right-cell pressure positivity reduced to
   `1 / 50 < ![81 / 256, 9 / 80, 95 / 128] 2`;
4. the total-energy equality retained both third-coordinate vector
   projections instead of reducing them.

Those were elaboration and normalization failures, not accepted claims.  The
temporary axiom output containing `sorryAx` came solely from the open goals in
that failed compilation; no source `sorry`, `admit`, or axiom declaration was
present.  No generated object, dependency, or cache was removed or invalidated.

The repair changed `sodRight` to `noncomputable def` and inserted explicit
`change` statements for the two rational pressure expressions and the final
energy sum before `norm_num`.  It did not alter any value or theorem statement.
A separate static audit independently proposed the same minimal patch and ran
no Lean, Git mutation, or file edit.

The exact serialized local command was:

```sh
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  LEAN_NUM_THREADS=1 \
  WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build \
    Project.EulerRusanov.RealStencil
```

It passed in 6.6 seconds wall time, reporting 3,060 completed jobs and a
4.3-second focused module build.  The replayed dependency warnings were the
existing deprecation and linter output.  The new module emitted no local
warning.  Its five printed audits—for generic balance, transmissive balance,
the exact quarter-step, and both cell-admissibility theorems—each depend only
on `propext`, `Classical.choice`, and `Quot.sound`.

The accepted result remains exact-real mathematics.  It proves the three
exact Sod interface fluxes, the two updated conservative vectors, open-set
admissibility of both cells, and exact total density, momentum, and energy
identities.  It makes no claim that update arithmetic executed in the current
WebAssembly artifact.

## 2026-09-04: decoded guards imply real hyperbolicity bounds

The next serialized target was
`Project.EulerRusanov.RealGuardBridge`.  A read-only API audit first confirmed
that `Bounds.StateBounds`, `Bounds.stateGuard_spec`,
`Bounds.eulerGuard_spec`, and `StateBounds.signalSpeed_le_alpha` match usage in
already compiled sibling modules.  It also checked the signatures of the
primitive velocity, pressure, and sound-speed bridges and recommended no
speculative edit.

The first local build exited nonzero after 5.3 seconds at the final module of a
3,073-job target.  All decoded positivity, admissibility, sound-speed, and
guard APIs elaborated.  The only failures were five `linarith` calls inside
`abs_eigenvalues_le_signalSpeed`: after `fin_cases`, the three goals still
displayed `eigenvalues u c` rather than `u-c`, `u`, and `u+c`.  Lean also
reported the attempted `eigenvalues_zero`, `eigenvalues_one`, and
`eigenvalues_two` `simp only` arguments as unused.  The downstream two axiom
prints consequently showed `sorryAx` only because this failed build retained
open goals; no source placeholder or axiom declaration exists.

The repair replaced those three brittle simplifier calls with explicit
definitionally equal `change` statements.  The original `abs_le` and linear
arithmetic proof then applied unchanged.  The warm rerun under the same exact
local command envelope passed in 5.3 seconds wall time, with a 2.9-second
focused build and all 3,073 jobs complete.  Its four audits—decoded
admissibility, the direct state-guard bridge, the per-characteristic fixed
`alpha` bound, and the two-sided Euler-guard spectral bound—depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

The accepted theorem chain is now explicit: a successful raw guard proves
strictly positive decoded density and pressure; primitive-to-conservative
conversion is admissible; the exact conservative Jacobian has its three
characteristic values; and each absolute value is bounded by the artifact's
certified fixed `alphaReal = 7/4`.  The square root is part of the exact-real
eigensystem only.  The executable still evaluates no square root and continues
to use the already proved fixed signal-speed bound.

`RealMathematics.lean` now imports both this guard bridge and `RealStencil` in
addition to the derivative and eigenbasis modules.  Its documentation keeps
the execution boundary explicit.  The plan separates the completed exact-real
stencil from the still-open decoded numerical-error propagation task.

The integrated `Project.EulerRusanov.RealMathematics` target passed under the
same serialized local envelope in 5.3 seconds wall time, with a 2.7-second
focused build and 3,161 jobs complete.  The full `Project` root then passed in
6.3 seconds wall time, with a 3.4-second root build and 3,805 jobs complete.
The large root output was replayed existing deprecation and linter output; the
two new focused modules have no local warning in their passing builds.

A targeted source scan found no `sorry`, `admit`, or axiom declaration in
`RealGuardBridge.lean`, `RealStencil.lean`, or the amended umbrella.  No native,
C, Wasmtime, or remote-host result is used as formal evidence for these
theorems.

Refreshing the release record for the changed proof source produced
release-input SHA-256
`cc19497c194554bdddc6b8f4fc952a0a67ae2e374e11eba50f8fa89d8fbc9882`.
The draft still contains twenty-one exact packages and the expected four
blockers: immutable source revision, aggregate artifact proof for this new
input, semantic conformance, and the cold-checkout gate.  No stale receipt is
represented as current.  The intended coherent checkpoint commit message is
`Prove guarded exact-real Euler stencil`.

A final independent read-only mathematical and scope review found no theorem
blocker.  It rechecked the exact Sod fluxes, update vectors, totals, the bound
direction `|lambda_i| <= alpha`, the umbrella imports, and every WASM nonclaim.
It did identify stale prospective wording in `plans/euler-rusanov.md` and an
earlier journal design note.  That wording had promised a generic three-cell
stencil, a strict spectral bound, and generic admissibility under a symbolic
CFL condition.  The accepted checkpoint instead proves a generic two-cell,
three-interface balance, the non-strict bound `|lambda_i| <= alpha`, and
admissibility for the concrete rational quarter-step.  This entry corrects the
earlier journal wording without rewriting the chronological record, and the
detailed plan now states the implemented scope exactly.  A symbolic
CFL/invariant-domain result remains a separate unchecked follow-on only if a
future claim needs it.

The review also required the input distinction to remain visible:
`RealStencil.sodRight` uses mathematical rational `1/10`, whereas the future
compiled artifact must use the exact dyadic decoded from binary64 `0.1`.
`RealStencil.lean`, the detailed plan, and the concise notes now state that the
decoded bridge is pending.  The review ran no Lean, Git mutation, or file edit.

The pre-publication non-Lean gates passed before that wording repair:
`git diff --check`; `node tools/check-docs.js` over 90 maintained Markdown
files; `node test/artifact_release.js` over release identities, receipts, pins,
results, and blockers; `node tools/artifact-release.js audit-kernel-scope`;
final four-blocker release inspection; and the targeted no-placeholder/no-axiom
source scan.  Because the scope repair changes maintained documentation and a
Lean doc comment, the affected focused/root and documentation/release checks
are rerun below before staging.

The scope-corrected `RealStencil` target passed again in 6.7 seconds wall time
over 3,060 jobs, with a 4.4-second focused build.  The integrated mathematics
umbrella passed again in 5.3 seconds over 3,161 jobs, and the complete
`Project` root passed again in 6.2 seconds over 3,805 jobs.  All printed audits
remained standard-axiom-only, and the edited source comment introduced no
local warning.  Existing replayed dependency/project warnings remain unchanged.

Because even documentation inside a proof source is part of the frozen source
input, the release record was refreshed once more after that comment change.
The final checkpoint release-input SHA-256 is
`3d4778e8bcf2ca10731c14045af4cdfb9d389ac5603b9e1b93a74331b2beff7e`.
It supersedes the intermediate `cc19497c...` identity recorded above and keeps
the same twenty-one packages and four blockers.

Final non-Lean validation after the scope correction and final refresh passed:
`git diff --check` was silent; `node tools/check-docs.js` checked 90 maintained
Markdown files; `node test/artifact_release.js` checked release identities,
receipts, pins, results, and blockers; the kernel-scope audit passed its three
recorded roots; release inspection reproduced exactly twenty-one packages and
four blockers; and the targeted Lean-source scan returned no placeholder or
axiom declaration.  The next action is explicit staging of only the two new
Lean modules, their umbrella, the two plan files, the two note ledgers, and the
refreshed release record, followed by exact Git-data publication.

## 2026-09-04: decoded numerical stencil checkpoint

Work resumed from the clean published checkpoint
`6a26a76fe9c47026981a17e7c9d1ad44eb1b6902` on `talosfp-euler`.  The opening
`git status --short --branch` contained only the branch header and confirmed
that the local and tracking refs agreed.  No workspace cleanup, maintenance,
deletion, reset, stash, cache invalidation, worktree rewrite, or `dev`-host
probe was performed.  All delegates were restricted to read-only API or
mathematical audits; none ran Lean, Lake, Git, or a remote host.  The sole Lean
process at each build step ran locally under the pinned `LEANRUN_LOCAL=1`,
Lean 4.34.0-rc2, compatibility-preload, one-thread, explicit-wasm-tools, and
fifteen-minute-timeout envelope recorded in the operating contract.

The mathematical audit fixed the intended error accounting before source was
written.  If `e_AB = approximate_AB - exact_AB`, the left cell error is
`lambda * (e_LL - e_LR)`, the right cell error is
`lambda * (e_LR - e_RR)`, and the total-state residual against the exact
boundary balance is `lambda * (e_LL - e_RR)`.  Consequently the respective
absolute bounds are `|lambda|` times the sums of the applicable two budgets,
and the interior-interface error cancels completely from the balance
residual.  This is an exact-real assembly statement; a compiled update will
need its own rounding terms.

The input-representation audit separately derived the frozen right-pressure
value

```text
value(0x3fb999999999999a)
  = 3602879701896397 / 36028797018963968
  = 1/10 + 1/180143985094819840
  = 1/10 + f64Epsilon/40.
```

For the exact Rusanov target, that pressure bias changes the middle flux by
`[0, delta/2, -35*delta/16]`, the right boundary flux by `[0, delta, 0]`, and
the right conservative input energy by `5*delta/2`.  At `lambda = 1/4`, the
decoded-input exact step is therefore

```text
left  = [207/256, 9/80 - delta/8, 257/128 + 35*delta/64]
right = [ 81/256, 9/80 - delta/8,  95/128 + 125*delta/64].
```

These identities are deliberately distinct from both the rational
`RealStencil.sodQuarterStep` and the frozen artifact-flux assembly.

`Project.EulerRusanov.StencilNumerical` was added as a new module.  Its generic
layer defines exact decoded flux vectors, pointwise vector errors, update
budgets, a subtraction perturbation theorem, the signed one-cell identity,
two-cell componentwise propagation, and the boundary-only balance residual.
Its bridge turns the existing `Numerical.FluxRealError` record into a vector
theorem and specializes the already proved `sodLL`, `sodLR`, and `sodRR`
guard/model facts.  Its concrete layer defines decoded left and right Sod
states, proves the exact pressure decoding above, distinguishes the
decoded-input exact stencil from the exact-real assembly of the three frozen
flux rows, proves the general-ratio error theorem, specializes it to the
quarter-step half-budget, and proves the exact decoded-input quarter-step.

The first focused build reached the new module after 3,392 dependencies and
exited nonzero after 7.3 seconds wall time, with 4.8 seconds in the module.  It
reported six local proof-shape issues: two Lean metavariables inferred the
wrong ordering for `difference_perturbations`; the zero-word encoding needed
an explicit `rfl`; `PrimitiveReal` has no generated `.ext` theorem; and the
quarter-step vector budget needed an explicit function equality.  The two
large facts of interest—the exact binary64 pressure decoder and the exact
decoded quarter-step arithmetic—already elaborated.  The temporary `sorryAx`
lines in that failed build were unresolved-goal reporting only; the source
contained no placeholder or axiom declaration.

The repair supplied all perturbation arguments explicitly, completed the
zero-word equality with `rfl`, let simplification close the two record
equalities directly, and proved the budget equality by function extensionality
and ring normalization.  The second focused build again reached the module in
4.8 seconds and left only two algebraic presentation mismatches: Lean needed
the signed errors rewritten from `(a-a0)-(b-b0)` to
`(a-b)-(a0-b0)`, and the balance proof needed the two error budgets commuted.
Those exact rewrites were added; no unchanged failing command was repeated.

The third focused invocation passed all 3,393 jobs in 7.9 seconds wall time,
with a 4.0-second module build.  Its six printed axiom audits—for generic
two-cell error, boundary-only balance error, exact decimal-word decoding,
decoded-stencil error, decoded balance error, and the exact decoded quarter
step—each contain only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorry`, `admit`, or new axiom.

`Project.lean` now imports the numerical stencil module.  The complete local
`Project` build then passed all 3,806 jobs in 6.1 seconds wall time, with a
3.3-second root build.  Its long output consists of existing replayed warnings;
the new focused module emitted no warning in its successful build.

The plan checkbox for decoded flux-error propagation is complete, and the
detailed Euler plan now states the proved semantic boundary.  It does not call
`decodedTransmissiveStep` a WebAssembly stencil: the current frozen artifact
executes three scalar flux calls, while their state-update assembly here is in
Lean's mathematical reals.  The next two small proof checkpoints are (1)
transfer of the concrete `5*epsilon`, `8*epsilon`, and `13*epsilon` coarse
bounds to positive density and internal energy for both assembled cells, and
(2) a wrapper exposing the three exact decoded-artifact executions beside the
pure assembled-step theorem.  Only a later separately compiled artifact may
claim that update arithmetic itself ran in WebAssembly.

Refreshing the draft release record after the new proof source and imports
produced release-input SHA-256
`9805d168c1d68a8fb3a5f69a1143f4256d6697c7f3ceca4aada040f802a507f9`.
The record still contains exactly twenty-one artifact packages and the same
four honest blockers: immutable source revision, aggregate artifact proof for
this input, semantic conformance, and cold-checkout verification.  No stale
receipt is presented as current.  Pre-publication checks passed:
`git diff --check`; the 90-file maintained-document checker; release identity,
receipt, pin, result, and blocker tests; kernel-scope audit over its three
recorded roots; and inspection reproducing twenty-one packages and four
blockers.  The final source-placeholder scan and post-note documentation check
are repeated below before explicit staging and exact non-forced Git-data
publication.

An independent read-only review rechecked every sign and constant in the new
module.  It confirmed the two cell-error formulas, the boundary-only balance
formula, the half-budget quarter specialization, the exact binary64 pressure
bias, and all four decoded-step correction terms.  It found one documentation
inconsistency: the detailed-plan milestone checklist still marked decoded
propagation incomplete after the root plan, header, prose, and notes marked it
complete.  That checkbox was corrected before publication.  The reviewer
reported no remaining mathematical, API, or scope blocker and ran no build,
Git mutation, or file edit.

In parallel, a read-only audit selected the smallest direct compiled follow-on.
The compiler already supports repeated direct calls, flattened multi-result
calls, and at least seven `i64` result slots, so compiler expressiveness is not
the blocker.  A separate `EulerRusanovStep` case should expose a no-argument
`sodQuarterStepCheckedBits` returning status plus six conservative output
words.  It should invoke the current checked flux kernel for `LL`, `LR`, and
`RR`, require all three statuses to be zero, and update each component in the
fixed operation order `round(FR-FL)`, `round((1/4)*difference)`, then
`round(U-scaled)`.  With the frozen flux words, the expected result is:

```text
status 0000000000000000
left   3fe9e00000000000 3fbccccccccccccc 4000100000000000
right  3fd4400000000000 3fbcccccccccccce 3fe7c00000000000
```

The exact decoded-output errors against the dyadic-input ideal stencil are
`[0,-3*epsilon/64,-7*epsilon/512]` on the left and
`[0,+5*epsilon/64,-25*epsilon/512]` on the right.  Their exact decoded-real
balance error is `[0,+epsilon/32,-epsilon/16]`.  A natural binary64 residual
calculation returns positive-zero words in all three components, so publishing
those bits alone would conceal actual real rounding error.  The plan now
requires conservation evidence as a Lean exact-real theorem and permits any
runtime residual only under an explicit `roundedResidualBits` label.

The fixed artifact is high-feasibility.  Its principal medium-risk proof task
is not the new update arithmetic but reuse of the existing 335-instruction
call-free flux proof inside a different generated module.  The intended repair
is a module/function-index-parametric execution theorem specialized both to the
current standalone scalar artifact and to the future embedded helper.  This
design audit performed no edit, build, Git operation, native numerical run, or
remote-host action.

## 2026-09-04: decoded assembled-step admissibility checkpoint

Work resumed from published commit
`2a591bbc7d3bcc472bd9bdabcbdd66dd6a96c2dd` with exactly the three expected
in-progress proof paths: modified `Project.lean`, modified
`StencilNumerical.lean`, and untracked `StencilAdmissibility.lean`.  Their
contents were preserved.  Before every subsequent file mutation,
`git status --short --branch` was re-read.  No cleanup, maintenance,
reclamation, deletion, truncation, cache invalidation, reset, stash,
checkout-overwrite, worktree rewrite, or `dev`-host probe occurred.  No
unrelated path was edited.  Delegated work was read-only; the root serialized
every local Lean invocation under the exact pinned operating envelope.

The numerical module now exposes the quarter-step component budgets exactly as

```text
[5*epsilon, 7*epsilon, (25/2)*epsilon]
```

and gives a named quarter-step boundary-only balance theorem.  The new
`Project.EulerRusanov.StencilAdmissibility` module then composes those flux
budgets with the proved decimal-word representation error
`delta = epsilon/40`.  Against the rational `p = 1/10` reference step, both
assembled cells satisfy the deliberately coarse common component bounds

```text
density  <= 5*epsilon
momentum <= 8*epsilon
energy   <= 13*epsilon.
```

Those bounds imply the explicit open-set margins `rho > 5/16`,
`|momentum| < 1/8`, and `E > 1/2`.  Hence the kinetic term is below `1/40`,
internal energy is above `19/40`, pressure is above `19/100`, and both cells
are Euler-admissible.  An independent read-only arithmetic review rechecked
all correction coefficients and inequalities and found no mathematical or
scope defect.

The first focused build followed a known earlier diagnostic in
`sodQuarterErrorBudget_exact`: its three remaining scalar goals needed ring
normalization.  Adding that normalization allowed `StencilNumerical` to build
and exposed seven local proof-shape errors in the new module: two uses of the
three-point `abs_sub_le` lemma had the wrong arity, four additions needed an
orientation-independent `add_le_add` plus explicit vector-index reduction,
and the standalone momentum margin had the same addition-orientation issue.
The build exited nonzero after about 12.1 seconds; the new numerical module
itself built in 5.2 seconds.  Its printed accepted theorems already reported
only the standard axioms.  The failed downstream axiom prints contained
`sorryAx` solely because Lean reports unresolved goals that way; there was no
source `sorry`, `admit`, or axiom declaration.

The second focused build used explicit `hmain` inequalities and
`abs_add_le`.  It left only two syntactic parsing mismatches between
`(-delta) / 8` and `-(delta / 8)` in the triangle-inequality witnesses, then
exited nonzero after about 7.2 seconds.  Parenthesizing the intended negated
quotient changed no theorem or bound.  This was a materially changed proof on
each retry; no unchanged failing command was repeated.

The third focused local invocation passed all 3,394 jobs in about 7.4 seconds,
with a 4.7-second build of `StencilAdmissibility`.  Its four printed public
audits—common rational error, left margins, right margins, and joint
admissibility—depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The integrated `Project` target then passed all 3,807 jobs in about 6.3
seconds, rebuilding the root in 3.3 seconds.  The large integrated output was
existing replayed deprecation and linter output; the new focused module emitted
no warning.

This checkpoint still makes no claim that the update operations execute in
WebAssembly.  It proves admissibility of the exact-real assembly of the three
already frozen artifact flux rows.  Direct IEEE update execution remains the
separate fixed `EulerRusanovStep` artifact checkpoint.

The operating-contract audit found the repository-wide record complete in the
earlier local-only contract entry and concise notes.  To make the detailed plan
self-contained too, its verification gates now reproduce the full local Lean
command envelope, say “one global Lean/Lake/compiler process,” enumerate
`.git`, dependencies, build products, caches, evidence receipts, and partial
work as persistent user-owned state, require `git status` before every
mutation and explicit-path staging, and spell out the exact non-forced GitHub
Git-data publication and fetched-tree verification protocol.  Thus no reader
has to infer an operational rule from another file.

Refreshing the draft release record after the completed proof and umbrella
import produced release-input SHA-256
`5188ca2230e2670aa2e4d2c3ee9129c970181a428e9bb72b939ae45d3cd7f264`.
The record contains twenty-one packages and exactly the same four honest
blockers: no immutable source revision for the changed tree, no aggregate
artifact-proof receipt for that tree, pending semantic conformance, and no
cold-checkout receipt.  No earlier receipt is presented as current.

Final non-Lean gates passed concurrently: `git diff --check` was silent;
`node tools/check-docs.js` checked all 90 maintained Markdown files;
`node test/artifact_release.js` checked release identities, receipts, pins,
results, and blockers; `node tools/artifact-release.js audit-kernel-scope`
passed all three recorded roots; release inspection reproduced twenty-one
packages and four blockers; and the targeted changed-source scan found no
`sorry`, `admit`, or axiom declaration.  The next mutation is explicit staging
of only the seven reviewed paths, followed by exact non-forced Git-data
publication and local/remote tree verification.

## 2026-09-04: fixed compiled Euler step source/model checkpoint

Implementation resumed from the clean published commit
`70aae44702a970506ff1a71fee4c6f698a314060` on `talosfp-euler`.  The opening
`git status --short --branch` contained only the synchronized branch header.
Every later mutation was preceded by another status inspection.  The whole
checkout remains persistent user-owned state, including `.git`, tracked and
untracked source, ignored generated files, dependencies, `.lake` products,
caches, evidence, and partial work.  No generic maintenance, cleanup,
reclamation, pruning, cache invalidation, `git clean`, reset, stash,
checkout-overwrite, worktree rewrite, or deletion of pre-existing state was
performed.  No `dev` host exists or was invoked or probed.  All compilation,
generation, proof checking, and regression execution ran locally, with one
global Lean/Lake/compiler-family process at a time.

The durable local command envelope remains:

```sh
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  LEAN_NUM_THREADS=1 \
  WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build TARGET
```

The compatibility preload is confined to relevant Lean-family commands; it
was not passed to process inspection.  Repository Node drivers which invoke
`tools/leanrun` for their own children must instead be invoked directly under
the same environment.  In particular, `tools/talos-artifact.js`,
`tools/talos-proof.js`, and tests using `tools/run-process.js` must not be
outer-wrapped in `tools/leanrun`, because nested runner use is rejected.

`LeanExe.Examples.EulerRusanovStep` now defines a seven-word result and the
fixed no-argument `sodQuarterStepCheckedBits` entry.  It evaluates the guarded
scalar Euler flux three times for `LL`, `LR`, and `RR`, rejects with status one
and six positive-zero payloads if any call rejects, and otherwise performs six
component updates in the exact source order

```text
fluxDifference  = round(fluxRight + (-fluxLeft))
scaledDifference = round(binary64(1/4) * fluxDifference)
updated          = round(state + (-scaledDifference)).
```

Subtraction uses exact sign-bit XOR followed by the existing binary64 add
intrinsic.  The primitive right pressure is the exact word
`3fb999999999999a`, while the conservative right energy is the separately
rounded word `3fd0000000000000`; the source comments prohibit silently
identifying these with rational `1/10` and its exact-real product.  A focused
source build passed four jobs, building the new module in 417 milliseconds.
The source umbrella now imports it.

The case `euler_rusanov_step` was registered with its seven-result source
entry, generated module `EulerRusanovStep`, intended theorem
`Project.EulerRusanovStep.Spec.sodQuarterStepCheckedBits_exact`, and
`complete: false`.  The incomplete flag is deliberate: no generated-WAT
execution theorem exists yet.  The completed `Project` aggregate therefore
does not import its Spec.  The runtime aggregate does import its generated
Program and pins alloc/reset/retain/release at functions 7, 8, 9, and 10 to
the shared runtime definitions.

The artifact preparation driver was invoked directly, not through an outer
runner:

```sh
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  LEAN_NUM_THREADS=1 \
  WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  tools/talos-artifact.js prepare euler_rusanov_step
```

Before that run, the user-facing progress note incorrectly anticipated that
fresh staging would be below the system `/tmp`.  The command output and a
subsequent source audit established the actual behavior: the driver created
the fresh task-owned repository path `tmp/leanexe-talos-jqTrWD` and removed
only that same newly created staging directory when the requested outputs were
ready.  This exact correction is material and is retained here.  The
pre-existing directories `tmp/leanexe-talos-WauTHs` and
`tmp/leanexe-talos-x9h6ML` were left untouched.  No pre-existing source,
generated result, cache, dependency, evidence, or partial-work path was
deleted.  The plans and maintained workflow documentation now name this
repository-local staging behavior and prohibit treating any pre-existing
`tmp/` entry as a cleanup target.

Generation produced these exact persistent outputs:

```text
2551 bytes  proofs/talos/.generated/euler_rusanov_step/program.wasm
             SHA-256 0e4ec3be7480e0490a8637536501ba4b2adf84df66c4a4a45819b0e62d622511
25528 bytes proofs/talos/.generated/euler_rusanov_step/program.wat
             SHA-256 4daa739b85e0c115f9279fa90298a50f660d50fe47482c6c1d29938e321e8898
25302 bytes proofs/talos/lean/Project/EulerRusanovStep/Program.lean
             SHA-256 fee069ab47b6c96abc44d1b902cbcfbaa5996174517f7d7c2a215366c7d7f2bc
```

The tracked generated Program has 1,375 lines and eleven functions.  Function
0 is the embedded four-result guarded flux; function 2 is the three-argument
single-result update helper; function 6 is the no-argument, seven-result
export; and functions 7 through 10 are the runtime exports.  The exported
function calls function 0 exactly three times and function 2 exactly six
times.  The embedded flux has 22 `f64.mul`, 27 `f64.add`, and three `i64.xor`
operations.  The update helper has one multiply, two adds, and two XORs.
Consequently the complete artifact has 23 floating multiplies, 29 floating
adds, and five XORs.  These are inspected WAT/IR facts, not conclusions drawn
only from sample output.

`Project.EulerRusanovStep.Model` independently mirrors the fixed source with
Talos's pure `Wasm.IEEE64.add` and `mul` operations, reusing the already proved
LL/LR/RR scalar models.  Its kernel-checked
`sodQuarterStepCheckedBitsModel_exact` theorem proves the source-order words

```text
0000000000000000
3fe9e00000000000 3fbccccccccccccc 4000100000000000
3fd4400000000000 3fbcccccccccccce 3fe7c00000000000
```

and defines their exact reverse as Talos's top-first result stack.  The focused
model build passed 3,391 jobs in approximately 7.2 seconds wall time, with
about 4.4 seconds in the new module.  Its public theorem reports only
`propext` and `Quot.sound`.  The focused runtime-pin build then passed 3,368
jobs in approximately 10.5 seconds wall time, including about 4.4 seconds for
the generated Program and 3.5 seconds for the checks.

`test/euler_rusanov_step.js` compiles the source to WASM and WAT, dumps its IR,
executes the no-argument export under Wasmtime with seven result slots, checks
every raw result word, and pins the operation and call shape above.  Its first
invocation was mistakenly outer-wrapped in `tools/leanrun`.  The nested-runner
guard rejected it immediately with `nested tools/leanrun is not supported`;
no compilation or test execution occurred.  The invocation shape was then
corrected, not retried unchanged:

```sh
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  LEAN_NUM_THREADS=1 \
  WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  node test/euler_rusanov_step.js
```

That direct regression passed in approximately 5.56 seconds.  A later
independent read-only audit reproduced all seven words, including the one-bit
left/right momentum asymmetry, and confirmed source/model association, ABI
order, helper indices, and every operation/call count.  It found no semantic
or ABI defect and suggested pinning the exported index and total step-call
count.  The test now additionally requires exported function 6 and exactly
nine calls; the hardened direct rerun passed in 5.41 seconds.  Wasmtime remains
regression evidence only and is not substituted for the Talos execution
theorem.

`Project.EulerRusanovStep.Spec` is a deliberately minimal incomplete root.  It
defines `ExactSpecFor`: for every host environment and initial store, function
6 terminates from an empty argument stack, preserves the complete store, and
returns exactly `Model.resultValues`.  It does not declare the pending theorem.
The focused Spec target passed 3,393 jobs in 6.07 seconds wall time, building
the root in 3.4 seconds.  The updated root `LeanExe` target passed 52 jobs in
1.72 seconds wall time, building the umbrella in 1.1 seconds.  The full
completed `Project` aggregate passed 3,808 jobs in 6.32 seconds wall time,
building its root in 3.4 seconds; its long warning stream was replayed existing
deprecation/linter output.

The registry and documentation now state the exact inventory: twenty-six
registered source-driven cases, twenty-five complete cases, one incomplete
`euler_rusanov_step` case, and twenty-six tracked `Program.lean` caches.  Six
registrations use the restricted raw-bit binary64 path and five are complete.
The plans split the old combined milestone into completed compilation/model/
runtime/regression work, pending exact generated-WAT execution and theorem
transfer, and pending exact-byte/raw-data publication.  They also correct an
earlier broad output description: the selected ABI emits only status and six
updated-state words; initial states, fluxes, admissibility, and balance are
fixed inputs, intermediates, or theorem/data-certificate layers.

Refreshing the draft release record for the changed source/proof tree produced
release-input SHA-256
`1de33fb55c4181fe63c05985dcf1fb7e17b5776968d50b20f9bdd26f00564e95`.
It retains twenty-one exact-artifact packages and exactly four honest blockers:
no immutable source revision for this changed tree, no aggregate artifact
proof receipt for this input, pending semantic conformance, and no cold-checkout
receipt.  No older receipt is presented as current.

This checkpoint makes no claim that the generated step WAT has been proved,
that the 2,551 bytes form a registered exact artifact, or that verified step
data has been published.  The next proof boundary is reuse of the existing
call-free 335-instruction scalar-flux proof for embedded function 0, followed
by the small function-2 update theorem and composition of three flux calls plus
six update calls in function 6.  The current exact WAT body shape makes that
work feasible without a new compiler or floating-point semantic feature.

Pre-publication non-Lean checks then passed without mutating project inputs:
`git diff --check` was silent; `node tools/check-docs.js` checked 90 maintained
Markdown files; `node test/artifact_release.js` accepted release identities,
receipts, pins, results, and blockers; the release kernel-scope audit passed
its three recorded roots; JavaScript syntax and the 26-registered/25-complete
case inventory were checked; and the targeted changed-Lean scan found no
`sorry`, `admit`, or axiom declaration.  The intended coherent commit is
`Add fixed Euler step compiler case`.  Only the explicitly reviewed source,
generated Program, model/spec, runtime/case/test plumbing, maintained count and
operational documentation, plan/journal/devnotes, and refreshed release record
will be staged.  Ignored generated WASM/WAT, `.lake` products, pre-existing
temporary directories, dependencies, caches, and unrelated checkout state
remain untouched by Git staging and publication.

### Publication of the fixed-step source/model checkpoint

The 21 explicitly staged paths formed local tree
`ae000775b0f8985bc2691794ff64ff2838987ba4`.  Every GitHub-created blob was
required to equal its staged local blob identity, including reconstruction of
the append-only `journal.md` and `devnotes.md` values from their fetched remote
parents plus the exact staged tails.  GitHub created commit
`cb56446a6d3588f2933710d0d6cc3439cd8e322e`, message
`Add fixed Euler step compiler case`, with parent
`70aae44702a970506ff1a71fee4c6f698a314060` and that exact tree.  The
`talosfp-euler` ref accepted a non-forced fast-forward.

The published commit was fetched through the ordinary read path.  Its commit,
parent, tree, and message matched the requested values; the fetched tree, local
index tree, and worktree contents were identical.  Only then did an exact
compare-and-swap `git update-ref` advance the local branch from `70aae447` to
`cb56446`.  Final status was clean and local `HEAD`, the tracking ref, and the
GitHub branch all named `cb56446`.  No checkout, reset, merge, stash, cleanup,
file replacement, or worktree rewrite was used in publication.

## 2026-09-04: canonical operating-notes checkpoint

The user again required every operational note to be written down, committed,
and pushed.  Although the constraints were already present across the root
plan, detailed Euler plan, workflow documentation, journal, and development
notes, their distribution made a complete audit unnecessarily difficult.
This checkpoint therefore adds `plans/talosfp-euler-operations.md` as the
canonical consolidated contract and links both active plans to it.

The contract records the full checkout as persistent user-owned state,
including `.git`, tracked and untracked sources, generated and ignored files,
submodules, dependencies, build products, caches, exact artifacts, evidence,
temporary-looking paths, and partial work.  It records that the earlier
automated workspace-maintenance deletion was data loss.  Generic maintenance,
cleanup, repair, reclamation, invalidation, pruning, truncation, movement,
recursive deletion, `git clean`, destructive reset, checkout-overwrite, stash,
and worktree rewriting are prohibited.  Any destructive action against
pre-existing state requires fresh authorization naming its exact target.

It also centralizes status-before-mutation, preservation of unrelated state,
explicit reviewed staging, local-only execution with no `dev` host or probe,
direct Lean authorization through the pinned `LEANRUN_LOCAL=1` envelope, one
global Lean-family process and one Lean thread, timeout handling, preload
scope, direct invocation of runner-owning Node drivers, exact repository-local
artifact staging behavior, no self-hosted-emitter work, formal claim and axiom
discipline, detailed append-only journaling, concise development checkpoints,
frequent commits, and the exact non-forced GitHub Git-data publication and
fetched-tree verification protocol.

Before this documentation mutation, `git status --short --branch` reported a
clean `talosfp-euler` synchronized with `origin/talosfp-euler` at
`4a36794f9ca4fee9a4539d8c8c814ca680d07969`.  Only the new canonical document,
the two plan links, this append-only journal entry, and the corresponding
concise `devnotes.md` checkpoint are intended for the documentation commit.
No Lean process, remote executor, `dev` probe, artifact driver, cleanup,
deletion, cache operation, dependency operation, or worktree rewrite is part
of this checkpoint.

The first documentation gates passed: `git diff --check` was silent and
`node tools/check-docs.js` checked all 91 maintained Markdown files, including
the new canonical contract.  Command review confirmed that the pinned Lean
example is local, serialized, one-threaded, explicitly timed, and does not
outer-wrap a runner-owning Node driver.  The intended commit is
`Consolidate TalosFP Euler operating notes` and its explicit path set is
`journal.md`, `devnotes.md`, `plan.md`, `plans/euler-rusanov.md`, and
`plans/talosfp-euler-operations.md`.

An independent read-only audit made no edit, Git mutation, or Lean invocation.
It confirmed the core contract and identified edge conditions now stated
explicitly: one top-level command per status review; read-only delegation by
default; progress updates during long operations; censored-timeout semantics;
dependency and trusted-base authority; path/hash validation after recovery;
the narrow same-invocation staging-directory exception; the distinction
between an authorized atomic deliverable update and cleanup; and a terminating
publication-receipt rule.  The audit also prompted `journal.md` to be named in
the detailed plan's per-checkpoint record requirement.

Publication preparation first uploaded the new 12,002-byte operating-contract
blob and required GitHub's returned SHA
`e02f1b3fd5f8d7aeeb18f4710f528d478a5ad9dd` to equal the staged local blob.
The following batched read of the four larger staged files detected that a
requested 49,152-byte base64 chunk had been truncated by the command-output
transport (`21,848` characters returned where `40,392` were required for the
complete detailed-plan blob).  The length check stopped the operation before
any of those four blobs, a tree, a commit, or a ref update was requested.  The
exact operating-contract blob remains as an unreferenced Git object, which is
harmless and will be reused if its staged identity remains unchanged.  The
reader will use smaller 12,288-byte chunks and require every chunk length,
complete reconstructed length, and returned GitHub blob SHA to match before
tree creation.  No repository file, cache, dependency, artifact, temporary
path, index entry, local ref, or remote ref was deleted or rewritten by the
failed preparation attempt.

A second read-only reconstruction attempt reduced the shell chunk to 12,288
bytes, but its explicit length guard found another transport truncation in
`devnotes.md`: chunk five returned `5,464` base64 characters instead of the
required `16,384`.  It likewise stopped before invoking any additional GitHub
write.  The safer established route is now used for the two append-only notes:
fetch each exact parent blob through the authenticated GitHub read API, append
the small staged byte tail, upload the reconstructed UTF-8 value, and require
the returned blob SHA to equal the staged local blob.  The two roughly 30 KiB
plans will use 3,072-byte base64 chunks with an exact length check, below the
observed output boundary.  This second failed read created no blob, tree,
commit, ref update, filesystem mutation, or deletion.

The subsequent small-chunk attempt established that both preceding diagnoses
of “transport truncation” were wrong.  GNU `dd` was consuming a pipe without
`iflag=fullblock`; a single requested input block may therefore be a short
pipe read, so `skip=N` did not identify fixed byte intervals.  On the plan's
sixth requested 3,072-byte interval, the explicit guard received 1,026 bytes
(`1,368` base64 characters) rather than 3,072 bytes (`4,096` characters) and
stopped.  The correction is appended here instead of rewriting the historical
diagnostic.  Future chunk reads add `iflag=fullblock`, and every interval and
complete blob still requires an exact length and SHA match.

Before that guard fired, reconstruction from the exact remote-parent prefixes
successfully uploaded staged `devnotes.md` as
`5ceabf8062674de4e435afb996cf55be41d8279d` and the then-staged `journal.md` as
`97fe1149d5a4600b79bc421127f1d41cf406bb66`.  The journal blob became obsolete
when this correction was appended and remains only an unreferenced Git object.
No plan blob, tree, commit, branch update, filesystem mutation, or deletion
occurred in that attempt.

### Publication of the canonical operating-notes checkpoint

With `iflag=fullblock` in place, every 3,072-byte plan interval had its exact
expected base64 length.  GitHub returned the staged local blob identities for
the current journal (`e00e268da13712be8647b0c418d5a057728bd4dc`), root plan
(`83a524719bdf231d4855fba3d6b712d6349db495`), and detailed Euler plan
(`91c123e806822c7ceb43479a246e7d9452220d9a`).  Those joined the already exact
devnotes (`5ceabf8062674de4e435afb996cf55be41d8279d`) and operating-contract
(`e02f1b3fd5f8d7aeeb18f4710f528d478a5ad9dd`) blobs.

The five explicitly staged paths formed local tree
`2064098493bc9ab61db089dbb114207ae06423dc`.  GitHub created the same tree from
remote-parent tree `3a6282eb1c6fd4ffc1c0357c59aef9d711ef4577`, then created
commit `8ca721c351cd0847f1694b67205492ea5898548f`, message
`Consolidate TalosFP Euler operating notes`, with sole parent
`4a36794f9ca4fee9a4539d8c8c814ca680d07969`.  A final parent-race check still
found the remote branch at that parent, and `refs/heads/talosfp-euler` accepted
the new commit with `force: false`.

The commit was fetched through the ordinary Git read path.  Its SHA, parent,
message, and tree matched the requested values; the tracking ref named the same
commit; the fetched tree and local index were both
`2064098493bc9ab61db089dbb114207ae06423dc`; and both index-versus-fetch and
worktree-versus-index comparisons were clean.  Only then did compare-and-swap
`git update-ref` move the local branch from `4a36794` to `8ca721c`.  Final
status was clean and local `HEAD` equaled `origin/talosfp-euler`.  No checkout,
reset, merge, stash, cleanup, file replacement, cache invalidation, temporary
path removal, or worktree rewrite was used.

## 2026-09-04: exact generated-WAT execution of the fixed Euler step

Implementation resumed from the clean, synchronized documentation receipt
`021a890559c64ffea3e208b6a756929b1fbeb79f` on branch `talosfp-euler`.
`git status --short --branch` was reviewed before each top-level mutation or
build boundary.  The only source changes in this checkpoint are the scalar
flux theorem generalization, two new fixed-step execution modules, the
registered Spec wrapper, the registry/aggregate wiring, current inventory
documentation, and these append-only notes.  No pre-existing generated file,
ignored file, cache, dependency, evidence path, temporary directory, or
partial work was deleted, moved, truncated, invalidated, or replaced as
maintenance.

The existing 335-instruction scalar-flux proof was generalized to
`rusanovFluxCheckedBits_exact_in_module`.  It accepts hypotheses identifying
function zero with `Project.EulerRusanov.func0Def` and excluding an import at
that index, while retaining the old standalone
`rusanovFluxCheckedBits_exact` theorem as an exact specialization.  This is a
semantic reuse theorem about the actual generated body, not a source-level
substitution.  Its first focused build did not pass: the initial `refine`
conversion omitted the tactic bullet before `change`, so Lean reported a
layout/application failure and the incomplete diagnostic exposed `sorryAx`.
No result from that failed elaboration was accepted.  Adding the missing `·`
was the only repair.  The rerun completed 3,357 jobs; both printed axiom audits
then contained exactly `propext`, `Classical.choice`, and `Quot.sound`.

`Project.EulerRusanovStep.Spec.func2_exact` proves the generated function-two
update helper for arbitrary host environment, initial store, and three raw
`UInt64` words.  It consumes the Talos top-first stack
`[fluxRight, fluxLeft, state]`, returns the singleton pure value
`quarterUpdateComponentBits state fluxLeft fluxRight`, and preserves the
complete store.  Its focused build completed 3,393 jobs and passed.  No native
floating-point evaluator, `native_decide`, admission, or new axiom is used.

`Project.EulerRusanovStep.Spec.func0_exact` instantiates the generalized scalar
theorem inside the larger generated module.  Private LL, LR, and RR wrappers
specialize its fixed call stacks to the three pure model flux rows.  Their
accepted status facts are derived from the already proved public interface
data.  `func6_exact` then enters the actual generated function-six body,
composes the three function-zero calls with `wp_call_tw`, follows all eight
generated accepted-status `iff` decisions, composes the six function-two
calls, and proves the final top-first seven-word stack equals
`Model.resultValues`.  Every callee and the exported entry preserve the exact
initial store.  The proof was statically checked against all 85 generated
locals and the six update argument orders before its first Lean run.

The first focused `Project.EulerRusanovStep.Execution` run passed without a
proof repair: 3,394 jobs, 13 seconds reported for the target and 19.8 seconds
wall time.  Its public `func0_exact` and `func6_exact` axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`.  Lean emitted the existing
`if_pos` deprecation warnings and one unused final simp argument; the latter
was removed before the final gate.  No semantic warning or placeholder was
present.

`Project.EulerRusanovStep.Spec.sodQuarterStepCheckedBits_exact` exposes the
registered fuel-independent contract at function index six.  The registry
flag changed from `complete: false` to `complete: true`, and `Project.lean` now
imports the Spec.  A direct local `Project` build completed all 3,812 jobs;
the final target took 3.1 seconds and the complete command 23.4 seconds wall
time.  The focused source-driven gate then regenerated the fixed-step WASM,
WAT, and Talos model in a fresh repository-local staging directory, required
the generated cache to match, rebuilt the 3,395-job Spec target, and reported
`Talos proof passed: euler_rusanov_step` in 6.7 seconds wall time.

The aggregate source-driven gate was invoked directly, not outer-wrapped in
`tools/leanrun`, under the pinned local environment.  It regenerated all 26
registered cases serially, checked their Program caches, verified the registry
against runtime pins and Spec imports, rebuilt the full 3,812-job `Project`
target, and reported `Talos proof library passed: 26 completed case(s)` in
15.7 seconds wall time.  Each driver removed only the fresh staging directory
it had created.  The two pre-existing directories
`tmp/leanexe-talos-WauTHs` and `tmp/leanexe-talos-x9h6ML` remained present and
untouched after both gates.

The exact output remains the seven already modeled words:

```text
0000000000000000
3fe9e00000000000 3fbccccccccccccc 4000100000000000
3fd4400000000000 3fbcccccccccccce 3fe7c00000000000
```

This completes the source-driven exact generated-WAT boundary, not the whole
publication.  The next theorem must decode these actual rounded output words,
prove both emitted cells finite and admissible, and connect their signed error
and balance residual to the existing decoded-input stencil theorem.  Only
after that public behavior theorem is fixed should the stable 2,551-byte WASM
be migrated into an exact-artifact package, because the artifact manifest must
copy the final behavior-theorem list exactly.  Verified CSV/raw-word data and
its formal interface theorem remain a separate following checkpoint.

All Lean, compiler, verifier, and gate execution in this checkpoint was local,
globally serialized, and one-threaded.  No `dev` host was assumed, contacted,
or probed.  No cleanup, reclamation, destructive Git command, checkout, reset,
stash, worktree rewrite, or deletion of pre-existing state occurred.

After removing the unused final simp argument, the focused registered Spec was
rebuilt: 3,395 jobs passed, with 13 seconds for `Execution`, 3.1 seconds for
`Spec`, and 19.4 seconds wall time.  `node test/euler_rusanov_step.js` then
passed in 5.8 seconds, checking the exact Wasmtime words, IR operation graph,
and WAT call shape.  The source proof therefore has both formal execution and
the intended regression boundary at this checkpoint.

The release-input inventory test still carried a hard-coded count of 25 Talos
`Program.lean` caches even though the registered step had already introduced
the twenty-sixth cache at the preceding source/model checkpoint.  Its count was
corrected to 26; `node test/artifact_identity.js` passed.  This proof change
invalidated the prior draft release-input identity as expected.  A deliberate
`tools/artifact-release.js inspect` first rejected the stale release record,
then `tools/artifact-release.js refresh` wrote current digest
`432fc417d53cbf1a42519b313cc19eaca72abea4295f60996657079fc6261853`.
It did not consume prior receipts for different inputs and reports exactly four
honest blockers: no immutable source revision, no matching aggregate artifact
proof, no matching semantic conformance receipt, and no cold-checkout receipt.

The 91-file maintained-document check, release identity/receipt/pin/result/
blocker test, release inspection, whitespace check, and stale-current-count
search all pass.  Historical journal entries and their old digests remain
unchanged; current-facing documentation now distinguishes the passing 26-case
source gate from the still-pending twenty-one-package artifact receipt for the
new release input.

The optional final-review hardening added `#print axioms func2_exact`.  Its
focused rebuild completed 3,395 jobs in 6.8 seconds wall time and printed
exactly `propext`, `Classical.choice`, and `Quot.sound` for the helper; the
registered and composed theorem audits remained the same.  Because this was a
proof-source change, the preceding `432fc417...` refresh was an intermediate
identity, not a publishable final one.  A second refresh correctly produced
`de4761fc0d3b129d99dfdb239f0cec042df3962fbbf5de133c8ef11592fb1717`
with the same four blockers.  The correction is appended rather than rewriting
the chronological intermediate result.

Independent final review also found two maintained files outside the first
inventory list, plus a later Developing paragraph, that still called the
`bbc645...` receipt current.  They now label that receipt historical for its
exact earlier input and identify the current aggregate receipt as pending.
No proof or artifact claim changed; this repairs only current/historical
documentation consistency.

The root work queue carried the same combined execution/transfer item after
the detailed plan had split it.  Final review split the root item too: exact
generated-WAT execution is checked, while decoded-real transfer for the actual
rounded output remains unchecked.  This changes no implementation claim and
keeps `plan.md` authoritative about the next boundary.

A final repo-wide current/pass phrase scan found one additional stale sentence
in `docs/typetheory.md`.  It now treats the preceding aggregate artifact result
as historical and names all four current release requirements.  The scan still
distinguishes the genuinely passing 26-case source-driven aggregate from the
pending artifact-release aggregate.

Final pre-publication checks now pass with release input fixed at
`de4761fc0d3b129d99dfdb239f0cec042df3962fbbf5de133c8ef11592fb1717`:
whitespace, all 91 maintained Markdown files, release-input membership and
canonical hashing, release identities/receipts/pins/results/blockers, the three
recorded kernel-scope roots, exact 26-registered/26-complete/26-cache counts,
JavaScript syntax for the changed inventory test, and changed/new Lean scans
for `sorry`, `admit`, axiom declarations, `native_decide`, and `sorryAx`.
Release inspection reports the expected 21 packages and four blockers.  The
independent read-only checkpoint review found no remaining semantic,
integration, inventory, documentation, or publication blocker.

## 2026-09-04: fixed Euler-step checkpoint publication

At 2026-09-04T14:29:53Z the exact generated-WAT execution checkpoint was
published.  Pre-staging status contained only the reviewed 19 modified paths
and two new Lean proof paths.  `git add --` named those 21 paths explicitly;
no blanket add, cleanup, stash, reset, checkout, file move, file removal, or
workspace-maintenance operation was used.  The staged diff had no whitespace
errors and no unstaged remainder.  Its local Git tree was
`ef132bf74241ae6fbb7547af4e4ea92e8dfcb93e`.

The first parallel post-staging verification briefly made `git write-tree`
report an existing index lock while another Git query was active.  No lock or
other file was removed.  A subsequent status check showed the intended index
unchanged, and the sequential `git write-tree` retry produced the tree above.
This was transient local command contention, not a workspace repair or loss of
state.

Publication used the GitHub Git-data API.  Each of the 21 staged blobs was
uploaded and required to reproduce its local index blob SHA.  For the large
append-only journals, the remote parent blob plus the exact local appended tail
was used; the tail read used full-block semantics and the resulting GitHub blob
SHA was still required to match the local index.  A tree based on parent tree
`aaca7d5a686b5aee74cbf288e9aac663c611d4f2` reproduced the local tree SHA
exactly.  Immediately before commit and ref mutations, status was re-read and
the remote branch was required to remain at
`021a890559c64ffea3e208b6a756929b1fbeb79f`.

GitHub created commit `889560e9528302e2a98ab6c6716f9bbc77305f2c`,
`Prove exact fixed Euler step execution`, with the expected tree and sole
parent.  The `talosfp-euler` ref update was explicitly non-forcing.  An ordinary
local fetch then retrieved the commit.  Local Git verified the fetched sole
parent, message, tree, exact index equality, and exact worktree equality before
the local branch ref was compare-and-swapped from `021a890...` to `889560e...`.
Final status was clean and synchronized with `origin/talosfp-euler`.

Every operation ran locally.  No `dev` host was assumed, contacted, or probed;
no pre-existing tracked, untracked, ignored, generated, cached, dependency,
evidence, temporary, or partial file was deleted, moved, truncated, or
invalidated.  This append-only publication record is the one finite receipt
follow-on for the checkpoint; its own commit SHA is intentionally reported
after publication instead of creating a self-referential receipt chain.

## 2026-09-04: operating contract explicitly reaffirmed

At 2026-09-04T14:46:08Z the user explicitly required all operational notes to
be written down, committed, and pushed before further implementation.  The
canonical contract remains `plans/talosfp-euler-operations.md`; an immediate
non-negotiable summary was added near its beginning so the rules do not depend
on reconstructing earlier conversation or reading the chronological ledger.

The reaffirmed rules are: all work always runs locally; there is no `dev` host
and it must never be invoked, probed, discovered, assumed, or used as a
fallback; direct local Lean is authorized only through the pinned one-thread,
one-process, timeout-bounded envelope; no generic workspace maintenance is
authorized; and no pre-existing tracked, untracked, generated, ignored,
cached, build, dependency, evidence, temporary-looking, or partial state may
be deleted, moved, truncated, replaced, invalidated, pruned, reset, stashed,
or discarded.  Status precedes every mutation, changes are path-bounded,
diffs are reviewed, staging names exact paths, `journal.md` remains detailed
and append-only, `devnotes.md` remains the concise checkpoint, and coherent
checkpoints are committed and published frequently through a non-forced
GitHub fast-forward with fetched tree/content verification.

The status inspected before this notes-only mutation was synchronized at
commit `ada055bc0b9c2168b01a6b1023d3c3a3b25fb1ef` and contained exactly the
ongoing numerical implementation paths
`proofs/talos/cases.json`,
`proofs/talos/lean/Project/EulerRusanovStep/Spec.lean`, and the untracked
`proofs/talos/lean/Project/EulerRusanovStep/Numerical.lean`.  Those three
paths are preserved in place and are deliberately excluded from this
operational-notes checkpoint.  No Lean, Lake, compiler, generator, verifier,
test, cleanup, deletion, file move, cache invalidation, reset, checkout,
stash, or worktree rewrite is part of this checkpoint.

One read-only search command incorrectly put Markdown backticks inside a
double-quoted shell argument.  The local shell therefore attempted command
substitution for the literal word `dev` and printed
`/bin/bash: line 1: dev: command not found`.  It did not invoke or probe a
remote host, did not run any repository tool, and made no filesystem or Git
mutation.  The failure is recorded here rather than hidden, and shell search
patterns containing backticks will use non-interpolating quoting going
forward.

The exact intended staged paths for publication are
`plans/talosfp-euler-operations.md`, `journal.md`, and `devnotes.md` only.
Their whitespace, staged diff, blob identities, local tree, remote parent,
non-forced ref update, fetched commit, and final worktree/index equality must
be checked before the checkpoint is reported complete.

An independent read-only audit found every substantive standing rule already
present in the canonical contract, plans, journal, and developer notes.  It
identified two useful literal hardenings, which were applied: the publication
section now names the selected authenticated GitHub connector explicitly, and
the checkpoint rule now says checkpoints stay small as well as coherent,
prompt, and frequent.  The auditor changed no file, ran no build, and made no
Git mutation.

## 2026-09-04: operating-contract publication and fixed-step numerical certificate

The preceding operating-contract reaffirmation was published before further
implementation as commit
`0725a0cac73945528d3b723c2580827ce1f8bb53`, message
`Reaffirm TalosFP Euler operating contract`, tree
`eaecb95cc5982465644233329026177273262176`, with sole parent
`ada055bc0b9c2168b01a6b1023d3c3a3b25fb1ef`.  Only `devnotes.md`,
`journal.md`, and `plans/talosfp-euler-operations.md` were staged; the two
modified numerical implementation paths and new `Numerical.lean` remained
unstaged and in place.  All three final GitHub blob SHAs equaled the local
index, the API-created tree equaled `git write-tree`, the branch update used
`force: false`, an ordinary fetch retrieved the same parent/tree/message, and
the local branch moved through compare-and-swap only after the fetched tree
equaled the index and the three published worktree paths.  Local and remote
refs then both named `0725a0c` while the intended numerical work remained
dirty.

Two rejected publication attempts are part of that record.  The first
orchestration script stopped before any blob upload because its V8 isolate did
not define `atob`.  A later reconstruction of the 1,117,665-byte
`devnotes.md` from a connector raw-file response produced unmatched,
unreachable blob `e1a851e6b708dc67464139ad0ed054b5d248dc67`; no tree referred to it.
The complete local staged file was then read without a temporary file as 47
24,000-byte-or-smaller chunks, Base64-concatenated at three-byte boundaries,
and uploaded as blob `7bac101a0dc6b46a07ef871e7a238165242ce3c2`, exactly matching the index.
Nothing was deleted, repaired, reset, checked out, stashed, or rewritten in
response to either rejection.

`Project.EulerRusanovStep.Numerical` now decodes the actual six fixed result
words through the pure IEEE64 semantics and does not evaluate native Lean
`Float`.  With `epsilon = 2^-52`, it proves the exact emitted cells

```text
left  = [207/256, 9/80 - epsilon/20, 257/128]
right = [81/256, 9/80 + 3*epsilon/40, 95/128]
```

and proves all six words finite.  Against
`StencilNumerical.decodedExactTransmissiveStep (1/4)`, the exact signed errors
are

```text
left  = [0, -3*epsilon/64,  -7*epsilon/512]
right = [0,  5*epsilon/64, -25*epsilon/512]
```

The physical boundary-flux balance theorem, obtained through
`transmissiveTwoCellStep_balance` rather than by reading rounded residual
words, has exact residual `[0, epsilon/32, -epsilon/16]`.  Direct fixed-value
pressure calculations prove both decoded cells `Admissible`.  The bundled
`RealCertificate` records status zero, six finiteness facts, both exact cells,
the six signed cell identities, all three physical balance identities, and
both admissibility facts.  Its principal pure theorem is
`sodQuarterStepCheckedBitsModel_real`.

The numerical proof was developed through three explicit diagnostic stages.
Its first focused build left two pressure goals because the momentum and total
energy projection wrappers were not unfolded; the incomplete diagnostic
therefore displayed `sorryAx`, and no theorem result from that run was
accepted.  After exposing those wrappers, the next run still left the vector
index-two projections folded.  Replacing that fragile reduction with explicit
fixed rational `change` goals made the following 3,395-job build pass.  The
first `Spec` build then failed only because a qualified numerical theorem name
had been split before its dot.  Joining the identifier was the complete
repair; the next 3,399-job build passed.  These are theorem elaboration
failures and corrections, not timeouts or accepted partial proofs.

`Project.EulerRusanovStep.Spec.RealSpecFor` and registered theorem
`sodQuarterStepCheckedBits_wat_real` use `TerminatesWith.mono` on the already
proved exact function-six execution.  They therefore attach the certificate
to the same `Model.resultValues` returned by the actual generated WAT while
retaining complete store preservation.  `proofs/talos/cases.json` now lists
that theorem after `sodQuarterStepCheckedBits_exact`.  The source inventory is
26 registered cases, 26 complete, 26 `Program.lean` caches, and 38 behavior
theorem names.  The separate exact-artifact inventory deliberately remains 21
packages; no step manifest, artifact registry entry, embedded-byte proof, or
binary package was created in this checkpoint.

Two independent read-only reviews recomputed every encoding and exact value,
both error vectors, the physical balance target and residual, and the two
pressure inequalities.  They found no semantic or arithmetic defect.  One
review noted that the end-to-end error includes both nested scalar-flux and
final update arithmetic, so the module prose was tightened from “update
operations” to “complete generated fixed-step computation.”  The other noted
that positive internal energy is already derivable from the bundled
`Admissible` facts and need not be duplicated.  A separate read-only registry
audit confirmed the 37-to-38 behavior-name change and the unchanged
26/26/26/21 inventory boundary.

At the final source wording, the direct pinned local numerical build passed
3,395 jobs in 6.675 seconds wall time and the registered Spec build passed
3,399 jobs in 6.031 seconds.  Direct axiom prints for the new public numerical
theorems and `sodQuarterStepCheckedBits_wat_real` report exactly `propext`,
`Classical.choice`, and `Quot.sound`.  The focused runner-owning source gate,
invoked directly under the same environment, regenerated the step and passed
in 6.509 seconds.  The aggregate regenerated all 26 cases, built the full
3,813-job `Project`, and reported
`Talos proof library passed: 26 completed case(s)` in 17.491 seconds.  The
generated step WASM, WAT, and `Program.lean` remained unchanged.  Each driver
removed only its own fresh staging directory; the pre-existing directories
`tmp/leanexe-talos-S1boEy`, `tmp/leanexe-talos-WauTHs`, and
`tmp/leanexe-talos-x9h6ML` all remained present afterward.

The first `node test/euler_rusanov_step.js` invocation omitted
`LEANRUN_LOCAL=1`; its internal compiler runner was rejected immediately with
`Failed to connect to bus: No medium found`.  That invocation supplies no test
result and is recorded as an environment error, not a theorem or runtime
failure.  Reinvocation under the pinned local environment passed in 5.693
seconds, checking the exact Wasmtime words, compiler IR operation graph, and
generated WAT call shape.

As expected after the source and behavior-registry change, an explicit
pre-refresh `node tools/artifact-release.js inspect` rejected the old release
record with `release input identity mismatch`.  After source stabilization,
the bounded `refresh` mutation changed only the release-input identity to
`dfad5b82317c9ca0a67e6692ecb872457e6d6406cd9d6bad90e1333a29c1ec11`.
It retains 21 packages and the same four blockers: aggregate artifact proof,
semantic conformance, immutable source revision, and cold checkout.  No stale
receipt was reused.  Current-facing documentation now carries this digest;
historical journal and developer-note identities remain unchanged.

All compiler, Lean, Talos, and Wasmtime work in this checkpoint ran locally,
serially, and with one Lean thread.  No `dev` host was invoked or probed.  No
pre-existing tracked, untracked, generated, ignored, build, cache, dependency,
evidence, temporary, or partial path was deleted, moved, truncated, replaced,
invalidated, cleaned, or reclaimed.

Final pre-staging consistency gates passed.  `test/artifact_identity.js`
accepted verifier-source membership and canonical hashes;
`test/artifact_release.js` accepted release identities, receipts, pins,
results, and blockers; the kernel-scope audit accepted its three recorded
roots; release inspection reported exactly 21 packages and the four expected
blockers; all 91 maintained Markdown files passed the documentation checker;
and `git diff --check` passed.  The explicit source-policy scan found no
`sorry`, `admit`, axiom declaration, `sorryAx`, or `native_decide` in the new
or modified step theorem files.  Counts independently read 26 cases, 26
complete cases, 38 behavior names, 26 generated program caches, and 21 frozen
packages.

The final read-only pre-staging audit independently recomputed the 652-input
release digest, verified the exact 15-path dirty set and empty index, found no
duplicate case/spec/behavior names, and confirmed that no fixed-step artifact
package or registry entry had been added prematurely.  It found no substantive
defect.  Its sole wording suggestion was adopted: four documents now say
“six numeric payload words,” distinguishing them from the seventh ABI word,
the status code.

## 2026-09-04: exact-byte fixed Euler-step artifact checkpoint

The preceding fixed-step numerical certificate was published as commit
`77edac202190b41ec237210d2caba368587a9838`, message
`Certify fixed Euler step numerics`.  Before artifact migration, local and
remote `talosfp-euler` were clean and synchronized at that commit, the index
was empty, the exact-artifact registry contained 21 packages, and no
`euler_rusanov_step` package or
`Project.EulerRusanovStep.Artifact*.lean` module existed.  The stable generated
step module was 2,551 bytes with SHA-256
`0e4ec3be7480e0490a8637536501ba4b2adf84df66c4a4a45819b0e62d622511`;
its generated `Program.lean` cache had SHA-256
`fee069ab47b6c96abc44d1b902cbcfbaa5996174517f7d7c2a215366c7d7f2bc`.
The pre-existing directories `tmp/leanexe-talos-S1boEy`,
`tmp/leanexe-talos-WauTHs`, and `tmp/leanexe-talos-x9h6ML` were inventoried as
state to preserve.

After a fresh status inspection, the bounded migration ran locally and
serially under the pinned environment:

```sh
env LEANRUN_LOCAL=1 \
  LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
  LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
  LEAN_NUM_THREADS=1 \
  WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
  node tools/artifact-migrate.js migrate euler_rusanov_step
```

The driver completed in about 2.8 seconds after locally building and running
its `DumpRaw` boundary.  Its atomic publication touched exactly 11 named
deliverables: the seven new modules
`Project/EulerRusanovStep/ArtifactBytes.lean`, `ArtifactCache.lean`,
`ArtifactDecoded.lean`, `ArtifactRawCache.lean`, `ArtifactDecode.lean`,
`ArtifactValidation.lean`, and `ArtifactTranslation.lean`; package files
`proofs/artifacts/euler_rusanov_step/0e4ec3be7480e0490a8637536501ba4b2adf84df66c4a4a45819b0e62d622511/manifest.json`
and `program.wasm`; plus the reviewed `proofs/artifacts/registry.json` update
and `Project/Artifact/Binary/CheckFile.lean` dispatch update.  The generated
and frozen WASM files are byte-identical.  No `.tmp-*` or `.bak-*` residue was
left, and all three pre-existing `tmp/leanexe-talos-*` directories remained
untouched.

The schema-3 manifest has SHA-256
`ae92a42d9ed961507cccbeed8e573244aa757d3f167e10a7c20dd40950bce870`.
It records the 2,551-byte binary, validation profile `leanexe-core-v1`, proof
target `Project.EulerRusanovStep.ArtifactTranslation`, artifact theorem
`Project.EulerRusanovStep.Artifact.artifact_module_eq_cache`, no host
assumptions, and the two behavior theorems in registry order:
`Project.EulerRusanovStep.Spec.sodQuarterStepCheckedBits_exact` and
`Project.EulerRusanovStep.Spec.sodQuarterStepCheckedBits_wat_real`.  The
22-entry registry has SHA-256
`7c05e1ebaffd7fcc6e01a9fd3abf1f3b7a2b6077de972d2f048057fdc05cb237`;
the updated binary-check dispatch has SHA-256
`11bb3b70af0c2a585b53986810d48dac73514fb8628ef5093460d99f6cc971f4`.

A read-only post-migration Node inspection mistakenly resolved the manifest's
repository-relative subpath as though it were already checkout-root relative
and returned `ENOENT`.  It made no mutation and supplied no validation result;
the corrected direct file inspection established the identities above.  Two
overlapping `sed` output ranges then made one theorem header appear twice.  A
numbered source view and `rg` confirmed that exactly one declaration was
present, so no generator or proof edit was made for that display-only false
alarm.

The focused exact-artifact gate ran directly under the same pinned local
environment:

```sh
node tools/artifact-proof.js check \
  proofs/talos/.generated/euler_rusanov_step/program.wasm \
  Project.EulerRusanovStep.ArtifactTranslation
```

It exited zero after about two minutes.  Identity, all embedded bytes, binary
decode, `CoreValid` validation, the 11-function translation,
translation-cache equality, exact artifact theorem, full fixed-step `Spec`,
both registered behavior declarations, and axiom auditing all passed.  Public
behavior proofs report only `propext`, `Classical.choice`, and `Quot.sound`;
the generated decoded/cache/validation witnesses retain their expected
theorem-local `native_decide` witnesses.  Upstream deprecation and linter
warnings were non-fatal.  This focused gate used and removed only its own
fresh `tmp/leanexe-artifact-*` staging path and did not write an aggregate
receipt.

The safe non-receipt aggregate then ran as
`node tools/artifact-proof.js check-artifacts` under the same pinned local
environment.  It exited zero and reported
`Aggregate artifact theorem pass completed: 22 artifacts`, after confirming
all 22 package identities, embedded bytes, and exact artifact theorem targets.
The recovered unified runner session did not retain a single trustworthy
end-to-end wall-time measurement, so none is invented here.  It wrote ordinary
ignored Lake caches only, wrote no receipt, and left the three pre-existing
Talos temporary directories present.

The existing ignored aggregate receipt was treated as protected evidence, not
disposable generated output.  It remains byte-for-byte unchanged at
`build/evidence/artifact-proof.json`, SHA-256
`ecc17bdb8dbb65d335b072f9314c8298142f6b44224e92e1385c3b29d14ebe8f`,
with `artifactCount: 21` and historical release-input SHA-256
`bbc645be04edcae73d6d36958a01b85bfa0a24f7660fc0ccb801ac6e133711a3`.
Running `artifact-proof.js check-all` would replace that exact pre-existing
file.  Likewise, `artifact-release.js refresh` would replace tracked
`proofs/artifacts/release.json`, which remains unchanged at SHA-256
`fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1`
and still records 21 packages.  Neither replacement was inferred from
migration or validation authority.  The current 22-package release-input
identity is
`e8f96184c9b87c9e70a27f9438ec6043e7b14bfe4d15e6393f8c5d8820cff32f`
over 661 files.  Both exact replacements remain pending a fresh user
instruction naming their targets and actions.

Current-facing plans and documentation now distinguish the completed frozen
step artifact from the still-pending verified raw-state publication.  The live
inventory is 26 registered source cases, 26 complete cases, 38 source behavior
theorem names, 26 `Program.lean` caches, 22 exact artifacts, 44 package files,
154 `Artifact*.lean` modules, and 26 manifest behavior-theorem references.
Historical prose about the earlier 20- and 21-package receipts was preserved.
The release regression's package expectation changed from 21 to 22; its
release-dependent execution remains deferred until an authorized 22-package
release refresh.

The first combined documentation `apply_patch` attempt found a stale expected
context in `DEVELOPING.md`, failed its verification, and changed no file.  The
bounded patches were reapplied in reviewed batches.  A later ad hoc read-only
inventory script incorrectly expected `behaviorTheorems` directly on artifact
registry rows and stopped with a `TypeError` before producing a result.  The
corrected query read those names from each package manifest and produced the
inventory above.  These were editing/query errors, not proof or repository
failures, and neither discarded state.

The non-receipt validation set passes: `node test/artifact_identity.js`
accepted verifier membership and canonical input digests;
`node test/artifact_migrate.js` accepted transactional migration,
frozen-file identity, and the cold-cache decoder build; `node
tools/check-docs.js` checked all 91 maintained Markdown files; and `git diff
--check` passed.  The migration regression created and removed only its own
fresh `tmp/leanexe-migrate-test-*` directory.  Reinspection confirmed the same
three pre-existing Talos temp directories and unchanged protected-file hashes.

All Lean-family work remained local, globally serialized, one-threaded, and
bounded by the pinned runner environment.  No `dev` host was invoked, probed,
or assumed.  Status was inspected before each mutation.  No generic workspace
maintenance, cleanup, deletion, move, truncation, replacement, invalidation,
prune, reset, checkout, stash, worktree rewrite, or discard of pre-existing
tracked, untracked, generated, ignored, build, cache, dependency, evidence,
temporary-looking, or partial state occurred.  Staging and publication remain
future exact, reviewed mutations; no path is staged at this journal point.

### External workspace deletion after verification

Immediately before the next bounded edit, `git status --short --branch` failed
with `fatal: not a git repository`.  A read-only directory inspection showed
that the checkout root and surviving top-level files still existed but `.git`
did not.  No command in this work deleted, cleaned, moved, reset, checked out,
stashed, or otherwise rewrote that metadata.  A read-only `git ls-remote`
query for `https://github.com/jsmorph/leanexe.git` and
`refs/heads/talosfp-euler` confirmed that the remote branch remained intact at
`77edac202190b41ec237210d2caba368587a9838`.

To recover only missing Git metadata needed for the requested publication, a
narrow local recovery created the absent `.git` directory with
`git init --initial-branch=talosfp-euler .`, added the known public `origin`,
fetched only `refs/heads/talosfp-euler`, and created the local branch ref at the
exact fetched commit with compare-and-swap from the zero ref.  The newly
initialized index was empty, which initially displayed every remote file as an
index deletion plus its surviving top-level copy as untracked.  A
`git read-tree 77edac202190b41ec237210d2caba368587a9838` invocation populated only the index from the
exact remote tree; it did not write, remove, or overwrite a worktree file.

That comparison exposed the full extent of the external event: 6,278 tracked
worktree paths are absent.  The missing paths include the pre-existing
`build/evidence/artifact-proof.json`, tracked
`proofs/artifacts/release.json`, the modified artifact registry and
conformance file, all newly generated fixed-step artifact modules, and the
unpublished content-addressed WASM package.  They were present and hashed in
the preceding paragraphs before this event, then disappeared without a
command from this work.  The recovered index still contains every parent-tree
path and therefore shows these losses only as unstaged worktree deletions;
zero deletions are staged.

The external deletion also removed `test/artifact_release.js`, including the
uncommitted 21-to-22 expectation edit.  This appends a correction to the
earlier current-checkpoint sentence: that test edit is no longer present and
will not be included in the notes-only recovery checkpoint; the recovered
index retains the parent commit's 21-package test.  The verified artifact
payload cannot be honestly published from the surviving files, and no missing
path is silently regenerated, restored, or fabricated.

The safe recovery checkpoint therefore contains only this detailed journal
and the matching concise developer note.  Its tree is constructed from the
intact remote parent tree plus those two reviewed blobs, so it preserves every
remote file and records no deletion.  Surviving but unpublished edits to
`README.md`, `DEVELOPING.md`, and `plan.md` remain unstaged and untouched.
Restoring the 6,278 missing worktree paths or regenerating the exact artifact
requires a separate explicit recovery decision; neither is inferred from the
authority to record and publish these operational notes.

## 2026-09-07: ARM Mac recovery and local execution setup

The user requested a fresh clone under `~/src`, then authorized proceeding
with the complete Euler agenda: local setup, fixed-step artifact recovery,
raw data publication, and the later checked 100-cell Sod solver.  The fresh
checkout is `/Users/jamiestephens/src/leanexe` on `talosfp-euler`, with parent
`d597fc4c9f60d803498d5d21cf138b148cae0ac3` and an initially clean synchronized
worktree.  This is a new checkout; no old checkout or cached state was removed
or rewritten.  The remote contains 26 complete source cases and 21 artifact
packages.  The step's tracked Program cache SHA-256 is still
`fee069ab47b6c96abc44d1b902cbcfbaa5996174517f7d7c2a215366c7d7f2bc`.
The uncommitted 22nd package described in the previous notes is absent.

The new host is Darwin arm64.  Read-only prerequisite inspection found the old
Linux toolchain, x86-64 preload, and Linux wasm-tools paths absent, and only
older Lean toolchains installed elsewhere.  Global Node is v26.7.0 rather than
the pinned v24.13.0.  `tools/bootstrap-macos.sh` now installs the existing
project versions in fresh `build/tools` paths, without modifying the user's
Elan, Node, or Homebrew installations.  `gh api` release metadata supplied
SHA-256 digests for the official Lean 4.34.0-rc2 ARM Mac tarball, wasm-tools
1.251.0, and Wasmtime 44.0.0 CLI/C API; Node's official SHASUMS256.txt supplied
its v24.13.0 ARM Mac digest.  Each archive was downloaded with a bounded curl
command, verified, and extracted into an absent path.  Exact archive digests
are checked into the bootstrap script.  The bootstrap passed for all five
archives.  `file` inspection confirms native ARM Mac executables.

`tools/macos-env.sh` records replacement paths for LEANRUN_TOOLCHAIN,
LEAN_SYSROOT, WASM_TOOLS, WASMTIME, WASMTIME_C_API, and pinned Node PATH.
The Linux `/proc` compatibility preload is neither loaded nor required on
Darwin.  No alternate Lean or wasm-tools version has been substituted.  The
local runner gains a Darwin-only C resource wrapper using the native flock
system call on the same shared lock file, one inherited Lean thread, nice
priority, process-group signal forwarding, and an explicit monotonic deadline.
It requires LEANRUN_LOCAL=1 and reports the absence of cgroup and ionice
controls.  Linux execution remains on the existing runner path.  Fresh helper
build directories are retained rather than cleaned.  The Wasmtime host build
now recognizes ARM macOS and its dylib.  No compiler or proof command has run
at this journal point; local runner and host checks precede proof recovery.

Status was inspected before each edit and installation boundary.  Bounded
tracked changes so far are the bootstrap/environment scripts, runner/C helper,
Wasmtime host build, focused runner regressions, test registration, and this
append-only journal.  Read-only searches for a few guessed tool filenames
returned ENOENT; no command from those searches executed.  No remote execution,
cleanup, cache invalidation, reset, stash, or deletion of pre-existing state
occurred.

### Local setup validation and priority boundary

The first `node test/leanrun_local.js` stopped before its dummy target because
Darwin's sandbox rejected `setpriority` with Operation not permitted; the
subsequent lock test likewise did not reach its fixture.  A read-only priority
query through Node reports inherited nice value zero.  `/usr/bin/nice -n 10
/usr/bin/true` independently reported the same sandbox rejection, and `ps`
inspection was also denied.  These are resource-control failures, not Lean
proof failures.  A user approval question is pending for inherited priority
on this host.  No actual Lean, Lake, or compiler command has been attempted.

The runner now supports an explicit LEANRUN_INHERIT_PRIORITY=1 opt-in, disabled
by default and absent from macos-env.sh.  Its behavior was tested only on
Node fixture processes: both `env LEANRUN_INHERIT_PRIORITY=1 node
test/leanrun_local.js` and the Darwin-specific `test/leanrun_macos.js` pass.
Checks cover ordinary exit codes, environment propagation, nesting rejection,
strict standard-mode rejection, lock exclusion and waiting, bounded timeout,
descendant termination, signal forwarding, and lock release.  These fixture
checks do not authorize or substitute for proof execution.  The helper is
compiled with C11, -Wall -Wextra -Werror, and no third-party library.

Pinned Node and wasm-tools version checks pass.  `tools/build-wasmtime-host.sh`
built the ARM Mac C host with Wasmtime 44.0.0.  `node
test/euler_rusanov_interface.js` reproduced all eight existing interface rows
from the registered frozen binary and accepted CSV, manifest, and identity
checks.  `node test/wasm_tools_version.js` and `node test/run_process.js` pass,
including malformed-version rejection and process-routing/signal tests.
`git diff --check` passes.  Actual Lean and wasm-tools binary SHA-256 values
are respectively
`1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`
and `3b30448f3dda6a381aa2de7f401f7e635ceb90ebe0f168ad9cedd052e114ad3e`.

All eleven Git dependencies in the proof lake-manifest were fetched into
absent `proofs/talos/lean/.lake/packages/<name>` directories using `git init`,
a pinned-depth fetch, and an initial detached checkout of that exact fetched
commit.  No pre-existing dependency directory was reused or replaced.  A
subsequent comparison of every HEAD to its manifest revision passed, including
CodeLib 87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47 and Mathlib
85e3a25e006c35636f0e53b0e9296caca2685bc0.  No Lean process was needed for these
source-only fetches.  The existing build/cache state is retained.

The setup checkpoint's reviewed staging intent is exactly DEVELOPING.md,
devnotes.md, journal.md, plans/talosfp-euler-operations.md,
test/leanrun_local.js, test/leanrun_macos.js, test/run_all.js,
tools/bootstrap-macos.sh, tools/build-wasmtime-host.sh, tools/leanrun,
tools/leanrun-macos.c, and tools/macos-env.sh.  The fixture regressions above,
91-file documentation check, and whitespace check pass; actual Lean validation
remains pending the priority exception.  No generated binaries, archives,
dependency checkouts, caches, data replacements, or release receipts are staged.
Publication will use gh's authenticated Git-data API, exact index blobs/tree,
a sole current-remote parent, a non-forced ref update, and fetched tree/content
verification before compare-and-swap advancement of the local branch.  Actual
publication identities will be recorded in one bounded follow-up receipt.

### ARM Mac setup publication receipt

The reviewed twelve-path setup checkpoint was published as
`030a433688380534d2db62c2ab0e6bdb18d86693`, message
`Support pinned ARM Mac local tooling`, with sole parent
`d597fc4c9f60d803498d5d21cf138b148cae0ac3` and exact tree
`4aea36274a2e950e13145abeee4e167c1ff3ffc8`.  Every uploaded Git blob matched
its staged index identity.  The Git-data API tree matched `git write-tree`,
and the branch update used force:false.  A fetch with auto-maintenance disabled
confirmed the commit, tree, sole parent, message, index, and worktree equality
before the local branch advanced by exact compare-and-swap.  Final status was
clean and synchronized.  This is the single receipt follow-up for the setup
checkpoint; only journal.md and devnotes.md are staged for it.  Its own identity
is verified externally, with no recursive receipt chain.

## 2026-09-07: approved local priority exception and proof recovery

The preceding setup receipt was published and verified as
`a140f027eeef3f4f556de06d40659efd0a3192cc`, sole parent
`030a433688380534d2db62c2ab0e6bdb18d86693`, tree
`032522d87994ddf6d2463e96a5e9124f52960165`; status was clean and synchronized.
The user has now answered the pending question with “Nice is approved.”  This
approves the proposed inherited-priority fallback when the sandbox rejects
nice, while retaining the shared lock, one Lean thread, and explicit timeout.
The approval is recorded in the branch operating contract and enabled by
`tools/macos-env.sh`; no further approval is needed for this same exception.

The reviewed next commands select the previously hashed repository-local ARM
Mac tools and run `tools/leanrun --timeout 30s lean --version`, followed by the
bounded root compiler build `tools/leanrun --timeout 15m lake --no-ansi build
lean-wasm LeanExe.Examples.EulerRusanovStep`.  Ordinary root `.lake` build
outputs are in scope and all earlier helper caches and downloads are retained.
No Linux preload, alternate toolchain, or remote executor is involved.

The first actual Lean invocation passed: 4.34.0-rc2, arm64-apple-darwin24.6.0,
commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release.  The local runner
reported the approved inherited-priority fallback.  Root compiler and fixed-step
source build is progressing with a single runner slot; initial warnings are
existing deprecated if_true/if_false names.

The absent CodeLib `.lake/packages` path is now a relative symlink to the
already pinned parent package tree (`../..` from CodeLib/.lake), following the
dependency's shared-package layout.  No second dependency versions are selected
and no existing path was replaced.  MATHLIB_CACHE_DIR is set explicitly to
`build/cache/mathlib` so the upcoming pinned cache fetch writes only within this
checkout, not the user's home cache.  After the compiler finishes, the next
bounded command is `tools/leanrun --timeout 15m lake -d proofs/talos/lean exe
cache get`; it will materialize matching Mathlib build products and retains
existing local state.

### Successful compiler, cache, and exact step regeneration

The root compiler plus fixed-step source build passed (60 jobs).  The pinned
Mathlib cache tool built (27 jobs), downloaded and decompressed all 8,747
requested files from the official cache for the pinned checkout, and exited
successfully.  The fresh shared dependency layout was retained unchanged.

`tools/talos-artifact.js prepare euler_rusanov_step` passed locally.  The pinned
Talos verifier build completed 53 jobs, including a 146-second native C compile
of Verifier.Emit; the compiler/source stage replayed the passing 60-job build.
The driver used only its own fresh `tmp/leanexe-talos-9cBXOu` staging path and
removed that path internally after success.  The new `.generated` step WASM
is exactly 2,551 bytes with SHA-256
`0e4ec3be7480e0490a8637536501ba4b2adf84df66c4a4a45819b0e62d622511`.
The tracked Program.lean was byte-identical, retaining SHA-256
`fee069ab47b6c96abc44d1b902cbcfbaa5996174517f7d7c2a215366c7d7f2bc`.
This recovers the precise artifact-producing inputs recorded before the prior
workspace loss, across Linux x86-64 and native ARM Mac execution.

The next reviewed mutation is `node tools/artifact-migrate.js migrate
euler_rusanov_step`: create the seven missing artifact modules and the
content-addressed WASM/manifest package, and update only the artifact registry
and binary-check dispatch needed to register it.  The user-authorized recovery
covers those named step deliverables.  Existing artifact packages and release
receipts are preserved; focused verification will follow migration.

A future raw-data generator draft remains outside the checkout in the current
task's work directory.  Its independent BigInt rational model reconstructs
conservative states and three Rusanov fluxes from exact decoded inputs.  It
matches all six signed cell errors and residuals
`[0, 1/144115188075855872, -1/72057594037927936]` for the recorded step words.
One draft had a corrected malformed hex literal, and the first ad hoc Node
module loader omitted its filename and failed relative-import resolution;
the corrected pinned-Node invocation passes.  These were draft-only failures,
not artifact or theorem failures, and no data publication is claimed yet.

### Exact-artifact recovery gates

The scoped migration passed its seven-job raw decoder build and recovered the
seven EulerRusanovStep artifact modules, frozen binary and manifest, registry
entry, and embedded-byte dispatch.  The manifest SHA-256 is
ae92a42d9ed961507cccbeed8e573244aa757d3f167e10a7c20dd40950bce870,
matching the pre-loss record.  Its host-assumption list is empty; the verifier
source digest remains
bf03d3f47fb11563c947224601a21afa95c62fc88df81f493de821e69de9d1e7.

The focused command tools/artifact-proof.js check
proofs/talos/.generated/euler_rusanov_step/program.wasm
Project.EulerRusanovStep.ArtifactTranslation passed.  The separated shared
Talos build completed 3,346 jobs, then exact embedded-byte equality, decoding,
validation, CoreValid, and translation equality all passed.  The behavior
closure completed 3,399 jobs and all manifest declaration checks passed.
Both public execution/numerical theorems, sodQuarterStepCheckedBits_exact and
sodQuarterStepCheckedBits_wat_real, report only propext, Classical.choice, and
Quot.sound.  The generated exact-artifact witnesses retain the existing
native_decide policy; no changed proof introduces an admission or new axiom.

The focused Node regression test/euler_rusanov_step.js passed runtime raw words,
IR operations, and exact WAT call shape.  test/artifact_migrate.js passed
transactional migration, frozen identity, and cold-cache decoder checks;
test/artifact_identity.js passed.  tools/check-docs.js accepts 91 maintained
Markdown files, and git diff --check passes.  Existing dependency deprecation
and unused-variable warnings remain nonfatal.

The registry now has 22 packages; the source registry remains 26 complete
cases and 38 behavior names.  Current-facing inventories were updated in
README.md, DEVELOPING.md, docs/status.md, docs/artifact-format.md, plan.md,
plans/euler-rusanov.md, and proofs/talos/README.md.  Historical 21-package
receipts and release drafts are preserved, with no current-release claim.
The bounded aggregate tools/artifact-proof.js check-artifacts is running
serially; its fresh retained log is
tmp/euler-recovery-20260907/artifact-aggregate.log.  It checks the changed
22-package registry boundary and does not refresh a release receipt.

The aggregate check-artifacts command exited zero and reported
"Aggregate artifact theorem pass completed: 22 artifacts".  Every frozen
identity, embedded-byte comparison, and artifact theorem passed.  The final
91-file documentation, artifact identity, and whitespace checks also pass.
This aggregate covers artifacts; the new step's behavior and axiom gates were
checked separately above.  No old release receipt was modified.

During independent preparation of the next phase, one read-only lookup used
the wrong CodeLib source prefix and was corrected after rg --files located
the codelib subdirectory.  A scratch compiler-patch script initially had
unescaped Lean quotation backticks in a JS template and ran with the host
Node26 default; it failed before writing previews.  After correcting the
quoting and sourcing pinned Node24, it produced 14 preview files outside
the checkout.  A separate verifier-preview script initially assumed a test
used rfl rather than simp; its unique-anchor check failed before output, then
the corrected script produced 12 preview files.  Three primitive proof drafts
also remain outside the checkout.  None of those future drafts is installed,
compiled, staged, or represented as a completed solver change.  The proposed
conservative-state guard domain was raised with the user for design discussion.

The exact reviewed recovery staging list is DEVELOPING.md, README.md,
devnotes.md, docs/artifact-format.md, docs/status.md, journal.md, plan.md,
plans/euler-rusanov.md, plans/talosfp-euler-operations.md,
proofs/artifacts/registry.json, proofs/talos/README.md,
proofs/talos/lean/Project/Artifact/Binary/CheckFile.lean, tools/macos-env.sh,
the seven Project/EulerRusanovStep/Artifact*.lean modules, and manifest.json
plus program.wasm under the step's frozen SHA-256 directory.  Publication uses
exact index blobs, tree equality, a sole current remote parent, force:false,
and fetch-side commit/parent/message/tree/index/worktree checks before the
local compare-and-swap ref update.  Actual identities will be recorded in the
next substantive data checkpoint rather than a recursive receipt chain.

## 2026-09-07: fixed-step raw-data certificate

The recovery checkpoint was published as
fc50beb78bae6e387c5aa9a8245dd6939cb984c1, sole parent
a140f027eeef3f4f556de06d40659efd0a3192cc, tree
93705d36a764f63e8cf2dce5c78f71d7106b452a, with message
"Recover and verify exact Euler quarter-step artifact".  All 22 explicitly
staged paths matched their uploaded Git blobs, the API tree matched the index,
the remote ref advanced with force:false, and fetch-side commit, parent,
message, tree, index, and worktree equality checks passed before the local
compare-and-swap update.  Status was clean and synchronized.

The next bounded edit installs the reviewed new StepData.lean theorem,
tools/euler-rusanov-step-data.js generator, and focused regression
test/euler_rusanov_step_data.js from task-local drafts.  Project.lean imports
the dataset theorem and test/run_all.js includes the focused regression; the
full run_all command is not invoked because it includes the prohibited
self-hosted emitter.  No frozen binary or manifest is changed.  The data
writer creates only absent files and refuses differing existing data.
The next focused Lean build targets Project.EulerRusanovStep.StepData under
the existing local runner, one thread, and a 15-minute timeout; its fresh
retained log is tmp/euler-recovery-20260907/step-data-proof.log.

The StepData target passed on its first invocation, completing 3,407 jobs
with the new module taking 3.4 seconds.  model_words_published uses propext
and Quot.sound; stepV1_generated uses propext, Classical.choice, and Quot.sound.
artifact_stepV1 additionally carries precisely the three existing artifact
native-decision witnesses for decoded existence, decoded/cache equality, and
validation.  This is the existing artifact gate policy, not a new execution
or numerical axiom.  The proof specializes the fixed model theorem and uses
artifact_correct_of; no duplicated instruction trace or manual numeric proof
was needed.

The reviewed data writer created five absent files under
data/euler-rusanov-step-v1, followed by its README.  The focused Node regression
passed exact runtime words, all six independently computed rational signed
errors, both decoded positive pressures, exact balance residuals, signed-zero
and subnormal decoding, nonfinite rejection, all seven adjacent-word mutation
rejections, canonical CSV rows, and manifest checks.  Raw CSV SHA-256 is
d952ba579c4184acde0288e36a62726d46d2225068d4491b0f641191de92c74d;
the generator source SHA-256 is
967ed7cd7c57b71da45b8580265656a51661e6d6df77cf77702301c4457a1b9b.

Visual review first encountered the browser's local-file URL policy; no browser
workaround was attempted.  view_image cannot read SVG, and native qlmanage
failed sandbox initialization.  A materially safer static-file conversion
used the already bundled Sharp package, under pinned Node24, solely to create
a review PNG outside the checkout.  The resulting plot was visually inspected:
all three panels, axes, legends, title, parameters, and claim boundary are
legible and unclipped.  Sharp is not a repository dependency or dataset
generator input; the published SVG is generated by the pinned Node script.

README.md had a second current-inventory paragraph still saying 21 packages;
this checkpoint corrects it to 22.  README.md, DEVELOPING.md, docs/status.md,
plan.md, plans/euler-rusanov.md, and proofs/talos/README.md now distinguish the
completed fixed-step dataset from the pending full runner.

The final 91-file maintained documentation check, dedicated dataset README
link check, and whitespace check pass.  The reviewed data checkpoint stages
DEVELOPING.md, README.md, devnotes.md, docs/status.md, journal.md, plan.md,
plans/euler-rusanov.md, proofs/talos/README.md, proofs/talos/lean/Project.lean,
proofs/talos/lean/Project/EulerRusanovStep/StepData.lean, test/run_all.js,
test/euler_rusanov_step_data.js, tools/euler-rusanov-step-data.js, and exactly
README.md, cell-averages.svg, euler-rusanov-step-v1.csv, exact-comparison.csv,
manifest.json, and presentation.csv under data/euler-rusanov-step-v1.
The exact-tree non-forced publication protocol and fetch-side verification
remain unchanged.  No build log, static-review PNG, or FP extension draft is
staged.

## 2026-09-07: source-profile subtraction, division, and square root

The data checkpoint was published as fd1782ae720016cec2fc6fc3ec33d02da44f5b94,
sole parent fc50beb78bae6e387c5aa9a8245dd6939cb984c1, exact tree
f70971bbbd9ec461eb6ada623c85ae39f87133e6, with message
"Certify and publish fixed Euler step data".  Uploaded blob/index and API tree
equality, force:false ref advancement, fetched commit/parent/message/tree,
index/worktree equality, and local compare-and-swap all passed.  Status was
clean and synchronized.

The next bounded checkpoint installs only the reviewed 14-file compiler
preview and three new primitive proof drafts, plus three incomplete source
registrations.  The compiler paths are:
- LeanExe/Examples/Float64Bits.lean
- LeanExe/Extract/Core.lean
- LeanExe/Extract/Eval.lean
- LeanExe/Extract/OwnershipReport.lean
- LeanExe/Extract/Types.lean
- LeanExe/Extract/Values.lean
- LeanExe/Float64.lean
- LeanExe/IR/Core.lean
- LeanExe/Wasm/Binary.lean
- LeanExe/Wasm/Image/Emit.lean
- LeanExe/Wasm/Image.lean
- LeanExe/Wasm/Instr.lean
- LeanExe/Wasm/ScalarDescriptor.lean
- LeanExe/Wasm/Wat.lean
The new spec paths are Project/F64SubBits/Spec.lean,
Project/F64DivBits/Spec.lean, and Project/F64SqrtBits/Spec.lean beneath the
proof workspace.  The source registry is proofs/talos/cases.json.

Subtraction and division extend U64Op.  Square root has its own unary raw-word
IR expression; every liveness, ownership, evaluation, call-shift, scratch-size,
and native emission traversal follows its sole operand.  The production
serializer and WAT printer share the added instructions.  The experimental
image encoder keeps them rejected and will not be executed.  Native Float
remains a regression oracle; the proof drafts use pinned Talos IEEE64
semantics and existing numerical bounds.  No dependency or trusted axiom is
added.  The separate verifier-profile preview is not installed yet, keeping
all 22 frozen package manifests valid during this source-only checkpoint.

Next is the bounded compiler and Float64Bits build, then generation and
focused checking of the three new primitive caches/specs.  All work is local,
serial, one-threaded, and timed through the approved runner envelope.

The extended root compiler/source build passed all 59 jobs.  The new
test/f64_extended_bits.js passed four compiled entries, exact WAT and binary
opcode sequences, report/IR intrinsic boundaries, nested unary traversal,
and 37 raw-word vectors covering signed zero, adjacent inputs, subnormals,
rounding ties, overflow, infinities, and NaN classes.  Every regression run
uses a fresh retained tmp/f64-extended-* output directory.

The three prepare commands passed, using only their own fresh staging paths
leanexe-talos-WbTKQM (sub), leanexe-talos-dAzDw9 (div), and
leanexe-talos-xCeoka (sqrt), internally removed after successful generation.
Each new Program.lean was generated by the pinned verifier, not edited by hand.
The direct focused build of Project.F64SubBits.Spec, Project.F64DivBits.Spec,
and Project.F64SqrtBits.Spec passed on the first attempt (3,359 jobs); each
new spec took about 3.7–3.8 seconds.  All nine printed public exact-execution,
source numerical, and WAT numerical theorems use only propext, Classical.choice,
and Quot.sound.  The short shared wp_run proof handles all raw input words;
existing Talos numerical lemmas discharge the explicitly stated finite-domain
premises.  No extra primitive execution scaffold was necessary.

The three source cases are now marked complete and imported by Project.lean,
and the extended regression is registered in test/run_all.js.  Next is the
full source-driven 29-case gate to verify preserved cases against the changed
compiler.  This gate excludes self-hosted emission.  Its fresh retained log is
tmp/euler-recovery-20260907/fp-source-aggregate.log.

Two exploratory read-only queries guessed absent Wasm.lean and
Representation.lean paths; the first was corrected with rg --files locating
Execution.lean, and neither changed state.  A later absent docs/language.md
lookup was corrected to the existing docs/spec.md authority.  The user asked
to view the SVG, then requested PNG when it did not display.  The previously
reviewed static PNG was copied exclusively to the task outputs directory as
euler-two-cell-step.png and shown inline; no dataset source or SVG was changed.

The first 29-case aggregate invocation failed in preflight before starting
Lean: Project.Runtime.Checks lacked the three new Program imports.  The
correction adds those imports and all twelve alloc/reset/retain/release
equalities against the existing shared runtime definitions, erasing only the
module-local type index as in every prior case.  The generated functions are
at indices 1 through 4 in each new module.  This is a registry-integration
failure, not a theorem diagnostic or timeout.  The corrected aggregate uses
a separate retained log fp-source-aggregate-runtime-pins.log.

### Source FP documentation review and requested SVG link

Reviewed and corrected the source proof inventory to 29 cases, preserving the
historical 26-case gate date.  Joined the three new primitive rows to the
existing theorem table and synchronized the Euler plan and concise devnotes.
The 29-case aggregate continues through the cold existing proof closure; no
second Lean-family command ran alongside it.

The user reinforced frequent progress updates and incremental commits/pushes,
then asked to publish the SVG.  It was already included in fd1782ae720016cec2fc6fc3ec33d02da44f5b94.
A first read-only gh API lookup was rejected by zsh because its query URL was
unquoted (no request executed); the quoted lookup succeeded.  GitHub reports
the exact local blob 6f2174a27e007446aafd1f4508a068245423c7c3, 3,675 bytes, for
data/euler-rusanov-step-v1/cell-averages.svg.  Returned the immutable commit
link immediately; no duplicate publication or source mutation was needed.

Review found that the legacy test/f64_bits.js gate calls compile-image and
removes its named image output.  Neither action was executed.  Added the
explicit --native-only mode, which runs the existing arithmetic, lowering,
WAT/binary, and annotation assertions in a fresh retained tmp/f64-native-*
directory and skips image rejection entirely.  Default behavior remains the
existing full test.  This bounded test edit enables the authorized legacy
regression without an experimental emitter or pre-existing output deletion.

### Source arithmetic recovery checkpoint publication intent

The 29-case generator check passes every current source/cache comparison.
The aggregate Project build remains active while existing CLOB dependencies
compile cold on this Mac.  The focused new proofs, compiler build, and 37
extended runtime vectors have passed; the complete source aggregate and the
new native-only mode execution remain pending and are not claimed as passing.
All 91 maintained documentation checks, three additional primitive README
link checks, JS syntax checks, and whitespace checks pass.  The generated
Program.lean SHA-256 values are sub ae560f25cebdff7689a226dc83f24ab164761f22d11d651413e3b2f1e9997a6a,
div b2b151c897ea273ec1448dadc8432455457be431f07b21e564efe28286c55d48,
and sqrt 77e5a9274f768199b4e8e06c45657209b869a5028c144c5e5e7f96ecac1262d0.

To honor the user's request for frequent incremental publication, publish
this proved primitive checkpoint now with the remaining aggregate explicitly
pending.  The active build writes only ignored build outputs at this stage;
no tracked mutation or second Lean process is introduced during publication.
The unchanged verifier and all 22 frozen packages retain their published
identities.  A future 140-line generic finite/classification/order proof draft
is retained outside the checkout and is not claimed as checked.  Two
read-only discovery errors for absent Basic.lean and an interface-data tool
were corrected via rg --files; no state changed.

The exact reviewed staging set is:

- DEVELOPING.md
- LeanExe/Examples/Float64Bits.lean
- LeanExe/Extract/Core.lean
- LeanExe/Extract/Eval.lean
- LeanExe/Extract/OwnershipReport.lean
- LeanExe/Extract/Types.lean
- LeanExe/Extract/Values.lean
- LeanExe/Float64.lean
- LeanExe/IR/Core.lean
- LeanExe/Wasm/Binary.lean
- LeanExe/Wasm/Image.lean
- LeanExe/Wasm/Image/Emit.lean
- LeanExe/Wasm/Instr.lean
- LeanExe/Wasm/ScalarDescriptor.lean
- LeanExe/Wasm/Wat.lean
- README.md
- devnotes.md
- docs/spec.md
- docs/status.md
- docs/typetheory.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/README.md
- proofs/talos/cases.json
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/Runtime/Checks.lean
- test/f64_bits.js
- test/run_all.js
- test/f64_extended_bits.js
- proofs/talos/lean/Project/F64SubBits/Program.lean
- proofs/talos/lean/Project/F64SubBits/Spec.lean
- proofs/talos/lean/Project/F64SubBits/README.md
- proofs/talos/lean/Project/F64DivBits/Program.lean
- proofs/talos/lean/Project/F64DivBits/Spec.lean
- proofs/talos/lean/Project/F64DivBits/README.md
- proofs/talos/lean/Project/F64SqrtBits/Program.lean
- proofs/talos/lean/Project/F64SqrtBits/Spec.lean
- proofs/talos/lean/Project/F64SqrtBits/README.md

The intended commit is "Prove raw binary64 subtraction division and square root",
sole parent fd1782ae720016cec2fc6fc3ec33d02da44f5b94.  Use exact Git-data blob/tree
comparison, a non-forced ref advance, fetch validation, and local CAS.  Record
the resulting identities and the aggregate outcome in the next substantive
checkpoint.

## 2026-09-07: independent binary profile extension

The source arithmetic recovery checkpoint is published as
ab57101a17bc6b150b5abedc66a1c537571b4a80, sole parent
fd1782ae720016cec2fc6fc3ec33d02da44f5b94, tree a7c2a6e29d9784844ba20ccdea7eaa652cbe46ca.
Exact staged blob/API tree equality, force:false advancement, fetch-side
commit/parent/message/tree checks, index/worktree equality, and local CAS
passed.  The checkout was clean and synchronized.

The active source aggregate later hit its explicit 20-minute build limit
(exit 124), without a theorem diagnostic, after progressing to 3,600 of the
3,827 discovered jobs.  All 29 generated models had passed comparison, the new
runtime pins and three new specs passed, and existing CLOB dependencies were
still being compiled.  The complete source aggregate remains pending; do not
repeat unchanged Project.  Build smaller missing source-spec dependencies
before retrying.  The full retained log is fp-source-aggregate-runtime-pins.log.

After that process ended, serialized local regressions passed:
node test/f64_bits.js --native-only (fresh retained outputs; no image command),
node test/f64_dot.js, node test/euler_rusanov.js, and
node test/euler_rusanov_step.js.  Their fresh logs are respectively
f64-native-regression.log, fp-legacy-dot-regression.log,
fp-legacy-euler-regression.log, and fp-legacy-step-regression.log under
tmp/euler-recovery-20260907.  No changed tracked outputs resulted.

The independent host-only checked Sod trial, outside the checkout, reaches
t=0.2 in 93 steps with 100 cells.  Every intermediate is finite; maximum
|momentum|/density is 0.9290892948106627 and minimum energy/density is 2.  The
standard Sod inputs therefore remain inside the proposed conservative guard.
The target CFL 0.45 can round upward to 0.4500000000000001, motivating a
separate explicit acceptance ceiling of 0.5 in the implementation.  This is
design/regression evidence only.  The user received the stated domain
assumption; it is not represented as an explicit user approval.

Installed the reviewed binary profile preview in these twelve exact paths:
- proofs/talos/lean/Project/Artifact/Binary/Syntax.lean
- proofs/talos/lean/Project/Artifact/Binary/Decode.lean
- proofs/talos/lean/Project/Artifact/Binary/Grammar.lean
- proofs/talos/lean/Project/Artifact/Binary/Validity.lean
- proofs/talos/lean/Project/Artifact/Binary/Validate.lean
- proofs/talos/lean/Project/Artifact/Binary/Translate.lean
- proofs/talos/lean/Project/Artifact/Binary/Equality.lean
- proofs/talos/lean/Project/Artifact/Binary/Proof/Decode.lean
- proofs/talos/lean/Project/Artifact/Binary/Proof/Validate.lean
- proofs/talos/lean/Project/Artifact/Binary/DecodeTests.lean
- proofs/talos/lean/Project/Artifact/Binary/TranslateTests.lean
- proofs/talos/lean/Project/Artifact/Binary/ValidateTests.lean

The extension covers f64.sub (161), f64.div (163), and unary f64.sqrt (159)
through syntax, opcode classification, grammar, decoder, stack validator,
declarative validity, translation, equality, and soundness proof branches.
Decoder/translator and accepted/rejected operand tests exercise each addition.
No frozen bytes, package manifests, release receipt, or release draft have yet
changed.  The old manifests temporarily retain the prior verifier source
identity while this new profile is proved; no current manifest/release gate
success is claimed during that intermediate state.

The three focused binary test modules passed on the first build (3,350 jobs).
The decoder/validator/translation soundness targets are now building under a
separate 15-minute boundary.  To create the new exact packages without moving
or deleting any pre-existing installer backup, expose the migration output
preparer and CheckFile renderer from tools/artifact-migrate.js.  The existing
CLI and transactional installer are unchanged.  A scoped caller will review
and exclusively create only the new package/proof files, then make bounded
text edits to registry.json and CheckFile.lean.  It will never call applyOutputs.

All three binary soundness modules passed on the first build (3,355 jobs).
Created three exact primitive packages using the exported output preparer,
without the transactional installer.  All 27 new files were required absent
and written exclusively.  The two existing registry/CheckFile texts received
bounded additions, and only verifierSourceSha256 changed in each of the 22
existing manifests.  All existing frozen WASM bytes and protected receipt/draft
hashes were checked unchanged.  Exact mutation and identity ledger:

```json
{
  "oldVerifier": "bf03d3f47fb11563c947224601a21afa95c62fc88df81f493de821e69de9d1e7",
  "newVerifier": "67016a177b2ebcd226da56bd534fd1a1b227c7eefe3a9e1eafd8f9954af75e18",
  "packages": [
    {
      "case": "f64_sub_bits",
      "sha256": "4e320470f360eb2181772b234840d79414f19052ac6b3e26e94bf3a142c94929",
      "byteLength": 1049
    },
    {
      "case": "f64_div_bits",
      "sha256": "b3d81061ed69ffb1a60f9c87fbc82bb2b7d6edbc224ecaef0fb71636b2c34c62",
      "byteLength": 1049
    },
    {
      "case": "f64_sqrt_bits",
      "sha256": "7b236ffd9b15e117e80a60d4b4515682801c4a84bd9d4aeb34239d394d522841",
      "byteLength": 1046
    }
  ],
  "newFiles": [
    "proofs/talos/lean/Project/F64SubBits/ArtifactBytes.lean",
    "proofs/talos/lean/Project/F64SubBits/ArtifactCache.lean",
    "proofs/talos/lean/Project/F64SubBits/ArtifactDecoded.lean",
    "proofs/talos/lean/Project/F64SubBits/ArtifactRawCache.lean",
    "proofs/talos/lean/Project/F64SubBits/ArtifactDecode.lean",
    "proofs/talos/lean/Project/F64SubBits/ArtifactValidation.lean",
    "proofs/talos/lean/Project/F64SubBits/ArtifactTranslation.lean",
    "proofs/artifacts/f64_sub_bits/4e320470f360eb2181772b234840d79414f19052ac6b3e26e94bf3a142c94929/manifest.json",
    "proofs/artifacts/f64_sub_bits/4e320470f360eb2181772b234840d79414f19052ac6b3e26e94bf3a142c94929/program.wasm",
    "proofs/talos/lean/Project/F64DivBits/ArtifactBytes.lean",
    "proofs/talos/lean/Project/F64DivBits/ArtifactCache.lean",
    "proofs/talos/lean/Project/F64DivBits/ArtifactDecoded.lean",
    "proofs/talos/lean/Project/F64DivBits/ArtifactRawCache.lean",
    "proofs/talos/lean/Project/F64DivBits/ArtifactDecode.lean",
    "proofs/talos/lean/Project/F64DivBits/ArtifactValidation.lean",
    "proofs/talos/lean/Project/F64DivBits/ArtifactTranslation.lean",
    "proofs/artifacts/f64_div_bits/b3d81061ed69ffb1a60f9c87fbc82bb2b7d6edbc224ecaef0fb71636b2c34c62/manifest.json",
    "proofs/artifacts/f64_div_bits/b3d81061ed69ffb1a60f9c87fbc82bb2b7d6edbc224ecaef0fb71636b2c34c62/program.wasm",
    "proofs/talos/lean/Project/F64SqrtBits/ArtifactBytes.lean",
    "proofs/talos/lean/Project/F64SqrtBits/ArtifactCache.lean",
    "proofs/talos/lean/Project/F64SqrtBits/ArtifactDecoded.lean",
    "proofs/talos/lean/Project/F64SqrtBits/ArtifactRawCache.lean",
    "proofs/talos/lean/Project/F64SqrtBits/ArtifactDecode.lean",
    "proofs/talos/lean/Project/F64SqrtBits/ArtifactValidation.lean",
    "proofs/talos/lean/Project/F64SqrtBits/ArtifactTranslation.lean",
    "proofs/artifacts/f64_sqrt_bits/7b236ffd9b15e117e80a60d4b4515682801c4a84bd9d4aeb34239d394d522841/manifest.json",
    "proofs/artifacts/f64_sqrt_bits/7b236ffd9b15e117e80a60d4b4515682801c4a84bd9d4aeb34239d394d522841/program.wasm"
  ],
  "updatedManifests": [
    "proofs/artifacts/gcd/51801200954786e42d28caf3ba8806d613ab31ec4abe9b5d4b672e28d953b3ae/manifest.json",
    "proofs/artifacts/assoc_list/6b356640062b5977acaf5459a6d3f8c3f1184c1a3e442b963c54e7a1d3a5a1de/manifest.json",
    "proofs/artifacts/order_book/6faa6ae292bd217814d66e31ee241687974acfed74403543e8482540cfc95558/manifest.json",
    "proofs/artifacts/validate/d408c2db3af861b170cda77077ce4f5ba3d9137008db5a21c6acc433d1398c7a/manifest.json",
    "proofs/artifacts/append_bang/cc5a20a246d6c9f4fd215ffe01283e3c8ccbd80b9288b714e0dd0c380797ce96/manifest.json",
    "proofs/artifacts/push_size/6a6a5e4e9dba3d8daa4fc4becf0a335fef6eea1cd9130ed1b2867f1c21da22fb/manifest.json",
    "proofs/artifacts/push_twice/d62f015137837e6e4bd6c2cffda2d082b3e3268dc18f9ca2e4da52b07984af81/manifest.json",
    "proofs/artifacts/shared_pair/f1cf88bd4fbad114cab41ed10a1f1f43ac1fa49e2ed2e9e13f8d7df6872c741f/manifest.json",
    "proofs/artifacts/pair_free/e3809e304f3572d4674192de101ef74fcc22c3b1ea3c1651c18d7512cdfd8135/manifest.json",
    "proofs/artifacts/box_free/d2701846048e1079da8416f5c2fefeaec39f749b7e1567b8b9c0e7ae175590f5/manifest.json",
    "proofs/artifacts/fold_sum/b599860eb8fe3937148455c27c8cfca5473f967001e563530b4790c43017e3b5/manifest.json",
    "proofs/artifacts/leb_u32/02780df586732a25fdfe827892ca18b278ab02c3893e2c516f1a253d640c327a/manifest.json",
    "proofs/artifacts/clob_quote/5e3d45cba560f8a49c5cd9aedcc33698d57fed2c27034c10da4ac26362e5d522/manifest.json",
    "proofs/artifacts/clob_cancel/b9e304af59b8511a24be491d5e17e0c47f8d0f4a8d89b7471a9b49751ac9cf7e/manifest.json",
    "proofs/artifacts/clob_find_best/b66424e00789f14e8e4f2256f99682725f856a18efd9ce6064a588295bc0c536/manifest.json",
    "proofs/artifacts/clob_post_only/0407b872a87be0337399c414affdd82400fae45ac00a1ca3928e5db20489cf1b/manifest.json",
    "proofs/artifacts/clob_match_fuel/971deb775adf62fb4db34ffe353053b8660b4460a13c870341eba84626410e8a/manifest.json",
    "proofs/artifacts/clob_limit/8f44e7f96de04a6ce531801337305fa932b504ac70f6e4aff5d73b58e5a3747d/manifest.json",
    "proofs/artifacts/clob_market/1b7349307d6e19e7690331173d81d17cfba8f36b9e25f0ba2f16f2fc6d168ffc/manifest.json",
    "proofs/artifacts/clob_depth/d6fe056853750dd985e3d0cd03e6ec488ae98a9791d7b5d53baac95bd352b68f/manifest.json",
    "proofs/artifacts/euler_rusanov/145230bc0f956df81283fb37227c303de2c92e68842d38b985325dca467f6546/manifest.json",
    "proofs/artifacts/euler_rusanov_step/0e4ec3be7480e0490a8637536501ba4b2adf84df66c4a4a45819b0e62d622511/manifest.json"
  ],
  "protectedHashes": [
    [
      "proofs/artifacts/release.json",
      "fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1"
    ]
  ]
}
```

Updated the artifact identity regression's explicit normative verifier digest
to 67016a177b2ebcd226da56bd534fd1a1b227c7eefe3a9e1eafd8f9954af75e18,
and its source-cache inventory to 29.  The latter count had remained at 26
through the source checkpoint, whose gate was not claimed as passing.  The
17-file normative source membership is unchanged.  Existing manifest diffs
are exactly one old/new verifier digest line apiece; CheckFile adds only the
three matching imports and dispatch entries.

Synchronized maintained current inventories to 29 source cases and 25 frozen
packages while preserving historical gate dates and release draft identities.
The verification/specification guides had stale fixed-step pending statements;
these now reflect its completed exact-byte/data milestone.  The source
aggregate timeout and pending primitive package checks remain explicit.
Bounded documentation paths: README.md, DEVELOPING.md, docs/status.md, docs/artifact-format.md, proofs/talos/README.md, plan.md, plans/euler-rusanov.md, docs/spec.md, docs/verifying.md, docs/telos-bug.md, proofs/talos/lean/Project/F64SubBits/README.md, proofs/talos/lean/Project/F64DivBits/README.md, proofs/talos/lean/Project/F64SqrtBits/README.md, devnotes.md.
A read-only lookup for a nonexistent proofs/artifacts/README.md returned ENOENT;
existing documentation authorities were used instead.

The focused exact-package gates for subtraction, division, and square root
all pass, including identity, embedded bytes, decoder/validator soundness,
translation equality, behavior declarations, and axiom audits.  All nine
public primitive execution/numerical theorems report only propext,
Classical.choice, and Quot.sound.  Exact-byte witnesses retain the existing
native-decision policy.  Logs: fp-sub-artifact-check.log,
fp-div-artifact-check.log, and fp-sqrt-artifact-check.log.  The 25-package
check-artifacts aggregate is running in fp-artifacts-25.log, without writing
a release receipt.  Artifact identity/migration tests, 91 maintained docs,
three extra README link checks, and whitespace checks pass.

Independent drafts remain outside the checkout: general raw-word guards and
ordering, conservative side source and pure Talos model, and a checked host
Sod prototype.  A revised host prototype uses CFL target 0.45 with explicit
acceptance ceiling 0.5.  An independently written Riemann reference uses the
shock/rarefaction relations in https://www.clawpack.org/riemann_book/html/Euler.html
and analytic cell integrals for gamma=7/5.  Its pressure-root and shock-jump
residuals are below 4e-16, and its domain integrals reproduce
[0.5625, 0.18, 1.375] within 3e-16 at t=0.2.  The 100/200/400/800-cell host
trials take 93/190/385/774 steps, preserve every checked intermediate and
conservative guard, and give density L1 errors
[0.023762707776387997, 0.016645769363901008, 0.010889542673173476,
0.006977521849557591].  Momentum and energy errors also decrease.  This is
host scientific-validation evidence, not a generated-Wasm or convergence
theorem.  No Python or new repository dependency was used.

Read the original public reports lanyonai/CompressibleEuler issues 2 and 3
through read-only gh API calls.  Stored their numeric facts and links in an
external JSON draft, independently checked both positive exact internal
energies with BigInt rationals, and reproduced negative host-double internal
energies in the reported association.  Both violate |momentum| <= density,
so the selected conservative source guard rejects them before sqrt.  Planned
regressions include both interface orientations and explicit nonfinite inputs.
Exact facts:

```json
[
  {
    "name": "cancellation",
    "source": "https://github.com/lanyonai/CompressibleEuler/issues/2",
    "upstreamCommit": "a736aa5f8b17efd225c4692404e2442361d06729",
    "rhoBits": "3ff3be3969ca97cb",
    "momentumBits": "41981433e88dacc6",
    "energyBits": "432d5df2b6bc70d7",
    "exactInternalEnergy": "553765701395033/11114356709601174",
    "reportedAssociationHostInternalEnergy": -0.5,
    "expectedCheckedStatus": 1
  },
  {
    "name": "one_sided_nan",
    "source": "https://github.com/lanyonai/CompressibleEuler/issues/3",
    "upstreamCommit": "a736aa5f8b17efd225c4692404e2442361d06729",
    "rhoBits": "3fe999999999999a",
    "momentumBits": "400428f5c28f5c29",
    "energyBits": "400fc083126e978d",
    "exactInternalEnergy": "26177172834091/1014120480182583577492357906432",
    "reportedAssociationHostInternalEnergy": -4.440892098500626e-16,
    "expectedCheckedStatus": 1
  }
]
```

2026-09-07 binary-profile checkpoint completion: the serialized
`tools/artifact-proof.js check-artifacts` invocation completed with exit 0,
including all 25 registered exact-artifact theorem targets. The retained log
is tmp/euler-recovery-20260907/fp-artifacts-25.log. This is the artifact-only
aggregate, not a new check-all behavioral or release receipt. The three new
packages separately passed their full focused checks. Both
`node tools/euler-rusanov-interface.js check` and
`node tools/euler-rusanov-step-data.js check` passed after the verifier digest
updates, preserving all published data. Updated only the current status and
completion statements in docs/status.md, docs/spec.md, proofs/talos/README.md,
the three primitive READMEs, plan.md, and plans/euler-rusanov.md; appended
this record and devnotes.md. Source aggregate timeout remains explicit.
The latest user request to publish the SVG is already satisfied by commit
fd1782ae720016cec2fc6fc3ec33d02da44f5b94; the immutable GitHub SVG link was
provided again. Publication intent: review and explicitly stage the binary
profile, three exact packages, 22 verifier-digest-only manifest updates,
registry/check-file wiring, tests, docs, and these records, then publish a
non-forced fast-forward with exact tree/parent/content verification.

Final binary checkpoint review: 91 maintained documentation files pass the
link checker and git diff --check passes. The reviewed explicit path list
contains 80 paths: 53 modified and 27 new. Independently verified all 22 old
manifest changes alter only verifierSourceSha256, all three new binary hashes
and byte lengths match their manifests, the first 22 registry entries are
unchanged, and protected release.json retains SHA-256
fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1.
The external explicit list is work/fp-binary-checkpoint-paths.json.
Reviewed source soundness changes cover all three new opcodes and stack
effects; new package witnesses use the existing exact-byte native policy.
Stage precisely the 80 reviewed paths for the binary checkpoint.

- `DEVELOPING.md`
- `README.md`
- `devnotes.md`
- `docs/artifact-format.md`
- `docs/spec.md`
- `docs/status.md`
- `docs/telos-bug.md`
- `docs/verifying.md`
- `journal.md`
- `plan.md`
- `plans/euler-rusanov.md`
- `proofs/artifacts/append_bang/cc5a20a246d6c9f4fd215ffe01283e3c8ccbd80b9288b714e0dd0c380797ce96/manifest.json`
- `proofs/artifacts/assoc_list/6b356640062b5977acaf5459a6d3f8c3f1184c1a3e442b963c54e7a1d3a5a1de/manifest.json`
- `proofs/artifacts/box_free/d2701846048e1079da8416f5c2fefeaec39f749b7e1567b8b9c0e7ae175590f5/manifest.json`
- `proofs/artifacts/clob_cancel/b9e304af59b8511a24be491d5e17e0c47f8d0f4a8d89b7471a9b49751ac9cf7e/manifest.json`
- `proofs/artifacts/clob_depth/d6fe056853750dd985e3d0cd03e6ec488ae98a9791d7b5d53baac95bd352b68f/manifest.json`
- `proofs/artifacts/clob_find_best/b66424e00789f14e8e4f2256f99682725f856a18efd9ce6064a588295bc0c536/manifest.json`
- `proofs/artifacts/clob_limit/8f44e7f96de04a6ce531801337305fa932b504ac70f6e4aff5d73b58e5a3747d/manifest.json`
- `proofs/artifacts/clob_market/1b7349307d6e19e7690331173d81d17cfba8f36b9e25f0ba2f16f2fc6d168ffc/manifest.json`
- `proofs/artifacts/clob_match_fuel/971deb775adf62fb4db34ffe353053b8660b4460a13c870341eba84626410e8a/manifest.json`
- `proofs/artifacts/clob_post_only/0407b872a87be0337399c414affdd82400fae45ac00a1ca3928e5db20489cf1b/manifest.json`
- `proofs/artifacts/clob_quote/5e3d45cba560f8a49c5cd9aedcc33698d57fed2c27034c10da4ac26362e5d522/manifest.json`
- `proofs/artifacts/euler_rusanov/145230bc0f956df81283fb37227c303de2c92e68842d38b985325dca467f6546/manifest.json`
- `proofs/artifacts/euler_rusanov_step/0e4ec3be7480e0490a8637536501ba4b2adf84df66c4a4a45819b0e62d622511/manifest.json`
- `proofs/artifacts/f64_div_bits/b3d81061ed69ffb1a60f9c87fbc82bb2b7d6edbc224ecaef0fb71636b2c34c62/manifest.json`
- `proofs/artifacts/f64_div_bits/b3d81061ed69ffb1a60f9c87fbc82bb2b7d6edbc224ecaef0fb71636b2c34c62/program.wasm`
- `proofs/artifacts/f64_sqrt_bits/7b236ffd9b15e117e80a60d4b4515682801c4a84bd9d4aeb34239d394d522841/manifest.json`
- `proofs/artifacts/f64_sqrt_bits/7b236ffd9b15e117e80a60d4b4515682801c4a84bd9d4aeb34239d394d522841/program.wasm`
- `proofs/artifacts/f64_sub_bits/4e320470f360eb2181772b234840d79414f19052ac6b3e26e94bf3a142c94929/manifest.json`
- `proofs/artifacts/f64_sub_bits/4e320470f360eb2181772b234840d79414f19052ac6b3e26e94bf3a142c94929/program.wasm`
- `proofs/artifacts/fold_sum/b599860eb8fe3937148455c27c8cfca5473f967001e563530b4790c43017e3b5/manifest.json`
- `proofs/artifacts/gcd/51801200954786e42d28caf3ba8806d613ab31ec4abe9b5d4b672e28d953b3ae/manifest.json`
- `proofs/artifacts/leb_u32/02780df586732a25fdfe827892ca18b278ab02c3893e2c516f1a253d640c327a/manifest.json`
- `proofs/artifacts/order_book/6faa6ae292bd217814d66e31ee241687974acfed74403543e8482540cfc95558/manifest.json`
- `proofs/artifacts/pair_free/e3809e304f3572d4674192de101ef74fcc22c3b1ea3c1651c18d7512cdfd8135/manifest.json`
- `proofs/artifacts/push_size/6a6a5e4e9dba3d8daa4fc4becf0a335fef6eea1cd9130ed1b2867f1c21da22fb/manifest.json`
- `proofs/artifacts/push_twice/d62f015137837e6e4bd6c2cffda2d082b3e3268dc18f9ca2e4da52b07984af81/manifest.json`
- `proofs/artifacts/registry.json`
- `proofs/artifacts/shared_pair/f1cf88bd4fbad114cab41ed10a1f1f43ac1fa49e2ed2e9e13f8d7df6872c741f/manifest.json`
- `proofs/artifacts/validate/d408c2db3af861b170cda77077ce4f5ba3d9137008db5a21c6acc433d1398c7a/manifest.json`
- `proofs/talos/README.md`
- `proofs/talos/lean/Project/Artifact/Binary/CheckFile.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Decode.lean`
- `proofs/talos/lean/Project/Artifact/Binary/DecodeTests.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Equality.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Grammar.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Proof/Decode.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Proof/Validate.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Syntax.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Translate.lean`
- `proofs/talos/lean/Project/Artifact/Binary/TranslateTests.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Validate.lean`
- `proofs/talos/lean/Project/Artifact/Binary/ValidateTests.lean`
- `proofs/talos/lean/Project/Artifact/Binary/Validity.lean`
- `proofs/talos/lean/Project/F64DivBits/ArtifactBytes.lean`
- `proofs/talos/lean/Project/F64DivBits/ArtifactCache.lean`
- `proofs/talos/lean/Project/F64DivBits/ArtifactDecode.lean`
- `proofs/talos/lean/Project/F64DivBits/ArtifactDecoded.lean`
- `proofs/talos/lean/Project/F64DivBits/ArtifactRawCache.lean`
- `proofs/talos/lean/Project/F64DivBits/ArtifactTranslation.lean`
- `proofs/talos/lean/Project/F64DivBits/ArtifactValidation.lean`
- `proofs/talos/lean/Project/F64DivBits/README.md`
- `proofs/talos/lean/Project/F64SqrtBits/ArtifactBytes.lean`
- `proofs/talos/lean/Project/F64SqrtBits/ArtifactCache.lean`
- `proofs/talos/lean/Project/F64SqrtBits/ArtifactDecode.lean`
- `proofs/talos/lean/Project/F64SqrtBits/ArtifactDecoded.lean`
- `proofs/talos/lean/Project/F64SqrtBits/ArtifactRawCache.lean`
- `proofs/talos/lean/Project/F64SqrtBits/ArtifactTranslation.lean`
- `proofs/talos/lean/Project/F64SqrtBits/ArtifactValidation.lean`
- `proofs/talos/lean/Project/F64SqrtBits/README.md`
- `proofs/talos/lean/Project/F64SubBits/ArtifactBytes.lean`
- `proofs/talos/lean/Project/F64SubBits/ArtifactCache.lean`
- `proofs/talos/lean/Project/F64SubBits/ArtifactDecode.lean`
- `proofs/talos/lean/Project/F64SubBits/ArtifactDecoded.lean`
- `proofs/talos/lean/Project/F64SubBits/ArtifactRawCache.lean`
- `proofs/talos/lean/Project/F64SubBits/ArtifactTranslation.lean`
- `proofs/talos/lean/Project/F64SubBits/ArtifactValidation.lean`
- `proofs/talos/lean/Project/F64SubBits/README.md`
- `test/artifact_identity.js`
- `tools/artifact-migrate.js`

2026-09-07 next checked-solver boundary: binary checkpoint publication
completed as c084bf98fd3da0994afc83190ec4549251430124, sole parent
ab57101a17bc6b150b5abedc66a1c537571b4a80, tree
97e529a68e47e1f2f76838e10c1c45a098f95ab1. The exact 80-path staged tree
matched the GitHub API tree; force:false advanced the branch, ordinary fetch
with maintenance disabled returned that commit, all parent/message/tree/index/
worktree checks passed, and CAS update-ref left a clean synchronized branch.
Revalidated the pinned Mac Lean/Lake and wasm-tools executable paths after
compaction. The session sandbox granted the requested repo write and network
permissions for the already-authorized work; no new task permission was asked.

Following the source aggregate timeout, began the smaller existing target
Project.ClobFindBest.Spec through tools/leanrun --timeout 10m and pinned
local one-thread environment. Its fresh log is
tmp/euler-recovery-20260907/source-clob-find-best-boundary.log. Only this
Lean-family job is active. Installed the previously reviewed external draft
as the fresh Project/ProofKit/F64Order.lean: integer finite/positive guards,
sign-cleared magnitude ordering, and proof goals relating guards to decoded
real values. Added sign-clearing equality for positive words and kernel
classification examples for both zeros, subnormal/normal boundaries, maximum
finite encodings, infinities, and NaNs. This draft is not yet checked. No
existing source or artifact program was modified.

The smaller Project.ClobFindBest.Spec build passed (3349 jobs), completing
its Loop and Spec boundary without changing existing source. The first
Project.ProofKit.F64Order build failed in 3 seconds with explicit diagnostics:
UInt64.toNat numeral expressions were not normalized in two positive-word
bounds, and broad simp did not close sign=false. Finite classification and
magnitude-order theorems checked with the standard three axioms; two incomplete
positive lemmas were not accepted or claimed. Added explicit natural-literal
types to the bounds and a direct decide=false proof for sign. Retained
f64-order-first.log and all failed outputs. A read-only lookup mistakenly
named absent tools/talos-artifact-lib.js; recovered the actual tools/talos-lib.js
through file discovery, without any filesystem mutation from the failed read.

Second F64Order run (f64-order-normalized.log) finished in 2 seconds with
one remaining type mismatch in the finite-word subproof: simp-only retained
the UInt64 numeral toNat form while the revised natural bound used a literal.
Used the original raw comparison directly for that finite conversion, preserving
the normalized bound for the arithmetic steps; removed new deprecated ite
lemma names. Three of the four audited public lemmas already checked with
only the standard logical axioms; the final positive lemma remains unclaimed
until the next complete build.

F64Order positive-word correction passed (3050 jobs, 3-second module build)
in f64-order-positive.log. All four public guard/order lemmas audit to only
propext, Classical.choice, and Quot.sound; all signed-zero/subnormal/normal/
finite/infinite/NaN examples kernel-check. Removed the single now-unused
norm_num tactic and added the helper import to Project.lean so the aggregate
checks it. No source-case or exact-artifact registry count changes. This
checkpoint consists exactly of Project/ProofKit/F64Order.lean, Project.lean,
devnotes.md, and journal.md. Recheck the focused target after the no-op removal,
review all four files, then publish that bounded proof foundation.

Final focused F64Order build passed (3050 jobs, 2-second module build) in
f64-order-final.log with no new-module warnings. All four public axiom audits
remain standard-only. Reviewed the complete new proof and the aggregate import;
git diff --check passes. The user questioned the relevance of CLOB work.
Explained its sole role as an old full-regression dependency and deferred all
remaining CLOB builds and the full-source aggregate to keep the active path
on Euler proofs and tests. No CLOB job is running. Stage exactly devnotes.md,
journal.md, proofs/talos/lean/Project.lean, and
proofs/talos/lean/Project/ProofKit/F64Order.lean for this passing checkpoint.

2026-09-07 conservative-state boundary: published the four-path guard
checkpoint as c88c2f3233a74b036deaf009d6c78480eb42a212, sole parent
c084bf98fd3da0994afc83190ec4549251430124, tree
6118d3d286475ec365c9831abcb693e37e1124a6. Exact API/index tree equality,
non-forced branch advance, fetched parent/message/tree/content equality,
local CAS update-ref, and clean synchronized status all passed.
Installed three reviewed fresh drafts: LeanExe/Examples/EulerConservative.lean,
Project/EulerConservative/Model.lean, and Project/EulerConservative/Guard.lean.
The source returns a seven-word checked thermodynamic side; the model uses
only Talos IEEE operations. All inputs and every intermediate have finite/
positive guards before acceptance, including a positive radicand before sqrt.
The physical guard proof derives exact internal energy >= density/2 from
positive density, |momentum| <= density, and energy >= density. This is the
previously discussed conservative implementation domain, not a user-approved
claim of covering all admissible states. Next run only focused Euler targets.

First focused EulerConservative.Guard build completed Model and checked
internalEnergy_lower, but stateGuard_spec had an explicit Bool/decide
simplification mismatch. Replaced the broad unfolding simplifier with direct
short-circuit conjunction projections and of_decide_eq_true, matching the
executable guard structure. Log euler-conservative-guard-first.log retained.
The user then acknowledged the explanation of shared-code regression testing;
confirmed that focused Euler work continues while broader regression remains
pending. No further CLOB work was started.

The guard projection rerun reported a theorem-name error: Bool.and_eq_true
is a proposition equality in this Lean version; Bool.and_eq_true_iff is the
implication interface. Confirmed that in the pinned Lean source and changed
only the four projections. The source-only EulerConservative build passed
(3 jobs, 221ms module build). The user permits manageable regression checks;
use focused per-change checks and a small relevant set, keeping long whole-
repository builds outside the main Euler work.

The Euler guard proof now passes (3062 jobs, 2.8-second module build) in
euler-conservative-guard-iff.log. stateGuard_spec, internalEnergy_lower, and
stateGuard_admissible all use only propext, Classical.choice, and Quot.sound.
Added the focused test/euler_conservative.js with six fixed accepted-word
references, 32 rejection vectors, and emitted IR/WAT arithmetic counts.
Vectors include both Sod states, both velocity guard boundaries, negative
momentum and signed zero; invalid/adjacent inputs, all input positions with
infinities and both NaN classes, pressure underflow, pressure-ratio overflow,
enthalpy overflow, and both published failure tuples. Reference accepted words
were computed with a standalone Node IEEE arithmetic calculation; they are
regression evidence only. The test retains one fresh output directory and
uses the existing runner with a two-minute limit per compiler operation.

The focused compiled-side regression passed all 38 vectors and exact IR/WAT
arithmetic counts; outputs retained in tmp/euler-conservative-Z2IKrq and log
euler-conservative-regression-first.log. Added fresh EulerConservative/Safety.lean
to prove that accepted model status implies the input guard, physical input
admissibility, and finiteness of all twelve rounded intermediates. This is
pure Talos model safety; exact generated-WAT composition remains a subsequent
boundary and is not claimed by the runtime vectors.

First model-safety build produced direct proof diagnostics: split does not
traverse the branch-local have/let blocks without reduction, and norm_num
left the false UInt64 status equality unresolved. Added dsimp-only at each
accepted-stage boundary and discharged rejection with the kernel-decided
UInt64 1 != 0 fact. No numerical model or source code changed. Retained
euler-conservative-safety-first.log; no failed theorem was claimed.

The staged safety rerun proved accepted_inputGuard and accepted_admissible;
one redundant inner dsimp failed its progress check because the outer dsimp
had already reduced all nested lets. Removed only the two redundant inner
reductions; retained euler-conservative-safety-stages.log.

The reduced safety proof reached the final list-tail obligation: all twelve
finite witnesses were correct, but simp did not discharge the empty-list
universal. Added the direct List.forall_mem_nil witness and removed the two
unused simp arguments. Retained euler-conservative-safety-reduced.log.

The complete EulerConservative.Safety target passed (3063 jobs, 2.7-second
module build) in euler-conservative-safety-finite.log. All six Guard/Safety
public theorems audit to standard logical axioms only. Registered this model
safety import in Project.lean and the source build/test in test/run_all.js;
the prohibited full run_all suite was not executed. Added a case README and
updated only current Euler checkpoint items in plan.md, plans/euler-rusanov.md,
docs/status.md, and devnotes.md. There is no new Program cache or complete
source-case registration yet: exact WAT execution is the next boundary.
The first documentation edit command had a Node parser error from Markdown
backticks embedded in a template string and executed no mutations. Reissued
with ordinary quoted lines for the README. Reviewed checkpoint intent: source,
Model/Guard/Safety/README, focused test and registration, aggregate import,
status/plan records, and journal.

Final conservative-side checkpoint review: focused source build, six public
pure-model/guard theorem audits, and all 38 compiled vectors passed. Both test
scripts syntax-check; 91 maintained docs, every new README relative link, and
the aggregate import inventory check pass. No sorry/admit/new-axiom declaration
exists in the new source/proofs. Moved the new current-status paragraph next
to the current capability inventory and stated that the full suite is deferred.
No new numerical source change after passing tests; no broad regression rerun.
Review and stage precisely these 13 paths, then publish non-forced with exact
parent/tree/index/worktree verification:

- `LeanExe/Examples/EulerConservative.lean`
- `devnotes.md`
- `docs/status.md`
- `journal.md`
- `plan.md`
- `plans/euler-rusanov.md`
- `proofs/talos/lean/Project.lean`
- `proofs/talos/lean/Project/EulerConservative/Guard.lean`
- `proofs/talos/lean/Project/EulerConservative/Model.lean`
- `proofs/talos/lean/Project/EulerConservative/README.md`
- `proofs/talos/lean/Project/EulerConservative/Safety.lean`
- `test/euler_conservative.js`
- `test/run_all.js`

2026-09-07 exact conservative-side execution boundary: published the 13-path
source/model safety checkpoint as 4001afe81123cf61875387a79c946f4e27df8e77,
sole parent c88c2f3233a74b036deaf009d6c78480eb42a212, tree
cd8f2f9ed25e867150b07ee3bfa5d611bd94fa23. API/index tree equality,
non-forced branch update, fetched commit/parent/message/tree/content equality,
and local CAS update-ref all passed; final status was clean and synchronized.
Added one deliberately incomplete euler_conservative registry entry and a
Spec import boundary without any admitted theorem. Its two intended public
execution/safety declaration names are pending, not claimed. Explicitly
verified that its Program.lean and two .generated deliverables do not exist.
The following scoped prepare may create only those named deliverables and
its own fresh staging path, preserving all earlier generated state.

Scoped prepare euler_conservative passed and removed only its own fresh
staging directory tmp/leanexe-talos-UA7K2G. Generated Program.lean is unchanged
by hand. Its functions 0/1/2/3/4/5 are positiveBits/absBits/finiteBits/
stateGuard/rejectedSide/sideCheckedBits, with runtime helpers at 6/7/8/9.
Added the new Program import and four exact runtime pins to Runtime/Checks.lean.
Retained log euler-conservative-prepare.log and generated identities:

[
  {
    "path": "proofs/talos/lean/Project/EulerConservative/Program.lean",
    "bytes": 19719,
    "sha256": "1a88dfca607722fb2ccffb7834cef6f354ebb52cff1bcdb98648ec6c1424a7d2"
  },
  {
    "path": "proofs/talos/.generated/euler_conservative/program.wasm",
    "bytes": 2019,
    "sha256": "351a5a9c30b785897afab2c351c265cafd5e060845cb924825cc6badb9459114"
  },
  {
    "path": "proofs/talos/.generated/euler_conservative/program.wat",
    "bytes": 20531,
    "sha256": "3f4fc73b350495438f172357a82bcd517385717547373f39ec664005cc374320"
  }
]

Added fresh EulerConservative/Helpers.lean with a closed-module helper layout
and four module-polymorphic exact execution proof drafts: sign clearing,
positive classification, finite classification through the sign-clear call,
and the seven-word reject result. Each theorem preserves the complete store
and uses TerminatesWith; the state guard helper and main side remain next.
Build only these helpers and the exact runtime pins; no broad source suite.

The first helper build passed absBits_exact, rejectedSide_exact, the generated
Program, and all runtime pins. The positive/finite proofs failed on an
unavailable progress tactic, before their branch reasoning executed. Replaced
the speculative combinator with two explicit positive branches and one finite
branch, and imported the existing TalosCompat metadata-normalization lemmas
used by the earlier Euler execution proof. Retained helpers-first.log; helper
retries are focused on explicit diagnostics, not unchanged timeouts.

The helper branch run reached no-progress diagnostics after simp had already
consumed straight-line instructions. Replaced the redundant fixed sequence
with the existing bounded repeat/first pattern: wp_run itself fails when it
makes no progress, then the explicit if rule handles the next guard. The
final model-value simplification remains separate. Retained helpers-branches.log.

All four scalar helper execution theorems now pass (3350 jobs, 4.4-second
module build) in helpers-consume.log with only the standard three axioms.
Added fresh StateGuard.lean to compose those helper calls through the exact
short-circuit control flow. A small side_peel tactic consumes only determined
scalar prefixes and guards, stopping at calls; the proof splits actual Bool
helper outputs and the two final raw order comparisons. No source or generated
program changed.

StateGuard exact execution passed on its first run (3351 jobs, 5-second
module build), standard three axioms only. Added fresh Execution.lean to
compose the five helper specifications through the main side routine. The
proof names the twelve pure IEEE intermediates, handles the first failed
guard via the proved seven-word rejection call, and preserves the source
arithmetic association on acceptance. It is module-polymorphic over the
closed helper layout and main-function identity. The focused attempt has a
five-minute runner bound and an explicit heartbeat limit; exact main execution
is unclaimed until it passes.

First main execution attempt failed immediately at the entry-frame change:
Wasm operand-stack arguments are reversed, but Function.toLocals expects
source parameter order after the entry rule reverses them. Corrected only
the proof frame to [rho, momentum, energy]. The generated code/model are
unchanged; retained euler-conservative-execution-first.log.

Main execution frame attempt ended with a deterministic eight-million-heartbeat
whnf limit in the first reject tail, not a runner wall timeout. The failed
proof audit is not an accepted theorem. Retained execution-frame.log. A read
of a guessed Wp/Locals.lean returned ENOENT; discovered and read the actual
Interpreter/Wasm/Locals.lean instead, with no mutation from that failed read.
The existing EulerRusanov staged proof explicitly normalizes List.set and
concrete list indexing; wp_run alone does not include these rewrites. Added
only EulerConservative/Rejection.lean as a smaller first-rejection boundary,
with concrete frame normalization and a one-million-heartbeat budget. It
will be checked before changing or rerunning the main execution proof.
User requested manageable regression checks; unrelated CLOB/full-source
aggregate work remains deferred.

The isolated rejection proof passed in four seconds, standard three axioms
only, at one million heartbeats (rejection-normalize.log). This confirms
concrete List.set/index normalization removes the pathological local-frame
reduction. Applied that same explicit normalization to Execution.lean and
its initial prefix; lowered the whole-proof heartbeat budget from eight to
two million. The proof now imports the independently checked rejection
boundary. Only this materially changed focused target will run next.

Normalized main execution passed (3353 jobs, 19-second module), standard
three axioms only, in execution-normalize.log. It proves total seven-word
execution and full store preservation for arbitrary raw inputs. A token-checked
warning cleanup first rejected one-based column interpretation before any
write; Lean diagnostic columns are zero-based. The corrected scoped edit
removes only the 99 unused simp arguments identified by Lean in four new
handwritten proof modules, plus the redundant final peel. Installed the
prepared Spec composition: exact execution and accepted-state admissibility/
finiteness for all twelve intermediates. No generated code, source, or model
changed. Registry remains incomplete until this final focused gate passes.

Final Spec build passed (3366 jobs, Spec 3.7 seconds); both registered
public theorems audit to only propext, Classical.choice and Quot.sound. All
new Euler execution modules now have no linter warnings. Marked the case
complete, imported its Spec in Project, updated the cached-program identity
count to 30, and reconciled the six maintained inventories, side README,
plan and Euler plan. Frozen artifact count remains 25. The inventory edit
stopped at a checked row mismatch after the preceding bounded edits had
completed: the existing sqrt row uses a link around its name. Matched the
actual row, added the conservative side, and retained all prior one-line
behaviorTheorems array formatting. Added this ledger and devnotes only after
those corrections. A read-only lookup used the absent Float64Sqrt directory
name; rg --files subsequently found F64SqrtBits, with no mutation from the
lookup. Focused source regeneration/proof, runtime pins, identity metadata
and doc links remain the checkpoint gates. Source/compiled bytes are unchanged,
so the previously passing 38 vectors need no rerun.

Focused source regeneration and Spec gate passed; the 2,019-byte WASM, WAT
and generated Program identities remain exactly as recorded. Runtime pins
passed (3372 jobs); metadata checks accepted all 30 complete registrations
and cached programs, artifact identity membership, and 91 maintained docs.
The source gate removed only its own fresh staging directory. Correction to
the preceding linter note: one harmless redundant final side_fp_peel remained,
because the first line carried a branch bullet. Removed that exact duplicate
and will recheck only Spec; no runtime vector or unrelated gate is repeated.
The proof inventory now distinguishes the current 30-case aggregate from
the historical 29-case timeout.

The final Spec check passed after redundant-tactic removal (3366 jobs), with
standard-axiom audits and no new Euler warnings. No source or artifact bytes
changed. Review and stage the following 21 exact paths, then publish a
non-forced single-parent checkpoint using API/index/fetched-tree and local
content equality checks; preserve all ignored build/evidence/diagnostic state.

- `DEVELOPING.md`
- `README.md`
- `devnotes.md`
- `docs/spec.md`
- `docs/status.md`
- `docs/verifying.md`
- `journal.md`
- `plan.md`
- `plans/euler-rusanov.md`
- `proofs/talos/README.md`
- `proofs/talos/cases.json`
- `proofs/talos/lean/Project.lean`
- `proofs/talos/lean/Project/EulerConservative/Execution.lean`
- `proofs/talos/lean/Project/EulerConservative/Helpers.lean`
- `proofs/talos/lean/Project/EulerConservative/Program.lean`
- `proofs/talos/lean/Project/EulerConservative/README.md`
- `proofs/talos/lean/Project/EulerConservative/Rejection.lean`
- `proofs/talos/lean/Project/EulerConservative/Spec.lean`
- `proofs/talos/lean/Project/EulerConservative/StateGuard.lean`
- `proofs/talos/lean/Project/Runtime/Checks.lean`
- `test/artifact_identity.js`

Published exact conservative-side execution as 59e486622cbafefc9c79cbd3a64f1f9e046f9b55,
sole parent 4001afe81123cf61875387a79c946f4e27df8e77, tree
08eab1bb2b704b89691ea2abc313c495c469bb75. Non-forced API update, fetch,
commit/parent/message/tree/index/worktree equality and local CAS update passed;
final status was clean and synchronized. Prepared a scoped external freezer
for the exact 2,019-byte side: nine fresh package/proof files plus bounded
registry and CheckFile additions, with all 25 old packages and release draft
hash-protected. The single-package gate is next; no whole-suite rerun.

Created nine fresh conservative-side exact-package files using the output
preparer, with exclusive writes and exact expected-path membership. Added
one registry row and one CheckFile import/arm. All 25 prior manifest/WASM
pairs and the protected historical release draft remain byte-identical.
The verifier source did not change. This is pending the focused package gate.

{
  "case": "euler_conservative",
  "sha256": "351a5a9c30b785897afab2c351c265cafd5e060845cb924825cc6badb9459114",
  "byteLength": 2019,
  "newFiles": [
    "proofs/talos/lean/Project/EulerConservative/ArtifactBytes.lean",
    "proofs/talos/lean/Project/EulerConservative/ArtifactCache.lean",
    "proofs/talos/lean/Project/EulerConservative/ArtifactDecoded.lean",
    "proofs/talos/lean/Project/EulerConservative/ArtifactRawCache.lean",
    "proofs/talos/lean/Project/EulerConservative/ArtifactDecode.lean",
    "proofs/talos/lean/Project/EulerConservative/ArtifactValidation.lean",
    "proofs/talos/lean/Project/EulerConservative/ArtifactTranslation.lean",
    "proofs/artifacts/euler_conservative/351a5a9c30b785897afab2c351c265cafd5e060845cb924825cc6badb9459114/manifest.json",
    "proofs/artifacts/euler_conservative/351a5a9c30b785897afab2c351c265cafd5e060845cb924825cc6badb9459114/program.wasm"
  ],
  "oldPackagesUnchanged": 25,
  "protectedRelease": [
    "proofs/artifacts/release.json",
    "fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1"
  ]
}

The exact-byte checker matched all 2,019 bytes, and the focused artifact
translation theorem passed after decoding and validation. Reconciled package
counts to 26 in the six maintained inventories and two plans, retaining the
dated 25-package aggregate evidence and 25-file conformance counts. Corrected
the preceding source inventory historical sentence: the timed-out aggregate
was 29 cases; only the current inventory is 30. Added package links and
devnotes. The running gate still must finish its behavioral declaration and
axiom checks before publication. Two speculative test filenames were absent
in a read-only search; rg --files showed no such test files, and no test was
run from those names. No runtime or whole-suite regression is needed for
unchanged executable/verifier bytes.

Focused conservative-side package gate completed with exit zero, including
all manifest declaration types and axiom audits. Public source/execution/
safety theorems contain only the standard three axioms; exact embedded-byte
decision witnesses use the existing accepted native_decide package policy.
The normative decoder and validator soundness theorems remain standard-axiom
only. Identity membership and all 91 maintained doc links pass. The release
draft still hashes to fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1.
Review and stage only these 22 paths for a non-forced verified checkpoint:

- `DEVELOPING.md`
- `README.md`
- `devnotes.md`
- `docs/spec.md`
- `docs/status.md`
- `docs/verifying.md`
- `journal.md`
- `plan.md`
- `plans/euler-rusanov.md`
- `proofs/artifacts/registry.json`
- `proofs/talos/README.md`
- `proofs/talos/lean/Project/Artifact/Binary/CheckFile.lean`
- `proofs/talos/lean/Project/EulerConservative/README.md`
- `proofs/talos/lean/Project/EulerConservative/ArtifactBytes.lean`
- `proofs/talos/lean/Project/EulerConservative/ArtifactCache.lean`
- `proofs/talos/lean/Project/EulerConservative/ArtifactDecode.lean`
- `proofs/talos/lean/Project/EulerConservative/ArtifactDecoded.lean`
- `proofs/talos/lean/Project/EulerConservative/ArtifactRawCache.lean`
- `proofs/talos/lean/Project/EulerConservative/ArtifactTranslation.lean`
- `proofs/talos/lean/Project/EulerConservative/ArtifactValidation.lean`
- `proofs/artifacts/euler_conservative/351a5a9c30b785897afab2c351c265cafd5e060845cb924825cc6badb9459114/manifest.json`
- `proofs/artifacts/euler_conservative/351a5a9c30b785897afab2c351c265cafd5e060845cb924825cc6badb9459114/program.wasm`

Published conservative-side exact bytes as f8a1d80bc39a579b390bba4696ef80052cc2c1ae,
sole parent 59e486622cbafefc9c79cbd3a64f1f9e046f9b55, tree
7e8b076645d43b45bbdcca844cab9a5afbb69345. Non-forced API update, fetch,
commit/parent/message/tree/index/worktree equality and local CAS update passed;
final status was clean and synchronized. Installed the reviewed dynamic-flux
source draft and corresponding pure IEEE model as fresh files. Both sides
must succeed before unsigned speed selection; each scalar flux component
checks all five inputs and six rounded intermediates. Added a fresh side
output-positivity proof boundary for that selection. Source registries and
artifact inventories remain at 30 and 26 until new exact execution passes.

Dynamic-flux source builds (4 jobs, 187 ms). Its pure model and the separate
accepted pressure/speed positivity theorem also pass first try (3065 jobs);
accepted_outputPositive audits to propext and Quot.sound only. Added a fresh
dynamic Safety boundary proving all six component intermediates finite,
component result finiteness, both-side acceptance and physical admissibility.
The next checks remain those focused proof targets and the new runtime vectors.

Both component safety lemmas passed first try. accepted_sides stopped at
a leading source let binding before its first if; added dsimp only at that
exact point. No theorem using the failed lemma is claimed yet; retained
dynamic-safety-first.log. Added accepted_fields to compose finite component
outputs and the already proved positive finite speed selection. Added a
focused 76-vector runtime script: 15 scalar-component checks and 61 interface
checks, including both orientations of the published states and nonfinite
words in each input position. The script preserves fresh WASM/WAT outputs.

All 76 focused runtime vectors pass, including both issue orientations and
accepted-side viscosity overflow; retained tmp/euler-dynamic-flux-QSr4kZ.
The expanded Safety build identified a now-redundant dsimp after the first
side branch, and split selected the nested maximum-speed if before the final
component-status guard. The ensuing metavariable elaboration exhausted the
default heartbeat limit after that concrete type mismatch. Removed the
redundant simplification and explicitly split/simplified the two speed-order
branches before the component-status split. This changes the failing proof
boundary; no limit increase or unchanged timeout retry.

Dynamic model Safety passes after explicit speed-order splitting (3066 jobs,
2.6 seconds), with all five public theorems limited to the standard logical
axioms. Added selected_speed_bound to make raw-positive ordering imply a
decoded-real bound on both computed speeds, using F64Order rather than any
new float assumption. Registered only the source build/runtime test and model
Safety aggregate import, added the scoped README/status/plan checkpoint.
Exact WAT and artifact registration stay pending; counts remain 30/26.

Selected-speed bound passed on its first build (3066 jobs, Safety 2.7 seconds);
all six dynamic safety theorems and the side output-positivity theorem audit
to only the accepted standard logical axioms. No new warning. Source and
76 compiled vectors have not changed since passing. Added concise devnotes.
Remaining checkpoint checks are local doc links, JS syntax and aggregate
registration membership, with no further Lean or runtime regression needed.

The maintained 91-document gate, new dynamic README local links, both JS
syntax checks and unchanged 30-case aggregate membership all pass. Reviewed
the new source/model association, all seven theorem audits, 76 exact runtime
vectors, and registration diff. Stage exactly these 13 paths and publish
non-forced with the usual full parent/tree/content equality checks:

- `LeanExe/Examples/EulerDynamicFlux.lean`
- `devnotes.md`
- `docs/status.md`
- `journal.md`
- `plan.md`
- `plans/euler-rusanov.md`
- `proofs/talos/lean/Project.lean`
- `proofs/talos/lean/Project/EulerConservative/Outputs.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/Model.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/README.md`
- `proofs/talos/lean/Project/EulerDynamicFlux/Safety.lean`
- `test/euler_dynamic_flux.js`
- `test/run_all.js`

Published dynamic flux source/model checkpoint as 8591ffe023199b5016160e54f293185e1b49d694,
sole parent f8a1d80bc39a579b390bba4696ef80052cc2c1ae, tree
d6646b888e6d1167acb560684f2795ce50e1aca4. Non-forced API update, fetch,
commit/parent/message/tree/index/worktree equality and local CAS update passed;
final status was clean and synchronized. Added one deliberately incomplete
dynamic-flux source registration and fresh Spec import boundary. The next
scoped prepare may create only this case Program/WASM/WAT and its own fresh
staging path. Existing conservative-side functions occupy 0..5 unchanged in
the inspected compiled WAT, checked component is 9, main flux is 16, and
runtime helpers are 17..20. Getter functions are emitted but inlined in the
main body; exact main composition needs two side calls and three component
calls, with reject helper 15 and no getter calls.

Dynamic prepare passed, using only fresh staging tmp/leanexe-talos-bhS0V2.
Added the exact shared-function layout and two reject-helper proof boundaries,
plus four runtime pins for functions 17..20. The layout checks shared side
functions directly against the already proved conservative definitions.
No generated Program text was edited by hand. Exact generated identities:

[
  {
    "path": "proofs/talos/lean/Project/EulerDynamicFlux/Program.lean",
    "bytes": 32770,
    "sha256": "c8dfaa49d27023dece69d549536a89baea8be6089f65daafd738b13ad52324a0"
  },
  {
    "path": "proofs/talos/.generated/euler_dynamic_flux/program.wasm",
    "bytes": 3167,
    "sha256": "304dba74824ae38465a91c83c20b3aa9b8fe9310a761ca2c7135edc22bf9e022"
  },
  {
    "path": "proofs/talos/.generated/euler_dynamic_flux/program.wat",
    "bytes": 32864,
    "sha256": "ca3c822bfbb2fc0c1567e50cefd5c8c8dae5e2d337285f18ee71ec229c6616af"
  }
]

The closed dynamic module layout, shared conservative helper identities,
two reject functions, and four runtime pins all pass (3387 jobs; Helpers
3.6 seconds, Runtime.Checks 3.7 seconds). Audits contain only standard axioms.
Added the fresh Component.lean exact execution boundary for function 9: all
eleven helper guards and six IEEE operations in source order, each rejection
via the proved two-word helper, arbitrary raw inputs and full store preservation.
Concrete local-frame normalization is reused from the accepted side proof.

The input-generic component exact execution proof passed on its first build
(3357 jobs), standard logical axioms only. Removed only the unused simp
arguments identified at exact diagnostic locations. Added the fresh main
Execution proof boundary: reuse two previously proved side calls, select
the speed by unsigned order, compose three proved component calls, and
handle every accepted/rejected status path. The two speed branches use
explicit selected words and named pure component records to keep local
frame reduction separate from IEEE internals. Main execution remains
unclaimed until its focused three-minute check passes.

Main dynamic-interface exact execution passed on its first build (3358 jobs),
standard logical axioms only. Removed only diagnostic-identified unused simp
arguments. Installed the completed Spec draft composing exact execution with
physical input admissibility, finite output fluxes and positive finite alpha.
The public safety theorem is pending the focused Spec check; no generated
Program, source, model or runtime vector changed.

Dynamic Spec passed (3373 jobs; Spec 3.6 seconds), both public theorems with
standard logical axioms only and no new dynamic warnings. Marked the registry
entry complete, imported Spec, raised the cached-program identity count to
31, and reconciled the eight inventories/plans plus the dynamic README and
devnotes. Exact binary is 3,167 bytes; package count remains 26. Source, model
and runtime vectors are unchanged. The next gate regenerates only this
source cache and checks its Spec, followed by lightweight docs/identity/import
checks and incremental publication.

Focused dynamic source/cache regeneration and Spec gate pass. All 31
registration/import/cache memberships agree, identity metadata passes, and
91 maintained docs pass. Runtime pins already passed for these unchanged
bytes; the 76 compiled vectors need no rerun. Clarified the Euler plan count
sentence to include the new interface. Reviewed exact helper layout, component
proof, main call composition, both public Specs and all standard-axiom audits.
Stage only these 20 paths and publish a non-forced verified checkpoint:

- `DEVELOPING.md`
- `README.md`
- `devnotes.md`
- `docs/spec.md`
- `docs/status.md`
- `docs/verifying.md`
- `journal.md`
- `plan.md`
- `plans/euler-rusanov.md`
- `proofs/talos/README.md`
- `proofs/talos/cases.json`
- `proofs/talos/lean/Project.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/Component.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/Execution.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/Helpers.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/Program.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/README.md`
- `proofs/talos/lean/Project/EulerDynamicFlux/Spec.lean`
- `proofs/talos/lean/Project/Runtime/Checks.lean`
- `test/artifact_identity.js`

Published dynamic exact execution as 654da5b8a0fc1fe00f41532dc51f259b7da2dfcc,
sole parent 8591ffe023199b5016160e54f293185e1b49d694, tree
66dd638d0c7cbaa94d5497a370d8bb6aae0bdf14. Non-forced API update, fetch,
commit/parent/message/tree/index/worktree equality and local CAS update passed;
final status was clean and synchronized. Prepared the same scoped freezer
for the exact 3,167-byte dynamic interface, with nine new package/proof
files, bounded registry/CheckFile additions, and byte-hash protection of
all 26 prior packages plus the historical release draft. Verifier source
is unchanged. Only the new single-package gate will run.

Created nine fresh dynamic-interface exact-package files using the output
preparer, with exclusive writes and exact expected-path membership. Added
one registry row and one CheckFile import/arm. All 26 prior manifest/WASM
pairs and the protected historical release draft remain byte-identical.
The verifier source did not change. This is pending the focused package gate.

{
  "case": "euler_dynamic_flux",
  "sha256": "304dba74824ae38465a91c83c20b3aa9b8fe9310a761ca2c7135edc22bf9e022",
  "byteLength": 3167,
  "newFiles": [
    "proofs/talos/lean/Project/EulerDynamicFlux/ArtifactBytes.lean",
    "proofs/talos/lean/Project/EulerDynamicFlux/ArtifactCache.lean",
    "proofs/talos/lean/Project/EulerDynamicFlux/ArtifactDecoded.lean",
    "proofs/talos/lean/Project/EulerDynamicFlux/ArtifactRawCache.lean",
    "proofs/talos/lean/Project/EulerDynamicFlux/ArtifactDecode.lean",
    "proofs/talos/lean/Project/EulerDynamicFlux/ArtifactValidation.lean",
    "proofs/talos/lean/Project/EulerDynamicFlux/ArtifactTranslation.lean",
    "proofs/artifacts/euler_dynamic_flux/304dba74824ae38465a91c83c20b3aa9b8fe9310a761ca2c7135edc22bf9e022/manifest.json",
    "proofs/artifacts/euler_dynamic_flux/304dba74824ae38465a91c83c20b3aa9b8fe9310a761ca2c7135edc22bf9e022/program.wasm"
  ],
  "oldPackagesUnchanged": 26,
  "protectedRelease": [
    "proofs/artifacts/release.json",
    "fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1"
  ]
}

The dynamic package byte match, decoding, validation and exact translation
passed. Reconciled only current package counts to 27, retained the historical
26-case source aggregate and 25-package artifact aggregate facts, and linked
the exact package/proof from the dynamic README. The running gate still must
finish behavioral declarations and axiom audits before publication. A read-only
lookup mistakenly named absent LeanExe/Wasm/Core.lean; no source/compiler
mutation resulted, and future emitter searches use the directory inventory.
Array.replicate and Array.set! support was inspected for the forthcoming
double-buffered step; no new array source or proof has been installed yet.

The focused dynamic-interface package gate completed with exit zero, including
all manifest declaration types and axiom audits. Public execution/safety
theorems have only the standard three axioms; byte-decision witnesses use
the existing accepted package native_decide policy. Decoder/validator
soundness remains standard-axiom only. Identity metadata and 91 maintained
docs pass; protected release draft hash remains
fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1.
Review and stage only these 22 paths for a non-forced verified checkpoint:

- `DEVELOPING.md`
- `README.md`
- `devnotes.md`
- `docs/spec.md`
- `docs/status.md`
- `docs/verifying.md`
- `journal.md`
- `plan.md`
- `plans/euler-rusanov.md`
- `proofs/artifacts/registry.json`
- `proofs/talos/README.md`
- `proofs/talos/lean/Project/Artifact/Binary/CheckFile.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/README.md`
- `proofs/talos/lean/Project/EulerDynamicFlux/ArtifactBytes.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/ArtifactCache.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/ArtifactDecode.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/ArtifactDecoded.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/ArtifactRawCache.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/ArtifactTranslation.lean`
- `proofs/talos/lean/Project/EulerDynamicFlux/ArtifactValidation.lean`
- `proofs/artifacts/euler_dynamic_flux/304dba74824ae38465a91c83c20b3aa9b8fe9310a761ca2c7135edc22bf9e022/manifest.json`
- `proofs/artifacts/euler_dynamic_flux/304dba74824ae38465a91c83c20b3aa9b8fe9310a761ca2c7135edc22bf9e022/program.wasm`

Published dynamic exact bytes as 9788bd2efc0acc24b13d4313fb08bb47eed21cf0,
sole parent 654da5b8a0fc1fe00f41532dc51f259b7da2dfcc, tree
46062da645906cce05708280c3e5c55e27b15b95. Non-forced API update, fetch,
commit/parent/message/tree/index/worktree equality and local CAS update passed;
final status was clean and synchronized. Added fresh EulerCellStep source
and pure IEEE model. A positive finite dt/dx ratio and two accepted dynamic
interfaces precede the rounded Courant check (positive and at most 1/2).
Three checked difference/multiply/subtract updates precede a final checked
thermodynamic validation of the new state. Accepted output is status, density,
momentum, energy, pressure, selected speed and Courant number; rejection is
status one and six positive zeros. The array wrapper and runner are still
pending, with no new source-case or frozen-package registration yet.

Cell source builds (5 jobs, 183 ms). Added a fresh focused Safety boundary
for the three rounded update intermediates, accepted updated-state bounds/
admissibility/positive pressure, and the raw positive Courant ceiling. The
proof composes the checked-side safety result after explicit cell guard
case analysis; all resulting facts remain unclaimed until the build passes.

Cell Safety builds successfully (3,068 jobs, 2.0-second new module), with
only standard logical axioms for the three public theorems. A read-only
Node host-oracle import initially failed because process.argv[1] was absent;
using an explicit stdin '-' argument succeeded without modifying the oracle.
Fixed words include two adjacent ratios, 3fdb0b80ef844ba1 and
3fdb0b80ef844ba2, whose rounded Courant values are both exactly 1/2;
3fdb0b80ef844ba3 is the first rejected ratio with Courant one ULP above.
Added a decoded-real positive Courant ceiling lemma by composing existing
positive-word order with exact decoding of the binary64 half constant.
The resumed environment still selects pinned ARM Mac tools through
tools/macos-env.sh; no tool replacement or parallel Lean work occurs.

Decoded Courant proof passes (3,068 jobs, 6.0-second module). All four
public cell model safety audits contain only standard logical axioms. Added
a focused compiled regression with 16 scalar and 27 cell cases, including
the adjacent rounded-CFL boundary, update overflow stages, published bad
states in three neighborhood positions, and final updated-state rejection.
The expected full-cell operation counts are checked against emitted IR/WAT.

Registered only the new source build, focused test and model Safety import;
source-proof/artifact registries stay unchanged. Added the cell README and
synchronized plan/status/devnotes with that boundary. A read-only lookup
incorrectly named absent tools/talos-artifacts.json; the actual registry is
proofs/talos/cases.json. No generator or registry mutation resulted.

The focused compiled regression passes all 16 scalar updates and 27 full
cells, retaining tmp/euler-cell-step-Gh0rFn. Both emitted IR and WAT have
Sub2/Mul1 for scalar update and Sub5/Div2/Mul10/Add4/Sqrt1 for the full cell.
Identity metadata and 91 maintained Markdown files pass; new cell README
links were separately checked. Source/model diff has only the intended
namespace, intrinsic and deriving substitutions. No broad regression ran.
Review/stage precisely these 12 paths for verified non-forced publication:

- LeanExe/Examples/EulerCellStep.lean
- proofs/talos/lean/Project/EulerCellStep/Model.lean
- proofs/talos/lean/Project/EulerCellStep/Safety.lean
- proofs/talos/lean/Project/EulerCellStep/README.md
- test/euler_cell_step.js
- test/run_all.js
- proofs/talos/lean/Project.lean
- docs/status.md
- plan.md
- plans/euler-rusanov.md
- devnotes.md
- journal.md

Published the checked-cell source/model checkpoint as
9763988cdce7e658d9ff76c2baf2ef79ffd5c0da, sole parent
9788bd2efc0acc24b13d4313fb08bb47eed21cf0, tree
a84aa4026cc61ba508b3df814e11ef0fe66a2cc7. The non-forced GitHub update,
fetch, commit/parent/message/tree/index/worktree equality, local CAS and
clean synchronized status all passed. A read-only lookup named absent
test/runtime_pins.js; inventory discovery located the actual runtime pins
in Project/Runtime/Checks.lean. Added an explicitly incomplete cell registry
entry for scoped Program/WAT/WASM preparation; no execution claim yet.

Added fresh module-polymorphic cell layout/rejection and scalar-update
execution proof boundaries, reusing the dynamic layout and finite/positive
helper theorems. Emitted WAT inspection identifies update19, rejection24,
cell25, and allocator/reset/retain/release26–29. Shared functions0–16
retain the prior interface layout; concrete equality remains a Lean gate.

Scoped cell preparation passed, creating Program/WAT/WASM through fresh
tmp/leanexe-talos-b30Zbj. The tool removed only its own fresh staging path.
Added the exact cell execution composition draft: one ratio classifier,
two proved interfaces, Courant classification/ceiling, three proved scalar
updates and the proved final state calculation. All acceptance/rejection
branches preserve the initial store; the public claim awaits its Lean gate.

The scalar exact update and concrete shared-layout proofs pass (Helpers
3.7s, Update7.4s), using only standard axioms. The first full execution
draft failed after9.3s: generic peeling before Boolean case analysis
consumed a conditional boundary before the appropriate callee application.
Preserved that draft externally and its diagnostic log; moved case analysis
ahead of peeling, as in the accepted conservative/component proofs. These
were elaboration errors, not a timeout or a numerical test failure; no
failed declaration/temporary sorryAx report is claimed as a proof.

Generated cell identities: Program48,499 bytes SHA256
33942e73793fe3ba1387d76dba5db3150e6a371de2add323aeee3d31b0417279;
WASM4,592 bytes SHA256
2f6f8c1717d35fe1dbd236855620fade2e083d76d5163c69e6f1f41507bb346f;
WAT49,308 bytes SHA256
0fea5e1fe1c8db7ebcc84f1a5b64a2dd33234a635113f7edf4f4d0155f08cfa6.
Added accepted selected-speed positivity to the model and a public Spec
draft attaching state/Courant/speed safety to exact execution.

The second execution check narrowed failures to the Courant ceiling
(12-second module diagnostic). Removed the remaining premature peel before
that unsigned comparison case split and pruned the specifically reported
unused simp arguments. The second draft and diagnostics are retained.

The next Spec check confirms the new alpha safety theorem (Safety6.2s)
but execution still fails only at the Courant comparison boundary (12s).
Added one bounded pretty-printed goal trace at that boundary to inspect
the exact unsigned-comparison normalization; preserved the prior draft.
No timeout or limit increase occurred.

The diagnostic option pp.maxDepth is unavailable in this pinned Lean;
that diagnostic attempt failed before printing the goal. Replaced it with
ordinary trace_state and retained the failed log.

The ordinary trace isolates the remaining issue: the WAT condition contains
IEEE64.mul ratio right.alpha (or left.alpha), while the guard hypothesis
used a local let alias courant. Generic simp did not unfold that alias in
the hypothesis. Wrote the comparison case split with the explicit rounded
product, matching the instruction condition; removed only the temporary
trace statement. This corrects the earlier incomplete tactic-order diagnosis.

Explicit rounded-product hypotheses close the full execution proof (35s),
and the public Spec passes (3.7s,3,379 jobs total). Both public specifications
and execution/helper theorems use only standard logical axioms. Removed
only reported unused simp arguments for the final source gate, registered
the complete case and its four runtime pins, switched Project to the Spec
import, and reconciled current inventories to32 source cases/27 packages.
The five model safety results include positive selected speed. The source
and runtime vectors are unchanged. Historical aggregate/release facts remain
qualified; no broad source, release, conformance or selfhost check ran.

The final focused cell source gate passes regenerated-cache equality and
Spec (3,379 jobs), with no new cell warnings; Execution35s and Spec3.6s.
Runtime pin checks pass (3,374 jobs,3.8s module). All32 registry/import
members match; metadata and91 maintained docs plus cell README links pass.
Review and stage these21 exact paths for non-forced verified publication:

- DEVELOPING.md
- README.md
- devnotes.md
- docs/spec.md
- docs/status.md
- docs/verifying.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/README.md
- proofs/talos/cases.json
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/Runtime/Checks.lean
- test/artifact_identity.js
- proofs/talos/lean/Project/EulerCellStep/Execution.lean
- proofs/talos/lean/Project/EulerCellStep/Helpers.lean
- proofs/talos/lean/Project/EulerCellStep/Program.lean
- proofs/talos/lean/Project/EulerCellStep/Spec.lean
- proofs/talos/lean/Project/EulerCellStep/Update.lean
- proofs/talos/lean/Project/EulerCellStep/Safety.lean
- proofs/talos/lean/Project/EulerCellStep/README.md

Published exact cell execution as a4930832e6792c952b076c217bad278e6c7fca6c,
sole parent9763988cdce7e658d9ff76c2baf2ef79ffd5c0da and tree
9c331098bf8de79b7ce8bc88cab274103c876a00. Non-forced API update, fetch,
commit/parent/message/tree/index/worktree equality and local CAS all passed;
final status was clean and synchronized. Preparing only the new exact cell
package, while preserving prior binaries/manifests and historical receipts.

Created nine fresh cell-update exact-package files using the output
preparer, with exclusive writes and exact expected-path membership. Added
one registry row and one CheckFile import/arm. All 27 prior manifest/WASM
pairs and the protected historical release draft remain byte-identical.
The verifier source did not change. This is pending the focused package gate.

{
  "case": "euler_cell_step",
  "sha256": "2f6f8c1717d35fe1dbd236855620fade2e083d76d5163c69e6f1f41507bb346f",
  "byteLength": 4592,
  "newFiles": [
    "proofs/talos/lean/Project/EulerCellStep/ArtifactBytes.lean",
    "proofs/talos/lean/Project/EulerCellStep/ArtifactCache.lean",
    "proofs/talos/lean/Project/EulerCellStep/ArtifactDecoded.lean",
    "proofs/talos/lean/Project/EulerCellStep/ArtifactRawCache.lean",
    "proofs/talos/lean/Project/EulerCellStep/ArtifactDecode.lean",
    "proofs/talos/lean/Project/EulerCellStep/ArtifactValidation.lean",
    "proofs/talos/lean/Project/EulerCellStep/ArtifactTranslation.lean",
    "proofs/artifacts/euler_cell_step/2f6f8c1717d35fe1dbd236855620fade2e083d76d5163c69e6f1f41507bb346f/manifest.json",
    "proofs/artifacts/euler_cell_step/2f6f8c1717d35fe1dbd236855620fade2e083d76d5163c69e6f1f41507bb346f/program.wasm"
  ],
  "oldPackagesUnchanged": 27,
  "protectedRelease": [
    "proofs/artifacts/release.json",
    "fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1"
  ]
}

Reconciled current package inventory to28 and linked the exact cell
package from its README. The scoped gate is still running; these checkpoint
documentation statements will be published only after it passes. The
verifier source and all27 earlier packages remain unchanged, and source
count stays32. Existing Wasmtime host support already accepts ArrayUInt64
arguments/results; the planned array step can use it without C/API changes.

The focused cell package gate completed with exit zero. Embedded byte match,
exact decoding, validation, translation, behavioral declaration types and
axiom audits pass. The execution and safety declarations use only the three
standard logical axioms; exact-byte native decision witnesses remain within
the existing package policy. Metadata, 91 maintained docs and all new
package README links pass. Review/stage exactly these 22 paths:

- DEVELOPING.md
- README.md
- devnotes.md
- docs/spec.md
- docs/status.md
- docs/verifying.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/artifacts/registry.json
- proofs/talos/README.md
- proofs/talos/lean/Project/Artifact/Binary/CheckFile.lean
- proofs/talos/lean/Project/EulerCellStep/README.md
- proofs/talos/lean/Project/EulerCellStep/ArtifactBytes.lean
- proofs/talos/lean/Project/EulerCellStep/ArtifactCache.lean
- proofs/talos/lean/Project/EulerCellStep/ArtifactDecode.lean
- proofs/talos/lean/Project/EulerCellStep/ArtifactDecoded.lean
- proofs/talos/lean/Project/EulerCellStep/ArtifactRawCache.lean
- proofs/talos/lean/Project/EulerCellStep/ArtifactTranslation.lean
- proofs/talos/lean/Project/EulerCellStep/ArtifactValidation.lean
- proofs/artifacts/euler_cell_step/2f6f8c1717d35fe1dbd236855620fade2e083d76d5163c69e6f1f41507bb346f/manifest.json
- proofs/artifacts/euler_cell_step/2f6f8c1717d35fe1dbd236855620fade2e083d76d5163c69e6f1f41507bb346f/program.wasm

Published the exact cell package as 12a2dda2bf28bed106e29e58ab89798d185d0a05,
sole parent a4930832e6792c952b076c217bad278e6c7fca6c and tree
ec0d0ad13f15d3b00e8d71df3ce56c954f0763b7. Non-forced update, fetch,
commit/parent/message/tree/index/worktree equality, local CAS and clean
synchronized status passed. A read-only example lookup guessed absent
LeanExe/Examples/F64Dot.lean; discovery identified Float64Bits.lean.
Added fresh EulerGridStep source from the separately prepared draft. The
read-only maximum-speed scan checks every conservative state. The step
reads immutable flat triples and fills a separate array: leading status,
then six words per cell (density, momentum, energy, pressure, alpha, CFL).
It clamps boundary neighbors to the end state and stops on first rejection.
Rejected payload is not interpreted as a grid. Exact grid proofs and full
Sod evaluation remain pending; no new complete-case registration is made.

The grid source builds (6 jobs, 203 ms). Added 31 focused grid/scan
regressions using the existing generic test host wrapper. Five accepted
grids include one-cell boundaries, two-cell Sod, the 100-cell initial step
and a uniform moving state, with fixed raw expected outputs. Rejection
cases cover malformed shape, invalid ratio, bad state placement, CFL and
post-update domain failure. IR/WAT operation counts check both exports.

The first compiled-grid test was rejected immediately at the scan entry
signature; no Wasmtime vectors ran, and tmp/euler-grid-step-EH2m5f remains.
Inspection of Extract/Types.lean shows the public ABI accepts named
structures but does not export product types. Replaced the pair return with
CheckedSpeed (status, speed), retaining the same two raw slots and behavior.
This corrects the initial tentative loop-form diagnosis; no compiler change
or new ABI feature is needed. The original source draft remains outside
the checkout as the preserved first attempt.

The structured scan compiled and its operation counts matched. The grid
shape test stopped before numerical vectors: emitted IR/WAT contain 14
f64 multiplies rather than 10. Inspection of retained module
tmp/euler-grid-step-rTMtUl shows four inlined cell Courant calculations in
the grid entry, plus the separate original cell function; this is not
integer indexing emitted as floating point. The extra copies arise in the
multi-slot loop form. Preserved source/IR/WAT and replaced the body with a
named advanceAt helper returning the output array, using output[0] as the
status guard. Each cell still reads the old grid and writes only its own
six fields, or marks rejection. The source boundary is chosen to support
reuse of the already proved cell call; no compiler changes are made.

Added a fresh pure IEEE grid model with explicit finite recursion for the
speed scan and cell fill. The recursion parameter counts remaining cells;
it is not execution fuel. The model names the cell payload and six writes
for reusable array invariants. It matches the revised named-body source,
and preserves rejected partial payload rather than pretending it is a grid.
No grid execution theorem or completed registry entry is claimed yet.

The named body reduces the emitted extra cell copies from four to one,
but the shape check still finds 11 multiplies (10 shared plus one inlined
Courant in advanceAt). Preserved the helper draft and tmp/euler-grid-step-wdQrGj.
Separated writeCell, taking the checked result as an explicit parameter,
so the argument boundary can materialize the complete cell call once before
any output mutation. The pure model remains unchanged by this source-only
factoring; numerical vectors have not yet run because shape checking stops
on the differing instruction count.

Added the first grid model invariant boundary: output sizes, preservation
of earlier payload words and status by cell writes, rejection persistence,
and accepted-fill implication for every requested cell computation. These
are model-level facts pending their Lean check; exact array memory/loop
execution and output-payload correspondence remain separate open obligations.

The writer boundary leaves one inlined cell body (11 multiplies); retained
tmp/euler-grid-step-8ejoow and the writer draft. Demand.lean identifies the
reason: potentially trapping Array.get! arguments prevent a strict call
when the checked callee can reject before demanding every argument. Changed
input reads in source/model to total Array.getD with default zero. Valid
grid indices retain identical words; out-of-range state reads give zero
density and are rejected. This permits a strict reusable cell-call boundary
without modifying the compiler or trusted base.

The total-read grid test passes all 31 cases, retaining
tmp/euler-grid-step-FbrhmU. Scan bytes: 5,311, SHA256
86bc0a010fffc55441684298a58af9c8099552515f436acccd27a94594105286.
Step bytes: 11,222, SHA256
c7c0bb1425a0adb567b4b5cf96f62112181519078297fb3d4a3f5a8691695a02.
Step34 calls Cell25 once and writer33 once; entry35 calls Step34 in its
loop. Shared functions0–25 are retained, with no FP instructions in the
array wrapper. The pure Model builds (3s). First Safety proof attempt
needs local-let reduction before two case splits and an explicit split for
the size projection over fill. Preserved the first draft/log and made those
local proof corrections. No numerical or compiler failure remains.

The second grid Safety build reached the one-million-heartbeat limit in
advanceAt_accepted while resolving an anonymous guard over the full IEEE
cell expression. The failed draft and euler-grid-safety-splits.log remain.
Generalized the checked-cell result to an opaque record and named the guard
before extracting Boolean equality; this reduces the proof boundary without
raising its budget. The resumed session reread both operating contracts and
confirmed the pinned Mac environment.

The preliminary compiled 100-cell Sod runner completed 93 steps to t=0.2.
Maximum CFL was 0.4500000000000001; minimum density 0.125 and pressure 0.1.
Mass/momentum/energy boundary-balance residuals were approximately
1.53e-15, 2.78e-17, 3.45e-15. All 300 final state words exactly match the
independent host design calculation. The external script and JSON preserve
this runtime regression; grid WAT, bytes, and runner proofs remain pending.

The opaque-record correction passes Project.EulerGridStep.Safety in 2.6s
(3,070 jobs). The accepted-cell theorem audits to propext, Classical.choice
and Quot.sound; prefix preservation to propext and Quot.sound. No admitted
proof is present. An inline Node documentation edit failed at JavaScript
parse time because of a template-literal fence escape; it made no edits.
Applied the bounded edits with apply_patch after a fresh status check.
Added a README spelling out the remaining payload, scan, WAT, byte and
runner boundaries, registered the focused test/source build in run_all
without running that aggregate, imported Safety in Project, and synchronized
plan/devnotes. Complete source/package inventories remain 32/28.

Grid source/model checkpoint gates: 31 focused compiled vectors pass;
Safety builds with accepted standard axioms; 91 maintained Markdown files
and all new README links pass; JavaScript syntax and git diff --check pass.
Registry/aggregate import metadata checks pass without building the aggregate.
No source or frozen-package count changes. Reviewed explicit staging intent:
- LeanExe/Examples/EulerGridStep.lean
- proofs/talos/lean/Project/EulerGridStep/Model.lean
- proofs/talos/lean/Project/EulerGridStep/Safety.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- test/euler_grid_step.js
- test/run_all.js
- proofs/talos/lean/Project.lean
- plan.md
- plans/euler-rusanov.md
- devnotes.md
- journal.md

Published grid source/model checkpoint 64a28d5145be90bbc19831e9d04a543e9e303120,
sole parent 12a2dda2bf28bed106e29e58ab89798d185d0a05, tree
b0dfb346f2c453f8c97a03cf6fd0acffd96ce8c2. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed; the
branch was clean and synchronized. Added a separate Payload proof boundary
for six field writes and preservation by later iterations. Its first focused
build is pending; no grid output safety claim is made before it passes.

The first Payload build failed in 29 seconds. Field zero needed normalization
of index+0 before applying the self-write lemma; the cell payload transfer
hit the heartbeat budget while reducing its concrete checked-cell term.
Preserved draft/log, normalized the zero index explicitly and generalized
the checked result before the transfer. No budget increase; failed audit
outputs containing sorryAx are not accepted evidence.

The revised Payload attempt removed the heartbeat problem, but strict simp
reported no progress on five nonzero fields. Making zero normalization
optional exposed the remaining density self-write, discharged directly by
Array.getElem!_set!_self. Payload now builds in 2.8s and both audited
theorems use only propext, Classical.choice and Quot.sound. Added Outputs
to transfer payload safety; its first 2.6s build identified missing false
Boolean coercion reduction and two explicit definition-unfolding steps.
Preserved that draft/log and corrected only those proof reductions.

Outputs now passes in 2.7s (3,072 jobs), including audits of accepted size,
cell acceptance, exact payload and per-output safety. All use only propext,
Classical.choice and Quot.sound. The source and compiled vectors are
unchanged, so no repeated runtime regression is needed for this pure-proof
checkpoint. Updated README, Project import and plans/devnotes to distinguish
proved payload safety from pending scan, WAT and byte obligations.
Explicit reviewed staging intent:
- proofs/talos/lean/Project/EulerGridStep/Payload.lean
- proofs/talos/lean/Project/EulerGridStep/Outputs.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project.lean
- plan.md
- plans/euler-rusanov.md
- devnotes.md
- journal.md

Payload checkpoint review: diff whitespace, all new README links, 91
maintained Markdown files, registry/import metadata and no-admission source
checks pass. No broad regression or release gate was run.

Published payload checkpoint 741bd65380cb962b9723b9094d9e82fca40aea83, sole
parent 64a28d5145be90bbc19831e9d04a543e9e303120, tree
b0ed5f20fd791d642b2449f0907e456491f2eeb2. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed, with
clean synchronized status. Added a model scan-bound module. Its first
focused build identified that UInt64 order needs its explicit core lemmas
and toNat bridge, not generic preorder/omega inference. Preserved the draft
and log; corrected those boundaries and the Boolean shape reduction.

The scan-order build passes in 2.7s; one unnecessary tactic-sequencing
warning was removed by explicit UInt64 reflexivity and comparison cases.
The final focused rebuild also passes in 2.7s without local warnings.
scan_bounds audits to propext/Quot.sound; maxSpeed_safe to propext,
Classical.choice and Quot.sound. Updated docs and Project imports; no source
or runtime change requires repeating compiled vectors. Reviewed stage paths:
- proofs/talos/lean/Project/EulerGridStep/Scan.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project.lean
- plan.md
- plans/euler-rusanov.md
- devnotes.md
- journal.md

Scan checkpoint review passes whitespace, all README links, 91 maintained
Markdown files, registry/import metadata and no-admission source checks.
No broad regression or release gate was run.

Published scan-model checkpoint dfe2964f5b374ac4dd93b31b12bd92a9fec4da35,
sole parent 741bd65380cb962b9723b9094d9e82fca40aea83, tree
476508fe325b5dcf03b7f61f11e22ab4e0910a67. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronized status. Inspection of the retained scan WAT found
multiple checked-side call sites in the expanded loop and 93 local slots.
Preserved the source and introduced scanAt as a named iteration, returning
a CheckedSpeed record carried by the loop. Model behavior is unchanged:
the first rejection returns one/zero and accepted scans fold maximum speed.
This source boundary is intended to reduce exact-loop proof duplication;
no compiler or trusted-base change is made. Focused build/runtime gates follow.

The named scan-body source builds in 212ms and all 31 compiled vectors pass,
retaining tmp/euler-grid-step-EIzYr5. Its scan entry is much smaller but
record projection in the loop guard places a getter before the conservative
helpers, shifting their function indices and preventing direct reuse of
the existing module-layout theorem. Preserved that draft and restored scalar
status/speed loop variables around the named scanAt call. This aims to keep
the dependency order while retaining the smaller call boundary. Correction:
the prior scan used 92 local variables plus its parameter (93 frame slots).

The scalar-loop source builds, and direct WAT inspection confirms the
conservative functions remain at 0–5. scanAt is function8, with one call
to checked side5; entry11 repeats a compact loop for the two result
projections. The 31-case focused rerun is pending. Registered euler_grid_scan
explicitly incomplete to prepare its exact generated module next; no
execution theorem or additional complete source case is claimed.

The scalar-loop revision passes all 31 focused cases; retained
tmp/euler-grid-step-nZTlii. Exact step bytes remain c7c0bb1425a0adb567b4b5cf96f62112181519078297fb3d4a3f5a8691695a02.
The scoped prepare euler_grid_scan gate passes using fresh staging
tmp/leanexe-talos-wtKk6r; only that invocation-owned staging was removed
by its tool. Prepared identities:
proofs/talos/lean/Project/EulerGridScan/Program.lean 32859 SHA256 8506a2ea5d5af3b0798c92a4b9c977ad5953d3bc16283bcb5c2bc6e47029d011
proofs/talos/.generated/euler_grid_scan/program.wasm 3292 SHA256 279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9
proofs/talos/.generated/euler_grid_scan/program.wat 35251 SHA256 fb2a173b45553e528fe1792337161150a6109bf06fee6bf6ddf95869382a8d90
Helper layout and runtime pins pass (3.6s and 3.7s); concreteLayout audits
to propext. Corrected the new structure syntax deprecation before its final
check. Updated runtime imports and the literal cache inventory to 33;
registry has 32 complete cases plus one explicitly incomplete scan.
A read-only docs search guessed absent docs/talos-proof-library.md; existing
README, proofs/talos/README.md and docs/status.md own these inventories.
Updated those maintained counts and documented the pending exact obligations.

Final Helpers build passes in 3.4s without new local warnings; two existing
Array proof deprecations are replayed. The small metadata/import check passes
33 registered / 32 complete; identity test and all README links pass, as do
91 maintained Markdown files. Registry formatting churn from JSON printing
was narrowed to the single reviewed addition after asserting that all prior
entries are unchanged. No aggregate execution or release gate was run.
Reviewed explicit stage paths:
- LeanExe/Examples/EulerGridStep.lean
- README.md
- devnotes.md
- docs/status.md
- journal.md
- proofs/talos/README.md
- proofs/talos/cases.json
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/Runtime/Checks.lean
- test/artifact_identity.js
- proofs/talos/lean/Project/EulerGridScan/Program.lean
- proofs/talos/lean/Project/EulerGridScan/Helpers.lean
- proofs/talos/lean/Project/EulerGridScan/README.md

Published the scan-module checkpoint 81d59be763c57245236f376ac277c9f6b585be47,
sole parent dfe2964f5b374ac4dd93b31b12bd92a9fec4da35, tree
25a3ab6b9cdf2ae0a23f3a3e927c4ef1e0112674. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed with
clean synchronized status. New Indexing lemmas pass in 3.4s, proving triple
read bounds and checked multiplication/addition guards; audited arithmetic
lemmas use propext and Quot.sound. The first incomplete iteration diagnostic
reached the initial WAT if in both index-zero cases. Preserved draft/log and
added the existing explicit-if peeling pattern to reach memory-load goals.

The explicit-if iteration diagnostic reached the first memory read in the
zero-index branch; unrestricted simp hit its recursion limit in the nonzero
branch. Preserved both draft and log, replaced it with explicit simp-only
rules, and isolated arrayRead_facts in Indexing before retry. The smaller
read-fact module builds in 3.5s and audits to propext/Quot.sound. It supplies
the exact encoded index, length comparison, byte bound and model getD word
for each of the three reads. Added those facts and nonempty length-word
evidence to the pending iteration proof; no larger recursion limit is used.

The read-fact iteration diagnostic finishes in 4.2s without recursion errors,
but simp-only leaves ground zero/nonzero tests unreduced. Retained the
draft/log. Restored the normal ground simplifications while excluding the
two ofNat distribution rules that oppose the explicit folded-word arithmetic
facts; this narrows the rewrite loop rather than increasing recursion limits.

The folded-word iteration diagnostic reaches the first element load and
next offset addition without recursion failure (7.4s). The zero case needs
its index substitution applied to all memory facts; encoded literal one/two
in the addition hypotheses need the same surface form as emitted constants.
Preserved the draft/log, made those reductions explicit, and allow the
existing linear arithmetic facts to discharge memory-bound conjunctions.

The literal-aligned iteration diagnostic reaches the second read guard
(8.4s). Normalize the zero-index facts after substitution, and fold each
addition guard with the same word equality used in the emitted frame.
The previous draft and diagnostics remain preserved.

The offset-normalized diagnostic reaches the conservative call for nonzero
indices; the zero branch reaches its third read and needs the literal-two
comparison normalized. Added the existing exact side-call theorem with an
opaque checked-side record, then composed the status and maximum branches.
Preserved the previous diagnostic source/log. This iteration proof is still
pending its final focused check.

The call-composition attempt completed every nonzero-index branch; the zero
case needed its side-model equality stated with literal indices 0,1,2.
After that correction the entire Iteration module passes in 15s (3,376 jobs)
with no new local warnings. scanAt_exact audits to propext, Classical.choice
and Quot.sound. It proves all three array reads, guarded offset arithmetic,
the checked-side call, both status/max branches and full store preservation
for any valid grid index, seed word and capacity word in a matching module.
Updated README, Project import and devnotes. Whole-loop execution remains
pending, and the case remains incomplete. Source/runtime code is unchanged
since the passing 31-vector check, so no runtime repeat is needed.
Reviewed explicit stage intent:
- proofs/talos/lean/Project/EulerGridScan/Indexing.lean
- proofs/talos/lean/Project/EulerGridScan/Iteration.lean
- proofs/talos/lean/Project/EulerGridScan/README.md
- proofs/talos/lean/Project.lean
- devnotes.md
- journal.md

Iteration checkpoint checks pass: whitespace, all README links, 91
maintained Markdown files, registry/import metadata and no-admission or
remaining diagnostic-source checks. No broad regression or release run.

Published iteration checkpoint 7036a04302ea398c3257dff55325da59d41c94cb, sole
parent 81d59be763c57245236f376ac277c9f6b585be47, tree
2ee80b5e02edea7a6fb00274b11966ba58f67f9d. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed; clean
synchronized status. Added remaining-scan composition and exit lemmas.
The first model check rewrote the wrong occurrence of scan; targeting only
the RHS fixes it. Exit arithmetic also needs the explicit negated-index
fact extracted from its conjunction. The next run showed that the corrected
rewrite closes the goal, so removed redundant trailing tactics. Both failed
logs remain. Added structural loop extraction directly from Program and a
40-local frame/invariant preserving local27 between result projections.

LoopModel now passes; the shape extraction requires all five explicit
block/loop constructor fields, including the default type lists, in patterns.
Added explicit Instruction/Option types and constructor names. A read-only
lookup guessed absent Interpreter/Wasm/Instructions.lean; discovery found
Syntax.lean, which documents those fields. Added the exact scratch-slot
updates for continuing and exiting loop bodies; neither changes Program.

LoopShape and LoopFrame pass in 3.5s/3.6s; both exact loop-shape equalities
audit to propext. The first Loop execution attempt finishes in 4.4s but
rewrites the abstract count through input.size/3, so the encoded guard no
longer matches its prepared comparison. Preserved the draft/log, derived
the required count and cell-index bounds first, and removed that rewrite
hypothesis from the local simplifier context. The loop proof remains pending.

The count-isolated loop check completes both exit branches and all memory,
call, scratch-frame and decreasing-measure obligations in 9 seconds. One
remaining invariant equality needs its target normalized by the original
hTarget, which the instruction simplifier already used. Preserved the draft
and log, made that transport explicit, and removed two unused simp arguments.

The final loop proof passes in 10s (3,380 jobs), with no new local warnings.
scan_loop_spec audits to propext, Classical.choice and Quot.sound. It is
parameterized by the following continuation, proves both exit paths and
strictly decreasing iteration measure, retains the exact modeled status/
speed, preserves the complete store and preserves local27 for the second
projection. Both copied compiler loops are definitionally the same extracted
instruction list. Updated README, aggregate import and concise notes. Entry
guards/projection composition are pending; case count remains 33 registered
with 32 complete and 28 frozen packages. No source/runtime changes require
another compiled regression. Explicit reviewed stage intent:
- proofs/talos/lean/Project/EulerGridScan/LoopModel.lean
- proofs/talos/lean/Project/EulerGridScan/LoopShape.lean
- proofs/talos/lean/Project/EulerGridScan/LoopFrame.lean
- proofs/talos/lean/Project/EulerGridScan/Loop.lean
- proofs/talos/lean/Project/EulerGridScan/README.md
- proofs/talos/lean/Project.lean
- devnotes.md
- journal.md

Loop checkpoint checks pass: whitespace, all README links, 91 maintained
Markdown files, registry/import metadata and no-admission/diagnostic source
checks. No broad regression or release gate was run.

### 2026-09-07: Exported grid-scan execution

Published loop checkpoint 10e2990acd1f71b9b901c2f310478096806beedb, sole parent
7036a04302ea398c3257dff55325da59d41c94cb, tree
db3d3a322557eea9b9a9ea9a3785eb7641eba499. Non-forced GitHub update, fetch,
commit/parent/message/tree/index/worktree equality and clean synchronization
all passed. Reread AGENTS and the operations contract after compaction;
verified the existing pinned Mac Lean and wasm-tools paths before execution.

Added EulerGridScan/Execution.lean for header guards and both result loops.
The first focused 120-second build failed in 4 seconds at the header load's
unnormalized address/bounds conditional. The draft and complete log remain.
Added a separate standard simplification step before branch composition so
the existing array read facts can apply; no source or runtime changes.
Failed elaboration's sorryAx audit is not an accepted theorem.

The normalized header load closes the full exported execution theorem in
6.5 seconds (3,381 jobs), with propext, Classical.choice and Quot.sound only.
Both compiler-generated loops instantiate the same proved continuation rule;
the first status survives the second speed projection. Added Spec.lean: both
public declarations pass in 3.5 seconds (3,382 jobs), with the same standard
axioms. The contract covers every logical array fitting memory, all shape
guards, exact status/speed, termination and complete store preservation.
AcceptedSafety transfers the model's positive finite upper bound on checked
computed cell speeds, without an exact-real wave-speed claim.

Marked the scan registration complete, imported Spec, updated the scan README,
main/status/proof inventories and both plans to 33 completed cases / 33 caches
/ 28 frozen packages. Next gate is only talos-proof check euler_grid_scan,
plus small docs/metadata/whitespace checks; no repeated runtime or broad suite.

The focused source gate passes: current compilation/WAT decoding reproduces
the tracked scan Program, then both public specifications build and audit
with standard axioms only. No Program byte changes. All 91 maintained
Markdown files, scan README links, 33/33 registry and import metadata,
whitespace and changed-proof no-admission checks pass. The complete current
source aggregate and the scan's frozen package are not claimed.
Explicit reviewed checkpoint paths:
- README.md
- devnotes.md
- docs/status.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/README.md
- proofs/talos/cases.json
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridScan/README.md
- proofs/talos/lean/Project/EulerGridScan/Execution.lean
- proofs/talos/lean/Project/EulerGridScan/Spec.lean

Published completed scan execution as 7f3ff3f553b60d19b409780c40550b5f99250863,
sole parent 10e2990acd1f71b9b901c2f310478096806beedb and tree
34f34f5659361c6ac5d82da8933efd1ccb596d28. Non-forced GitHub update, fetch,
commit/parent/message/tree/index/worktree equality and local CAS all passed;
final status was clean and synchronized. Prepared a scoped freezer for only
the scan's nine fresh package files, registry row and CheckFile arm/import.
It checks prior package and historical receipt preservation, expected path
membership, exact bytes and the unchanged normative verifier digest.

Created nine fresh grid-scan exact-package files using the output
preparer, with exclusive writes and exact expected-path membership. Added
one registry row and one CheckFile import/arm. All 28 prior manifest/WASM
pairs and the protected historical release draft remain byte-identical.
The verifier source did not change. This is pending the focused package gate.

{
  "case": "euler_grid_scan",
  "sha256": "279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9",
  "byteLength": 3292,
  "newFiles": [
    "proofs/talos/lean/Project/EulerGridScan/ArtifactBytes.lean",
    "proofs/talos/lean/Project/EulerGridScan/ArtifactCache.lean",
    "proofs/talos/lean/Project/EulerGridScan/ArtifactDecoded.lean",
    "proofs/talos/lean/Project/EulerGridScan/ArtifactRawCache.lean",
    "proofs/talos/lean/Project/EulerGridScan/ArtifactDecode.lean",
    "proofs/talos/lean/Project/EulerGridScan/ArtifactValidation.lean",
    "proofs/talos/lean/Project/EulerGridScan/ArtifactTranslation.lean",
    "proofs/artifacts/euler_grid_scan/279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9/manifest.json",
    "proofs/artifacts/euler_grid_scan/279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9/program.wasm"
  ],
  "oldPackagesUnchanged": 28,
  "protectedRelease": [
    "proofs/artifacts/release.json",
    "fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1"
  ]
}

The scan freezer completed successfully; the single-package gate is running.
Reconciled package inventories to 29 and corrected remaining stale 32-source
counts in DEVELOPMENT documentation, the second main README inventory,
language/verifying docs and both plans. Correction to the previous inventory
entry: its registry/import changes were complete, but several duplicated
prose counts were missed; this checkpoint brings all maintained counts to
33 completed source cases / 33 caches / 29 packages. Updated scan package
claims are staged only after its focused gate passes. No broader regression.

The focused scan package gate completed with exit zero. Its 3,292 embedded
bytes match; exact decoding, validation, translation, both behavioral
declaration types and axiom audits pass. Public execution and safety use
only propext, Classical.choice and Quot.sound; exact-byte native decision
witnesses remain within the existing policy. Metadata checks validate all
29 manifests and 33/33 source/import membership, all 91 maintained Markdown
files and scan README links. The final no-admission rg returned no matches
(exit 1, expected). No broad source/artifact aggregate or release gate ran.
The next grid-step boundary needs copying-array writes and ownership proofs;
read-only WAT inspection confirms six copies and five releases in writeCell.
Explicit reviewed checkpoint paths:
- DEVELOPING.md
- README.md
- devnotes.md
- docs/spec.md
- docs/status.md
- docs/verifying.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/artifacts/registry.json
- proofs/talos/README.md
- proofs/talos/lean/Project/Artifact/Binary/CheckFile.lean
- proofs/talos/lean/Project/EulerGridScan/README.md
- proofs/talos/lean/Project/EulerGridScan/ArtifactBytes.lean
- proofs/talos/lean/Project/EulerGridScan/ArtifactCache.lean
- proofs/talos/lean/Project/EulerGridScan/ArtifactDecode.lean
- proofs/talos/lean/Project/EulerGridScan/ArtifactDecoded.lean
- proofs/talos/lean/Project/EulerGridScan/ArtifactRawCache.lean
- proofs/talos/lean/Project/EulerGridScan/ArtifactTranslation.lean
- proofs/talos/lean/Project/EulerGridScan/ArtifactValidation.lean
- proofs/artifacts/euler_grid_scan/279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9/manifest.json
- proofs/artifacts/euler_grid_scan/279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9/program.wasm

### 2026-09-07: Grid writer proof boundary

Published scan package bd58550520d7ae31f26697ba9cc13920623a3dbb, sole parent
7f3ff3f553b60d19b409780c40550b5f99250863 and tree
3a44cbb437d123068dc7aaa2a504b158f331f3a3. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed; clean
synchronized status confirmed. Preserved the existing grid source externally
and factored the six accepted cell writes through writeCellField. Offset
arithmetic stays inside the helper so call arguments are total variables.
This aims to expose one reusable copy/write proof boundary, without compiler
or numerical changes. Compilation and focused 31-vector regression are next.

The field helper builds in 207ms and all 31 focused compiled grid/scan cases
pass, retaining tmp/euler-grid-step-uCXTlz. The scan remains exactly 3,292
bytes with its frozen digest. Grid step shrinks from 11,222 to 8,866 bytes,
SHA256 bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297.
Read-only inspection initially hit a JavaScript shadowed-variable error; the
corrected command confirms field write function27, writer34 (six calls27 and
five releases40), advance35, entry36 and runtime37–40. Existing cell functions
0–25 remain the reusable layout boundary. Added the explicitly incomplete
grid-step registry row, matching runtime pins/import and expected34 Program
caches. Current complete count is still33 and package count29.

The explicit grid-step preparation passes, with fresh staging
tmp/leanexe-talos-nOW1UJ and only that invocation-owned staging removed by
the tool. Program is generated, not hand edited. Added Helpers.lean to
identify the new call layout, preserve the full checked-cell proof and pin
release/memory32; its focused build and shared runtime pins are running.
Updated imports and maintained inventories to 34 registered / 33 complete /
34 Program caches / 29 frozen packages, retaining the incomplete entry claim.

Runtime pins pass in 3.8s. The first Helpers check proves cellLayout with
propext, but fails defining the extended layout because its default parent
projection toLayout collides with an inherited projection. Preserved that
draft/log and named the new parent projection toCellLayout explicitly.
This is a declaration error, not an execution failure or timeout.

The corrected layout check passes in 3.6s (3,387 jobs); cellLayout and
concreteLayout audit to propext only. Shared runtime pins passed previously
in3.8s. Program has 90,075 bytes and SHA256
c05b49f9b1dcbeeb1b17beb5477e321a48796a34bcb7c29b19125ce5c034560f;
the prepared 8,866-byte WASM matches the tested bc546b72 digest. All34/33
registry/import checks and both grid README link checks pass. The completed
model safety and scan proofs remain separate from pending grid execution.
Explicit reviewed stage intent:
- DEVELOPING.md
- LeanExe/Examples/EulerGridStep.lean
- README.md
- devnotes.md
- docs/spec.md
- docs/status.md
- docs/verifying.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/README.md
- proofs/talos/cases.json
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridScan/README.md
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/Helpers.lean
- proofs/talos/lean/Project/EulerGridStep/Program.lean
- proofs/talos/lean/Project/Runtime/Checks.lean
- test/artifact_identity.js

### 2026-09-07: Grid field memory semantics

Published writer checkpoint 52953b4a225b55d52ffcde40d14675fe2138d47f, sole
parent bd58550520d7ae31f26697ba9cc13920623a3dbb and tree
0b093024505ca3e234d8f4e524a31d6562e92b4c. Exact non-forced publication,
fetch, complete identity/content checks and local CAS passed, with clean
synchronization. Its 91-doc/whitespace checks and no-admission scan also pass.

Added FieldMemory: a payload store realizes Array.set! and preserves a
disjoint input array. The first build fails only on the remaining array
read simplification (missing its bounds hypothesis); disjoint-array
preservation already audits to propext and Quot.sound. The same-address
read used CodeLib's bv_decide theorem, whose native certificate is outside
the agreed new public execution axiom set. Preserved the draft and replaced
that dependency with a separate WordRoundtrip bitwise kernel proof, currently
checking; no dependency or trusted-base change. A read-only BVDecide lookup
guessed an absent Elab directory; discovery found Std/Tactic/BVDecide/Syntax
and Lean/Meta/Tactic/BVDecide instead.

The first isolated round-trip check hit an incorrect lemma name; replaced
UInt64.toBitVec.inj with the verified core UInt64.toBitVec_inj.mp API.

The bitwise check then rejected an attribute name used as a simp lemma.
Replaced it with the explicit verified UInt64/UInt8 conversion lemmas;
the failed draft and log remain. No timeout or resource-limit change.

The explicit bitwise round-trip proof passes in8 seconds and audits to
propext, Classical.choice and Quot.sound. FieldMemory then passes in3.7s;
added and checked its exact outside-word byte footprint, also in3.7s.
No new theorem depends on the old native read-back certificate. Reduced
WordRoundtrip imports to array memory plus IntervalCases so these generic
facts do not depend on any Euler numerical or generated-module definitions;
one focused build checks that smaller import boundary. Added aggregate
import, README explanations and concise notes.

The isolated memory boundary passes (3,345 jobs): WordRoundtrip8.1s and
FieldMemory3.7s, with only the audited standard axioms. All91 maintained
Markdown files, grid README links, registry/import metadata and whitespace
checks pass. No source/runtime changes or repeated compiled regression.
Review/stage exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/FieldMemory.lean
- proofs/talos/lean/Project/EulerGridStep/WordRoundtrip.lean

### 2026-09-07: Copy-loop invariant

Published memory checkpoint 1233f0a591c9f3b8c3108e8858bb6a7f4dad5085, sole
parent 52953b4a225b55d52ffcde40d14675fe2138d47f and tree
07d84e6ad108456a45aa20ff4c1052ebf220e8f2. Non-forced update, fetch,
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. A read-only Store.lean lookup guessed an
absent file; no mutation resulted. Added CopyModel.lean with an invariant
for exact prefix copying, both logical arrays, unchanged non-memory store
fields and bytes outside the destination payload. Its initial, one-write
step and completed-copy conclusions are the next focused target.

The first CopyModel check hit the reserved syntax name prefix as a field;
renamed it copied and exposed the size equality to omega before arithmetic.
The initial failed draft and diagnostics remain.

CopyModel passes in3.5s with standard axioms. CopyFrame passes in3.6s; it
reuses the existing counter-frame lemmas and proves a general encoded-address
identity with propext only. The first CopyLoop check completes its exit branch
but needs the load/store bounds stated with the same wordAddress spelling
as the instruction goal. Preserved the draft/log, made those two conversions
explicit and used the current conditional rewrite names.

The corrected CopyLoop check passes in6.1s (3,349 jobs, mostly cached),
log euler-grid-copy-loop-addresses.log. Its exact terminating execution
theorem reports only propext, Classical.choice and Quot.sound. Exit and
advance paths both pass, retaining the complete non-memory store and outside
bytes. Added FieldShape.lean to identify the exact generated function27
copy region by definitional equality; updated aggregate imports, README,
plan.md, plans/euler-rusanov.md and devnotes.md. No source/runtime change.

The first FieldShape check selected the false branch when extracting iff
(the scan example used a false-branch valid case). The definitional equality
correctly rejected it. Preserved that draft/log and selected the field
writer's true branch explicitly; the copy-loop proof itself remains accepted.

FieldShape now passes in3.6s with propext only; the exact emitted copy
region equals the proved program. All91 maintained Markdown files, case
README links, registry/import metadata, no-admission scan and whitespace
checks pass. No compiled runtime suite was repeated for this proof-only
checkpoint. Review/stage exactly:
- devnotes.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/CopyModel.lean
- proofs/talos/lean/Project/EulerGridStep/CopyFrame.lean
- proofs/talos/lean/Project/EulerGridStep/CopyLoop.lean
- proofs/talos/lean/Project/EulerGridStep/FieldShape.lean

### 2026-09-07: Field-write tail after allocation

Published copy checkpoint db53437535e25f777bc30c2e101a3f0b090957b2, sole
parent1233f0a591c9f3b8c3108e8858bb6a7f4dad5085 and tree
6974c1625da407c0c15a5a8f51e04ceb133fb9d4. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree comparisons and local CAS passed;
clean synchronization confirmed. A read-only dependency search guessed an
absent root .lake/packages/CodeLib path; no mutation resulted. No additional
dependency source is needed for this step. Added HeaderMemory.lean to prove
that a length-header write creates a represented array over arbitrary existing
payload bytes, preserves a disjoint source and has an exact byte footprint.
The next composition will discharge the generated writer tail after allocation.

HeaderMemory passes in3.5s with standard logical axioms. Added
FieldTailModel.lean to combine a completed copy and one field store into
an exact logical-update/post-memory contract. FieldTail.lean extracts and
composes the complete generated post-allocation region, including its returned
pointer. It requires only region bounds, source separation and the live
locals; allocation remains a separate pending obligation.

FieldTailModel passes in3.5s, including its full state/frame audit. The
first exact-tail check accepts the generated shape but stops at the wrapped
header address: the goal spells its modulus as2^32 and the shared lemma as
4294967296. Preserved the draft/log and gave that identity the goal's exact
spelling before rewriting. No timeout or budget change.

The wrapped-address correction reaches the final continuation; its sole
remaining mismatch is the opaque writeWord spelling versus the expanded
physical store. Preserved this draft and unfolded writeWord in that final
simplification. All header, copy and final-store bounds already elaborate.

FieldTail passes in3.9s (3,354 jobs, mostly cached), log
euler-grid-field-tail-store.log. Generated-shape equality uses propext;
exact tail execution uses only propext, Classical.choice and Quot.sound.
The result includes the returned pointer, exact Array.set! contents, source
preservation and full outside/store frame. Added aggregate import and README
links; no source, byte artifact or runtime regression changes.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission scan and whitespace checks pass. Stage/publish exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/HeaderMemory.lean
- proofs/talos/lean/Project/EulerGridStep/FieldTailModel.lean
- proofs/talos/lean/Project/EulerGridStep/FieldTail.lean

### 2026-09-07: Fresh field allocation

Published field-tail checkpoint00a2f02b373bc14c3053d277688884442702e08d,
sole parentdb53437535e25f777bc30c2e101a3f0b090957b2 and tree
13a2800a388124581a23e7bda2ce6c3271ef3b34. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed; clean
synchronization confirmed. Added FieldAllocationBump.lean, adapting the
checked allocator-window proof to the exact field function's five parameters,
20 locals and return-pointer slot14. It reuses shared allocation arithmetic,
search/bump instruction definitions and store model. Its explicit scope is
empty free list and sufficient existing memory; buffer reuse remains pending.

The first allocator check built missing shared dependencies (Allocation3.6s,
FixedArrayAllocator23s, Capacity2.9s, Window31s), then failed its shape
equality and reached the recursion limit at the third header store. No
timeout occurred. A read-only instruction comparison identifies the exact
difference: generated bump uses localTee22 where the older helper uses
localSet22/localGet22. The i32 failure constant also has signed spelling
(-1), representing the same word. Preserved the failed draft/log. Added
HeaderStores.lean to isolate constant/local header stores with opaque store
results and complete local-frame preservation before retrying composition.
No recursion/heartbeat/time budget was increased.

The isolated HeaderStores check passes in3.4s with standard axioms. Removed
one reported unused simp argument. Added AllocationHeader.lean: its bump body
is extracted directly from generated WAT, its six metadata stores compose
through the small accepted store theorems, and the emitted allocation-region
equality now preserves localTee22. This isolates header execution before the
fresh-allocation proof is retried.

AllocationHeader passes in4.7s: both exact generated shapes use propext,
and the six-store execution theorem uses the standard three logical axioms.
Reworked FieldAllocationBump to call that accepted theorem, preserving the
actual emitted tee instruction and replacing the deep inline six-store
simplification with one opaque continuation boundary. Recursion remains16384
and the command timeout remains120s.

The isolated allocator retry reaches a no-progress simplification before the
overflow guard, with no recursion failure. Preserved the draft and added
one goal trace at that exact boundary to inspect the remaining program.

The trace shows the extracted generated list still suspended at getElem?0.
Selected the existing wp_alloc_window_lists variant, which supplies both
cons-index reductions, and removed the temporary goal trace after preserving
it and its log. This is a list-normalization correction, not allocator logic.

List normalization now completes the emitted search, overflow and no-growth
branches and reaches the accepted header-store theorem. Its remaining
continuation is the enclosing iff return, rather than the outer Q directly.
Preserved the draft/log and retained that inferred continuation while applying
the header theorem with an empty inner remainder.

The next diagnostic isolates the remaining boundary mismatch to the operand
stack: the emitted header frame has an empty stack, while fieldBumpFrame
inherited the original stack propositionally. Preserved the draft/log and
made the empty stack explicit in that result-frame definition.

The explicit frame reaches the final exact-store comparison. Broad
simplification normalized metadata addresses into UInt32 arithmetic, unlike
the shared store model's natural-offset spelling. Preserved the draft/log
and used a globals-only header projection in the return-path simplifier,
keeping header memory opaque until the final explicit address conversion.

The globals-only projection preserves exact header addresses and leaves
only the allocator-count read beneath the heap-top global update. Preserved
this draft/log and added that separate unchanged-slot read equality to the
final explicit simplification. The execution and store-shape goals agree.

The corrected fresh-allocation theorem passes in7.4s, log
euler-grid-field-alloc-bump-count.log (3,359 jobs, mostly cached). Its axiom
audit is exactly propext, Classical.choice and Quot.sound. The emitted tee
and six header stores are pinned; exact state includes the heap-top and
allocation-count updates plus every other original store field. All earlier
failed drafts/logs remain. Added aggregate import, README and concise notes.
The source/binary and runtime regressions are unchanged; free-list reuse
and ownership transfer remain explicit pending work.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/HeaderStores.lean
- proofs/talos/lean/Project/EulerGridStep/AllocationHeader.lean
- proofs/talos/lean/Project/EulerGridStep/FieldAllocationBump.lean

### 2026-09-07: Allocation metadata and ownership

Published fresh-allocation checkpointba7d34131ee5cc33532d0e441d13e262c058aa65,
sole parent00a2f02b373bc14c3053d277688884442702e08d and tree
79f0e945de88054c39a7a039c15e590b74dd47e9. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed; clean
synchronization confirmed. Added ArrayFrame.lean for byte-preserving logical
array transfer, plus AllocationMemory.lean for exact owned metadata, its
48-byte footprint, disjoint-array preservation and preservation of metadata
through the already-proved field-write tail. Read-back proofs explicitly use
the kernel word round-trip theorem, never the older native witness.

The first ArrayFrame build hits the default recursion limit in an omega call
for page-count monotonicity. Preserved the draft/log and replaced that search
with direct transitivity and Nat.mul_le_mul_right, isolating the arithmetic
from the byte-frame context without increasing any resource limit.

ArrayFrame passes in3.7s with propext and Quot.sound. AllocationMemory
already proves metadata preservation through field writes, but the repeated
read/byte frame rewrites leave constant UInt64.toNat offsets opaque to omega.
Preserved the draft/log and gave the six offset equalities explicit natural
literal result types before those arithmetic rewrites.

AllocationMemory passes in3.8s. Exact metadata read-back uses the standard
three axioms; the outside-byte, disjoint-array and field-preservation
theorems use propext and Quot.sound only. Added Release.lean to instantiate
the existing scalar-array runtime theorem at exact grid function40 using
OwnedHeader and represented-array facts. Its full axiom audit is the next
focused gate; no new release algorithm or source change is introduced.

Release passes in3.8s (3,410 jobs, mostly cached), log
euler-grid-release-owned-first.log. Its exact function40 execution theorem
uses only propext, Classical.choice and Quot.sound; the existing runtime
proof can be reused without expanding the trusted base. It specifies exact
release memory, free-list and counter results, without claiming preservation
of other store fields beyond that existing theorem. Added aggregate import,
README explanations and concise notes. No source/binary/runtime changes.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/ArrayFrame.lean
- proofs/talos/lean/Project/EulerGridStep/AllocationMemory.lean
- proofs/talos/lean/Project/EulerGridStep/Release.lean

### 2026-09-07: Reusing a suitable free-list head

Published ownership/release checkpoint888fec522a1cb31389b728ab48f280993e66a62b,
sole parentba7d34131ee5cc33532d0e441d13e262c058aa65 and tree
880163a03d9e73ea610d96e2ebb54afcef64a347. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed; clean
synchronization confirmed. The reuse path resets the same six metadata fields
but reads root/capacity from locals21/22, rather than24/19. Generalized the
accepted header program/theorem over those two indices and retained the
existing field theorem as a specialization, with unchanged emitted shapes.

The generalized header theorem passes in4.5s with standard logical axioms;
all existing generated shapes remain definitionally equal. Added ReuseHit.lean
for the exact successful first-candidate branch: unlink the head, execute
those six header writes through locals21/22, and select the resulting pointer.
The outer search still must establish candidate capacity and execute its
loop/return path.

ReuseHit passes on its first check with standard logical axioms; removed
one reported unused simp argument. Added ReuseSearch.lean with two exact
loop states (before and after selecting the head) and a one-to-zero measure.
It requires that the head capacity covers the request, reads only that head,
and composes the accepted unlink/reset/select theorem. Other free-list
search cases are outside this theorem's explicit scope.

The first ReuseSearch check normalizes both header loads and their values;
only their two in-bounds conditionals remain before the candidate branch.
Preserved the draft/log, explicitly rewrote those guards using the proved
bounds, and made store/frame substitution directions explicit so the
original initial-store name remains available to the continuation.

The bounded-load retry proves the successful iteration, selected-state
invariant and decreasing measure. The exit branch retains a concrete
i32-one branch match; preserved the draft/log and used ordinary simplification
at that final continuation to reduce the known tag/value comparison.

ReuseSearch passes in5.3s with standard logical axioms; it selects a
sufficient head in one successful iteration, then exits, preserving the
exact resulting store and local frame. Removed one reported unused simp
argument. Added FieldAllocationReuse.lean to compose initialization, this
search, the skipped bump branch, allocation counter and returned-pointer
slot for the entire exact emitted allocator region.

FieldAllocationReuse passes on its first check in3.0s, log
euler-grid-field-allocation-reuse-first.log. The same focused build rebuilds
the affected fresh-allocation proof in7.2s and search in5.3s; all axiom audits
are standard. The focused Release dependency check also passes in3.9s, log
euler-grid-release-generic-header.log, validating the existing metadata and
release users of the generalized header theorem. No source/runtime changes,
aggregate runs or repeated compiled regressions. Added aggregate import,
README explanation and concise notes.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/AllocationHeader.lean
- proofs/talos/lean/Project/EulerGridStep/ReuseHit.lean
- proofs/talos/lean/Project/EulerGridStep/ReuseSearch.lean
- proofs/talos/lean/Project/EulerGridStep/FieldAllocationReuse.lean

### 2026-09-07: Field index and capacity setup

Published reuse checkpoint006f97c81a05894324ba1c7b0c21accd06314f92, sole
parent888fec522a1cb31389b728ab48f280993e66a62b and tree
e3960c55de2377312e139e839da69fe8019e84ab. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed; clean
synchronization confirmed. Added FieldIndexing.lean for the checked six-word
offset multiplication, bounded additions, encoded field index and exact
rounded/normalized scalar-array capacity. These provide the arithmetic
preconditions for joining field setup to the accepted allocator/tail proofs.

The first arithmetic check accepts both overflow guards. Generic reverse
rewrites fail to infer natural literal factors from UInt64 numerals in the
index/capacity equalities. Preserved the draft/log and instantiated the
conversion equalities explicitly before using them; arithmetic assumptions
and resource limits are unchanged.

FieldIndexing passes in3.5s: guards/capacity use propext and Quot.sound,
and encoded index equality uses propext. Added FieldPrefix.lean to execute
the first44 emitted instructions, including zero-index handling, all checked
arithmetic guards and the length-header read, ending at the true array-bound
condition with an exact20-local frame. This target is independent of
allocator ownership composition.

The first FieldPrefix check stops at addition guards normalized by the
interpreter simplifier into equality with zero. Preserved the draft/log;
added explicit nonzero offset/destination facts in both encoded and emitted
spellings, plus the corresponding encoded second-addition guard. Their
natural bounds already follow from the valid field index.

The nonzero-index prefix now reaches the correct final frame behind only
the explicit header-load bound. The zero branch needs its specialized raw
nonzero destination fact normalized after substitution. Preserved the
draft/log and added those two local reductions to the existing proof steps.

The next FieldPrefix check completes the nonzero path; the zero path now
only needs its specialized final in-bounds comparison. Preserved the draft/log
and added that normalized fact. Added FieldCapacity.lean for the exact
22-instruction count/capacity setup, generic in the raw length word; its
physical byte-count interpretation is supplied separately by FieldIndexing.

FieldPrefix passes in6.8s with standard logical axioms. FieldCapacity has
a record-field continuation indentation error; its failed parser recovery
is not an accepted proof. Preserved the draft/log and placed the complete
local-set expression on one field line before checking it again.

FieldCapacity passes in3.8s with standard logical axioms, log
euler-grid-field-capacity-record.log. Together with the6.8s FieldPrefix
check, both setup regions now have exact frame/store contracts. Added
aggregate imports, README links and concise notes. A read-only generated-call
inspection confirms function34 performs all six field calls27 before its
five releases40; function35 calls25/34, and entry36 calls0/35/40. Thus an
accepted cell can keep seven output buffers live before release, and the
upcoming arena invariant must budget for that actual ordering. This is code
inspection for proof planning, not a new complete memory/execution claim.
No source/runtime changes or compiled regression reruns.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/FieldIndexing.lean
- proofs/talos/lean/Project/EulerGridStep/FieldPrefix.lean
- proofs/talos/lean/Project/EulerGridStep/FieldCapacity.lean

### 2026-09-07: Allocation postconditions for the field tail

Published setup checkpoint735b60f1838d9361e063a5e02ea6b3ad2c09bdda, sole
parent006f97c81a05894324ba1c7b0c21accd06314f92 and tree
aeabd7f46bf6c7e616603b51dfff3e9297b2fdad. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed; clean
synchronization confirmed. Added AllocationPost.lean: a shared postcondition
for fresh/reused regions (represented source, owned header, destination bounds,
pages and outside bytes), exact memory bridges from both allocation models,
and the combined allocation/payload object footprint.

AllocationPost passes in3.5s, all four audited theorems use only standard
logical axioms (log euler-grid-allocation-post-first.log). After compaction,
reread AGENTS.md and the operating contract and validated the pinned Darwin
Lean, wasm-tools, Wasmtime and Node paths; no toolchain replacement. Added
AllocationChoice.lean to give the two already-proved allocator paths one
explicit capacity/separation contract and common exact execution interface.

AllocationChoice's first check passes the memory bridge and fresh execution;
the reuse comparison rewrite does not unfold the emitted greater-or-equal
relation. Preserved the draft/log and changed that local goal directly to
its natural-number comparison. A read-only search also guessed a missing
EulerConservativeCell path; rediscovery locates EulerCellStep/Execution.lean.
No absent path or dependency was changed.

AllocationChoice passes in3.7s with only standard logical axioms, log
euler-grid-allocation-choice-comparison.log. Added FieldFrame.lean for the
allocator input shape and preservation of every live tail local under either
allocation path. These are frame facts over the exact emitted slot layout.

FieldFrame passes in4.0s, with propext/Quot.sound or propext alone. Added its
aggregate import and README/notes for all three modules. Reviewed the new
proofs, capacity and separation assumptions, exact emitted-frame mappings,
and standard axiom audits together with the short build telemetry. No source,
binary, dependency or trusted-base changes, so runtime reruns are unnecessary.
The remaining whole-function theorem can now consume these small contracts.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/AllocationPost.lean
- proofs/talos/lean/Project/EulerGridStep/AllocationChoice.lean
- proofs/talos/lean/Project/EulerGridStep/FieldFrame.lean

### 2026-09-07: Complete field-writer composition

Published allocation-contract checkpoint568409a73f106d6162fb70413d6511d5c5e72696,
sole parent735b60f1838d9361e063a5e02ea6b3ad2c09bdda and tree
c1e5831f568f389ff772e1874501ee3a14757436. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added FieldBody.lean to compose the exact
capacity, allocation and copy/update regions under the established contracts.

FieldBody passes in3.5s, standard logical axioms, log
euler-grid-field-body-first.log. Added FieldExecution.lean to connect the
checked index prefix, accepted branch and two-pointer function return, with
exact logical update, owned result metadata, unchanged pages and outside
object bytes. Its preconditions retain explicit allocation availability,
capacity, separation and the existing-memory limit.

The first FieldExecution check accepts the shape and result/footprint facts;
the outer generated if carries an explicit i64 result-type annotation, while
the structural rule matches the default annotation. Preserved the draft/log
and inserted the existing wp_iff_control_types semantic equality before the
structural rule. No generated program or dependency was changed.

The annotation correction reaches the six final return instructions. Their
simplification rewrites counter-frame lengths to the underlying allocation
frame, so added those already-proved underlying lengths and exact result
arity to the local simplifier. Preserved the prior draft/log; no resource
limit increase and no theorem-precondition change.

The return instructions now simplify completely, including the pointer pair;
the final goal is the already-proved FieldResult alone. Preserved that draft
and changed the closing proof from a redundant pair constructor to hResult.

FieldExecution passes in3.9s, log euler-grid-field-execution-result.log;
writeCellField_exact_in_module and field_result_of_write audit to propext,
Classical.choice and Quot.sound only. The checked subject is exact generated
function27 under bounded index and explicit FieldAllocation.Valid conditions,
not arbitrary free-list traversal or memory growth. Reviewed the theorem,
preconditions, object footprint and short telemetry together. Added aggregate
import and README links, updated both maintained Euler agendas and concise
notes. No source/runtime changes; no compiled or broad aggregate rerun.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/FieldBody.lean
- proofs/talos/lean/Project/EulerGridStep/FieldExecution.lean

### 2026-09-07: Preserving other live grid buffers

Published full-field checkpoint50a1917f574f50ef5653e9f6613306f6ea8509b8,
sole parent568409a73f106d6162fb70413d6511d5c5e72696 and tree
29e709c46e2f0f1a88b4b610137f418a3a47b28b. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added ObjectFrame.lean for full object
separation (including runtime metadata), metadata transfer across byte frames,
and preservation of other live headers/payloads by the full field theorem.

ObjectFrame passes in3.5s; its metadata and payload preservation theorems use
only propext and Quot.sound. Added ReleaseMemory.lean for the two exact
release writes, free-header read-back, unchanged payload/page count and
preservation of other separately allocated live headers and arrays.

ReleaseMemory passes in3.6s with only standard logical axioms, log
euler-grid-release-memory-first.log. Added FreeFrame.lean to preserve other
free-list nodes across cloning/release, and ReleaseFramed.lean to attach all
memory postconditions to the existing exact release call theorem. The
release theorem still specifies exact memory/globals and derived framing;
it does not assert an unproved equality of every Store field.

FreeFrame passes in3.7s (propext/Quot.sound); ReleaseFramed passes in3.8s
(standard three logical axioms), log euler-grid-release-framed-first.log.
Reviewed all four accepted proofs, standard audits and short telemetry:
full object separation protects both owned metadata and free-chain links,
while the release memory model touches only its two runtime header words.
Added the aggregate import and README/notes. No source/binary/runtime changes,
no dependency or trusted-base expansion and no broad regression rerun.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/ObjectFrame.lean
- proofs/talos/lean/Project/EulerGridStep/ReleaseMemory.lean
- proofs/talos/lean/Project/EulerGridStep/FreeFrame.lean
- proofs/talos/lean/Project/EulerGridStep/ReleaseFramed.lean

### 2026-09-07: Uniform free-buffer chains

Published buffer-frame checkpoint99961e75b01cde0a5e249ac942774511a5041e99,
sole parent50a1917f574f50ef5653e9f6613306f6ea8509b8 and tree
dee4509359ccc9926cb45b909a779f61b8d476ca. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added FreeChain.lean for finite uniformly
sized free buffers with header links and physical bounds, preservation by
separate operations, conversion of the first node into actual allocation
preconditions, and adding a released buffer to the preserved chain.

FreeChain passes in3.6s; all five audited theorems use only propext and
Quot.sound, log euler-grid-free-chain-first.log. Added FreeChainExecution.lean
to attach chain consumption/extension and exact runtime-global updates to
the proved full field and release functions. Pairwise separation remains an
explicit caller obligation; the list predicate alone does not assert it.

The first FreeChainExecution check accepts release/chain composition. The
field-global projection needs a local congrArg fact before reducing away the
memory-only record update; direct expected-type inference instead asked for
full Store equality. Preserved the draft/log and isolated that projection.

FreeChainExecution passes in3.9s, standard logical axioms, log
euler-grid-free-chain-execution-globals.log. Added LiveBuffers.lean to track
uniform-size owned arrays, preserve an entire separate live list through
cloning/release, and prepend the exact updated clone. This avoids manually
repeating header/payload preservation for every intermediate buffer.

LiveBuffers passes in3.7s, all four theorem audits use propext/Quot.sound,
log euler-grid-live-buffers-first.log. Reviewed the accepted chain/live-list
proofs and short telemetry together. Shared list contracts eliminate repeated
per-buffer framing while keeping physical bounds, exact contents and
separation obligations visible. Added aggregate import and README/notes.
No source, runtime, dependency, binary or trusted-base changes; no broad
regression or current aggregate run.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/FreeChain.lean
- proofs/talos/lean/Project/EulerGridStep/FreeChainExecution.lean
- proofs/talos/lean/Project/EulerGridStep/LiveBuffers.lean

### 2026-09-07: Buffer state across successive calls

Published buffer-list checkpointbcc8cedf51457f180fdb9cd1eaeb3d2a86714c47,
sole parent99961e75b01cde0a5e249ac942774511a5041e99 and tree
580386211e51d8e60255ec387b5142e26e50d6fb. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added BufferState.lean to combine the live
arrays, bounded free chain, head pointer, allocation/release/free counters
and page limit. Exact clone/release transitions preserve this combined state
under explicit source/live/free separation conditions.

The first BufferState check reduces the call/state contracts and leaves only
three direct global-list index bounds (1,2,5 below its length). The existing
frees-counter read already proves length greater than5. Preserved the draft/
log and discharged the remaining arithmetic after simplification.

BufferState passes with standard logical axioms, log
euler-grid-buffer-state-indices.log. Added CellPrefixes.lean to name the six
successive logical array updates, equate the sixth with Model.putCell, and
track the corresponding newest-first live-buffer list. Membership and
separation facts connect that list to fixed physical buffer roots.

BufferState's successful build is3.9s. CellPrefixes accepts the size, exact
six-update identity, membership decomposition and separation facts; the
zero-case membership proof has a one-line tactic-scope error. Preserved its
draft/log and separated the local equality, substitution and closing step
onto distinct lines. No proof assumptions or budgets changed.

CellPrefixes passes in3.7s with propext or propext/Quot.sound, log
euler-grid-cell-prefixes-scope.log. Added CellFieldCall.lean: any one of the
six exact field calls advances the corresponding logical prefix and live/
free/counter state. The seven relevant buffer roots require explicit pairwise
object separation; remaining free-tail separation is also retained.

CellFieldCall passes in3.6s with the standard three logical axioms, log
euler-grid-cell-field-call-first.log. Reviewed the BufferState, CellPrefixes
and field-stage proof interfaces with their short telemetry: each stage
consumes one distinct free buffer and preserves all earlier live prefixes;
no interleaved release is assumed. Added aggregate import and README/notes.
No source/binary/runtime changes, no new dependency or trusted axiom, and no
broad regression or current aggregate run.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/BufferState.lean
- proofs/talos/lean/Project/EulerGridStep/CellPrefixes.lean
- proofs/talos/lean/Project/EulerGridStep/CellFieldCall.lean

### 2026-09-07: Generated cell-writer call stages

Published cell-field-stage checkpoint3aab80780b900ae6eb8bce249c5d954daed90601,
sole parentbcc8cedf51457f180fdb9cd1eaeb3d2a86714c47 and tree
58dea63348b2ed6e26474b38bb023531d58cc580. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added WriterShape.lean to identify the exact
accepted/rejected outer branches, first field call, five uniform subsequent
call stages, and the release tail after instruction126. These equalities are
checked against the generated Program; no generated content is hand-edited.

The first WriterShape check confirms the10-parameter/72-local frame, but
branch extraction needs an explicit Option Wasm.Instruction type, as in the
existing FieldShape module. Preserved the failed draft/log and added that
type plus the qualified constructor before checking the generated equalities.
The parser-recovery axiom reports are not accepted proof audits.

Typed WriterShape accepts the outer branch and frame facts, but the combined
six-stage equality reaches the default recursion boundary. Preserved that
draft/log and replaced the single expansion with six separate exact equalities:
the first16 instructions, then five22-instruction stages. Each keeps the
remaining generated tail opaque at a concrete drop boundary. No recursion
limit or timeout increase; no unchanged failing target retry.

The split shape check accepts stages0–4; only the deepest stage5 equality
still reaches the default recursion boundary while reducing its whole tail.
Preserved the draft/log and isolated its22-instruction prefix as a closed
kernel-decided equality, then derived the full tail equality using the generic
List.take_append_drop and List.drop_drop lemmas. The same default recursion
limit and120s timeout remain unchanged; no native decision is used.

The smaller prefix check cannot use decide because this instruction type has
no DecidableEq instance. Its generic tail reconstruction is accepted. Preserved
the draft/log and checked just the isolated22-instruction prefix by rfl;
the problematic full-tail definitional comparison remains eliminated.

WriterShape passes in3.9s at its unchanged default recursion limit, log
euler-grid-writer-shape-prefix-rfl.log. All outer/stage equalities use
propext; the frame shape uses no axioms. Added WriterCalls.lean for the
first-call setup and the five uniform local handoff stages, each composing
an explicit terminating field-call contract with its exact resulting frame.

The first WriterCalls check executes every local/call stage and reaches its
continuation. The resulting frame comparison needs the explicit unchanged
parameter list, and the next-stage model must store the returned second slot
before the first, matching the emitted localSet order. Preserved the draft/
log, corrected that model order and supplied the parameter-list equality.

WriterCalls passes in4.1s with the standard three logical axioms, log
euler-grid-writer-calls-frame.log. Added WriterFrames.lean to name the exact
frame after each completed field call and prove preserved parameter/local
shape and the expected pointer-pair stack. These frame facts support composing
the six checked stages without unfolding their accumulated local updates.

WriterFrames passes in3.7s with propext only, log
euler-grid-writer-frames-first.log. Added WriterCopies.lean to compose all
six emitted call stages with the checked buffer-state transitions, retaining
seven live arrays and advancing allocation count by6 before entering the
release tail. The proof keeps explicit slot and remaining-free-chain
separation assumptions and reuses the small frame lemmas at each boundary.

The first WriterCopies check composes the six stages and leaves only explicit
normalization of the UInt64 allocation-counter constants1+1 through5+1.
Preserved the draft/log and supplied five small kernel-decided word equalities
alongside associativity. No execution, storage or separation assumption changed.

WriterCopies passes in3.7s with propext, Classical.choice and Quot.sound,
log euler-grid-writer-copies-counters.log. Reviewed its exact six-call shape,
slot/free-chain assumptions, seven-live-buffer postcondition, frame/counter
transitions and short telemetry alongside the supporting proofs. Added the
aggregate import and README/notes. The source and generated binary are
unchanged; no runtime, broad regression or current aggregate rerun is needed.

All91 maintained Markdown files, registry/import metadata, grid README
links, no-admission/no-trace scan and whitespace checks pass. Stage/publish
exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/WriterShape.lean
- proofs/talos/lean/Project/EulerGridStep/WriterCalls.lean
- proofs/talos/lean/Project/EulerGridStep/WriterFrames.lean
- proofs/talos/lean/Project/EulerGridStep/WriterCopies.lean

### 2026-09-07: Intermediate cell-buffer releases

Published six-call checkpointc6c174ea9029aab35e793bf96f7d4cdf7aa67b6d,
sole parent3aab80780b900ae6eb8bce249c5d954daed90601 and tree
d9965fa59097b8d4cf04a3883ff06266a36d01fd. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added CellReleaseCall.lean for one reverse-
order intermediate release, preserving the completed sixth output and all
earlier live prefixes while adding the released buffer to the free chain.

CellReleaseCall passes in3.5s with standard logical axioms, log
euler-grid-cell-release-call-first.log. Added WriterReleaseOne.lean for the
exact nonzero-pointer release conditional, preserving the caller frame and
composing an explicit terminating release contract with its continuation.

The first conditional-release check reaches the chosen branch with a residual
if True then1 else0 condition. Preserved the draft/log and reduced that true
conditional alongside the already-reduced false one before applying the
structural branch rule.

WriterReleaseOne passes in3.7s with standard logical axioms, log
euler-grid-writer-release-one-condition.log. Added WriterReleaseShape.lean
using the successful short-prefix/list-reconstruction pattern to identify
six setup instructions, five release conditionals and the exact empty tail.
The default shape-proof recursion limit remains unchanged.

WriterReleaseShape passes in3.7s at the default recursion limit, log
 euler-grid-writer-release-shape-first.log, with propext only. After context
recovery reread AGENTS.md and this branch's operating contract; verified the
pinned Darwin Lean/Lake, Node, wasm-tools and Wasmtime executables exist at
the already-recorded tools/macos-env.sh paths. No toolchain substitution or
Linux preload. Added WriterReleaseFrame.lean for the six exact save instructions
and the saved intermediate/result pointer locals. This isolates pure local
frame facts before composing the five release calls. Checks remain focused.

WriterReleaseFrame passes in4.1s, log euler-grid-writer-release-frame-first.log.
The setup WP theorem uses the standard three logical axioms; all saved-pointer
facts use propext only. Added WriterReleases.lean to compose the five exact
reverse-order release conditionals. Its postcondition retains the completed
six-field output and original input, restores the five intermediate free-list
heads in forward order, and increments release/free counters by5.
The preceding append to this journal followed its source patch without a new
status inspection; this was a mutation-protocol lapse. Subsequent edits and
journal appends are grouped into one reviewed command after fresh status.

The first WriterReleases check reaches all five release continuations but
requires explicit normalization of numeral subtraction and free-list cons/
append forms when transporting the counter equalities. Preserved the draft
and first log, then added those small structural simplifications. The failed
build axiom output is not accepted evidence; no proof resources increased.

WriterReleases passes in3.8s with propext, Classical.choice and Quot.sound,
log euler-grid-writer-releases-normalize.log. Reviewed the release order,
exact saved locals, free-list ordering, kept arrays, counter equalities and
short telemetry alongside the proofs. Added the Project import, README,
notes and both plan substeps; full grid execution remains explicitly open.
No source, generated program or binary changed, so no runtime rerun is needed.

All91 maintained Markdown files, registry/import metadata, grid README links,
no-admission/no-trace scan and git diff --check pass. Stage/publish exactly:
- devnotes.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/CellReleaseCall.lean
- proofs/talos/lean/Project/EulerGridStep/WriterReleaseOne.lean
- proofs/talos/lean/Project/EulerGridStep/WriterReleaseShape.lean
- proofs/talos/lean/Project/EulerGridStep/WriterReleaseFrame.lean
- proofs/talos/lean/Project/EulerGridStep/WriterReleases.lean

### 2026-09-07: Complete accepted cell-writer execution

Published release checkpoint2709a539c92d427e5a2ff26df3bd399ab2b89478,
sole parentc6c174ea9029aab35e793bf96f7d4cdf7aa67b6d, tree
5c3497c1559c8972ae28f634c31030197d0f8f95. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added WriterStatus.lean to isolate the
exact ten-instruction status prefix and prove both branch-condition outcomes
without unfolding either large branch.

The first WriterStatus check unfolded the generic local lookup before using
its supplied equality. Preserved its draft/log and made that first lookup
an explicit atomic WP reduction; the remaining prefix has only constants,
comparisons and conditionals. No target or proof resource increase.

WriterStatus passes in4.0s with standard logical axioms, log
euler-grid-writer-status-lookup.log. Added WriterAccepted.lean to join the
status prefix, all six field calls, five releases and exact pointer-pair
return. Its postcondition names Model.putCell directly and retains the original
array, with explicit free-slot separation and availability. This conditional
writer result does not establish cold arena initialization or the grid loop.

The first WriterAccepted check executes the entire function and reaches its
return contract. Preserved the draft/log; split the final ABI pointer equality
from the buffer-state proof and used the named six-prefix equality before
unfolding any recurrence. This prevents simplification from expanding the
logical update prematurely. All earlier execution stages were accepted.

The return-boundary check accepts the ABI equality and leaves only the type
of the anonymous buffer constructors in a change tactic. Preserved its draft/
log and annotated that list as List LiveBuffer. No logical contract changed.
The local calendar rolled to2026-09-08 during this continuation; existing
20260907 log directories remain preserved and in use for this recovery run.

WriterAccepted passes in3.8s with propext, Classical.choice and Quot.sound,
log euler-grid-writer-accepted-typed.log. Reviewed the full exact function34
contract, ABI order, status premise, Model.putCell equality, unchanged input
output-buffer ownership, free-chain/counter transitions and fast telemetry.
Added its aggregate import and synchronized README, notes and both plan
substeps. Full grid execution remains incomplete; in particular separate
old-grid framing and initial storage availability are not inferred from this
conditional writer theorem. No source/binary/runtime changes or broad tests.

All91 maintained Markdown files, registry/import metadata, README links,
no-admission/no-trace scan and git diff --check pass. Stage/publish exactly:
- devnotes.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/WriterStatus.lean
- proofs/talos/lean/Project/EulerGridStep/WriterAccepted.lean

### 2026-09-08: Reusable copying update for rejected cells

Published accepted-writer checkpoint226ccfb740e3a8308ee4d596871f05d9eb9a11b3,
sole parent2709a539c92d427e5a2ff26df3bd399ab2b89478, tree
166f0f7422332a2a39e040c17d1dd65ec49eb15e. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Inspected the rejected branch: its copy/
update local window begins at67 instead of10 and writes index0/value1.
Added CopyUpdate.lean, parameterizing the proven header/copy/store/return
tail by that local-window offset. It retains the existing FieldWriteState
contract and kernel-checked byte roundtrip. The existing FieldTail theorem
will be specialized from this reusable result after its focused check.

CopyUpdate passes in3.6s with standard logical axioms, log
euler-grid-copy-update-first.log. Preserved the previous FieldTail source
externally and specialized its unchanged public theorem from the new offset
proof, eliminating duplicated proof steps. Added RejectedShape.lean with
exact prefix/branch/finish shapes and the rejected copy tail at offset67.
The generated Program.lean remains unchanged.

The specialized FieldTail passes in3.7s with the same standard axiom audit,
log euler-grid-field-tail-window.log. RejectedShape is rebuilding its affected
Euler dependencies serially under120s; no unrelated aggregate is included.
Added RejectedPrefix.lean for the exact17-instruction header read and index-
zero bound, with its six local assignments and true branch-condition stack.

RejectedShape and all affected dependencies pass, with propext-only shape
audits; the target itself takes3.8s. The first RejectedPrefix check reaches
its exact continuation with a residual explicit header bound and a record
layout parse diagnostic. Preserved the draft/log, aligned the record fields
and applied the already-proven generated header bound directly.

RejectedPrefix passes in3.6s with propext, Classical.choice and Quot.sound,
log euler-grid-rejected-prefix-bound.log. Reviewed the exact local window,
nonempty index-zero precondition, generated shapes and shared copy/update
contract. Added the import, README and concise notes. The unchanged full
accepted-writer target is rebuilding affected dependencies as the focused
regression for the shared FieldTail proof refactor. No source or bytes changed.

The accepted writer and its affected dependencies pass, with the accepted
writer target taking3.8s and retaining standard logical axioms, log
euler-grid-writer-accepted-copy-window.log. This completes the focused
regression required by the shared-copy proof change. All91 maintained
Markdown files, registry/import metadata, README links, no-admission/no-trace
scan and whitespace checks pass. Stage/publish exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/CopyUpdate.lean
- proofs/talos/lean/Project/EulerGridStep/FieldTail.lean
- proofs/talos/lean/Project/EulerGridStep/RejectedShape.lean
- proofs/talos/lean/Project/EulerGridStep/RejectedPrefix.lean

### 2026-09-08: Rejection allocation and ready frame

Published shared-copy checkpoint654347ab3dce162964819b8372edd41b0cc013f6,
sole parent226ccfb740e3a8308ee4d596871f05d9eb9a11b3, tree
f5255c1bf25cf34c7ac2b15ca8d6b6ec99885624. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added RejectedCapacity.lean for the emitted
copy-count/capacity setup at locals70/76, and RejectedReuseHit.lean for the
first sufficient free-block branch at locals77–81. The latter shares the
existing unlink-store model and generic six-metadata-store execution theorem;
only the generated local/frame scaffold is specialized.

RejectedCapacity passes in3.7s with standard logical axioms, log
euler-grid-rejected-capacity-first.log. Added RejectedReuseSearch.lean for
the exact first-head search at offset67, reusing the physical allocation
store model and the generic metadata theorem through RejectedReuseHit.
The search retains the one-to-zero termination measure and explicit capacity,
header-read, root-bound and free-head premises of the accepted field path.

RejectedReuseHit passes in4.1s and RejectedReuseSearch in5.4s, logs
euler-grid-rejected-reuse-hit-first.log and
euler-grid-rejected-reuse-search-first.log. Both execution audits use standard
logical axioms; shape audits use propext. Added RejectedAllocationShape.lean
and RejectedAllocationReuse.lean to connect that search to the exact17-
instruction allocator region, skip bump allocation after a hit, increment
the allocation counter, and store the selected root in local71.

The allocation-shape check verifies the allocator and bump-header slices;
its full clone decomposition used an ambiguous rewrite that collapsed the
outer split first. Preserved the draft/log and replaced that rewrite with an
explicit congrArg over the17-instruction inner split. No resource increase;
the exact generated-slice checks were already accepted.

RejectedAllocationShape and RejectedAllocationReuse pass, log
euler-grid-rejected-allocation-reuse-split.log, with propext-only shapes and
standard execution axioms. Added RejectedFrame.lean to prove the capacity
request, frame shape and every live getter required by CopyUpdate at offset67,
including index0/value1 and valid counter local72.

RejectedFrame passes in4.3s, log euler-grid-rejected-frame-first.log. Its
capacity fact uses propext/Quot.sound and other frame facts use propext. The
complete allocator-reuse target took3.9s; its shape dependency took4.8s.
Reviewed all six new modules, the exact local numbers, capacity normalization,
first-head assumptions, generic metadata/store reuse and counter frame facts
with the telemetry. Added Project import, README and notes. No changed source
or bytes; no runtime or broad aggregate rerun is justified.

All91 maintained Markdown files, registry/import metadata, grid README links,
no-admission/no-trace scan and whitespace checks pass. Stage/publish exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/RejectedCapacity.lean
- proofs/talos/lean/Project/EulerGridStep/RejectedReuseHit.lean
- proofs/talos/lean/Project/EulerGridStep/RejectedReuseSearch.lean
- proofs/talos/lean/Project/EulerGridStep/RejectedAllocationShape.lean
- proofs/talos/lean/Project/EulerGridStep/RejectedAllocationReuse.lean
- proofs/talos/lean/Project/EulerGridStep/RejectedFrame.lean

### 2026-09-08: Complete rejected writer composition

Published allocation checkpoint66fb14bebd88cd8de5f1e8d5c534a4671ed84fa0,
sole parent654347ab3dce162964819b8372edd41b0cc013f6, tree
a7b10d776acc1313d2b093e050d8ef97d39083d7. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added RejectedClone.lean to join capacity,
reuse allocation and the generic copy/update tail into exact index0/value1
execution with the established allocation-validity contract.

RejectedClone passes in3.5s with standard logical axioms, log
euler-grid-rejected-clone-first.log. Added WriterRejected.lean to compose the
complete generated function34 for nonzero cell status: status dispatch,
header/bounds prefix, reuse clone, result-local saves and pointer-pair return.
Its FieldResult postcondition preserves the original array and metadata/
object footprint while representing input.set! 0 1. Initial reuse capacity
and physical separation remain explicit premises.

WriterRejected passes in3.7s with propext, Classical.choice and Quot.sound,
log euler-grid-writer-rejected-first.log. Reviewed complete function34 ABI/
branch handling, index-zero update, unchanged original array, owned result
metadata, object footprint and explicit reuse-only allocation premises with
the telemetry. Added its import, README, notes and both plan substeps.
Both accepted/rejected writer outcomes are now covered under their explicit
reusable-buffer assumptions; full grid execution and initial/fresh allocation
are not claimed. No runtime or unrelated aggregate rerun.

All91 maintained Markdown files, registry/import metadata, README links,
no-admission/no-trace scan and whitespace checks pass. Corrected four earlier
README pending-work sentences to point to the newly complete conditional
rejection theorem. Stage/publish exactly:
- devnotes.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/RejectedClone.lean
- proofs/talos/lean/Project/EulerGridStep/WriterRejected.lean

### 2026-09-08: Carrying protected old-grid observations through cell calls

Published rejected-writer checkpoint0564972942a15680fe755c8f5ad9285dcb59d23c,
sole parent66fb14bebd88cd8de5f1e8d5c534a4671ed84fa0, tree
906bd1cdbb7aae57e616a7925775a76467560c22. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. The current accepted-writer theorem retains
its original output array but does not carry an arbitrary separate old-grid
observation through all calls. Added CellFieldFramed.lean, preserving an
extra postcondition derived from the primitive FieldResult instead of losing
that result when projecting to BufferState. This supports the required
old-grid frame without changing numerical source or generated instructions.

CellFieldFramed passes in3.5s with standard logical axioms, log
euler-grid-cell-field-framed-first.log. Added CellReleaseFramed.lean with
the corresponding extra postcondition obtained from the exact ReleaseResult.
Both extend the cell-stage contracts so a separate old-grid array observation
can survive each operation under its physical-separation proof.

Added WriterCopiesFramed.lean to carry the extra property through the six
emitted calls, with an explicit per-field preservation rule over the exact
FieldResult and an initial property premise. The checked pointer frames,
seven-live-buffer state, free-list transitions and allocation counts remain
unchanged. This will instantiate to preservation of the separate old grid.

CellReleaseFramed passes in3.5s with standard logical axioms, log
euler-grid-cell-release-framed-first.log. Added WriterReleasesFramed.lean
to carry the same extra property through the five exact release conditionals,
with an explicit preservation rule over each ReleaseResult. The original
input/completed output, free-chain order and release/free counts are retained.

WriterCopiesFramed passes in3.7s with standard logical axioms, log
euler-grid-writer-copies-framed-first.log. Added WriterProtected.lean to
instantiate the extra property as an arbitrary separate represented array,
using FieldResult.preserves_array and ReleaseResult.preserves_array at every
step. The final postcondition retains both the exact writer result/buffer
state and the observed old-grid array, with explicit object separation.

WriterReleasesFramed passes in3.7s and WriterProtected in3.6s, logs
euler-grid-writer-releases-framed-first.log and
euler-grid-writer-protected-first.log. All new execution audits use only
propext, Classical.choice and Quot.sound. Reviewed the additional property
premises, exact field/release observations, every stage continuation and the
concrete different-length array preservation result. Added the import, README,
notes and both plan substeps. Full grid execution remains open. No source,
bytes, runtime or unrelated regression change.

All91 maintained Markdown files, registry/import metadata, grid README links,
no-admission/no-trace scan and whitespace checks pass. Stage/publish exactly:
- devnotes.md
- journal.md
- plan.md
- plans/euler-rusanov.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/CellFieldFramed.lean
- proofs/talos/lean/Project/EulerGridStep/CellReleaseFramed.lean
- proofs/talos/lean/Project/EulerGridStep/WriterCopiesFramed.lean
- proofs/talos/lean/Project/EulerGridStep/WriterReleasesFramed.lean
- proofs/talos/lean/Project/EulerGridStep/WriterProtected.lean

### 2026-09-08: Fresh first-cell allocation sequence

Published protected-grid checkpointf99dbab1349b5ce6a07b387b8e73b5edc0e8b0d7,
sole parent0564972942a15680fe755c8f5ad9285dcb59d23c, tree
0d02d094458956a586a6de1eaa2aafa9b688f057. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. The first nonempty cell begins without six
reusable buffers, so its emitted writes require fresh allocation. Added
WriterSequence.lean to abstract the exact six-call control flow over a staged
store invariant and explicit terminating field calls, retaining every saved
pointer/local handoff. It can compose fresh or reusable allocation contracts
without assuming the first cell starts with a prefilled free list.

WriterSequence passes in3.5s with standard logical axioms, log
euler-grid-writer-sequence-first.log. Added FreshBufferState.lean to lift the
existing complete fresh field-write theorem into the live-buffer/counter
invariant, keeping the free list empty and exposing the exact updated heap
pointer. Its physical capacity and separation premises remain explicit.

FreshBufferState passes with standard logical axioms, log
euler-grid-fresh-buffer-state-first.log. Added ArenaLayout.lean for seven
consecutive output objects: exact root/heap words, physical slot bounds,
metadata-inclusive separation, heap advancement, and the64+48*cells byte
size of each grid output object. These are conditional address/layout facts;
full fresh-writer and grid execution still need composition.

ArenaLayout passes in3.5s with propext/Quot.sound (root/heap word equality
uses propext), log euler-grid-arena-layout-first.log. FreshBufferState also
took3.5s. Added ArenaAllocation.lean to discharge the existing fresh
allocation-validity contract from the seven-slot memory budget, exact runtime
globals and distinct source/destination slots. No implicit preallocated free
pool or unbounded-memory assumption is introduced.

ArenaAllocation passes in3.7s with propext/Quot.sound, log
euler-grid-arena-allocation-first.log. Reviewed all four new modules with
the telemetry: the generic call sequence, fresh live/global transition,
seven-slot geometric bounds, exact word conversions and capacity/separation
preconditions. Added their imports, README and notes. The initial array and
six fresh calls still need composition, and full grid execution stays open.
No source, binary, runtime, broad aggregate or release-boundary change.

All91 maintained Markdown files, registry/import metadata, grid README links,
no-admission/no-trace scan and whitespace checks pass. Stage/publish exactly:
- devnotes.md
- journal.md
- proofs/talos/lean/Project.lean
- proofs/talos/lean/Project/EulerGridStep/README.md
- proofs/talos/lean/Project/EulerGridStep/WriterSequence.lean
- proofs/talos/lean/Project/EulerGridStep/FreshBufferState.lean
- proofs/talos/lean/Project/EulerGridStep/ArenaLayout.lean
- proofs/talos/lean/Project/EulerGridStep/ArenaAllocation.lean

### 2026-09-08: Complete fresh first-cell stages

Published fresh-arena checkpointa7f7173f3e9efbd4124cf13806966cf36bab6754,
sole parentf99dbab1349b5ce6a07b387b8e73b5edc0e8b0d7, tree
b4c0449ba5d3c7d376dbf0716e46a488dcb0cd96. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree equality and local CAS passed;
clean synchronization confirmed. Added FreshCellState.lean: a staged live-
prefix/free/counter invariant with the next heap slot and explicit seven-
object budget, advanced by one complete fresh field call. Its postcondition
also retains the exact FieldResult for old-grid preservation.

FreshCellState passes in3.5s with standard logical axioms, log
euler-grid-fresh-cell-state-first.log. Added FreshWriterCopies.lean to
instantiate WriterSequence with the fresh staged invariant and a separate
observed-array predicate. It composes all six emitted allocations/writes,
retaining the old grid and ending with seven initialized live slots.

FreshWriterCopies passes in3.4s with standard logical axioms, log
euler-grid-fresh-writer-copies-first.log. Added FreshWriterAccepted.lean
for the full generated accepted writer from an empty free list: six fresh
allocations, five intermediate releases, exact Model.putCell result and
old-grid preservation. Seven-slot availability comes from the explicit
budget; the initial output in slot0 is still an input to this theorem.

FreshWriterAccepted passes in3.6s with propext, Classical.choice and
Quot.sound, log euler-grid-fresh-writer-accepted-first.log. Reviewed the
full generated writer contract, staged heap/allocation transitions, empty
initial free chain, exact final live/free lists, seven-object budget and
protected old grid with the telemetry. Added the import, README, notes and
both plan substeps. Slot0 initialization remains a premise, and fresh
rejection/full grid execution are not claimed. No source/byte/runtime change.

Post-compaction review reread AGENTS.md and the operating contract. Confirmed
all three new proofs and their successful logs; no additional proof run was
needed. The91 maintained Markdown files,34 registry/import entries, README
links, no-admission/no-trace scan and git diff --check pass. In response to
the user's manageable-regression instruction, no broad gate was run.
Stage/publish exactly devnotes.md, journal.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,FreshCellState.lean,
FreshWriterCopies.lean,FreshWriterAccepted.lean}.

### 2026-09-08: Fresh rejected writer allocation

Published e5148ff3a52ce00c13d069bec24a4c52530e182b, sole parent
a7f7173f3e9efbd4124cf13806966cf36bab6754, tree
b096c59e81fa85c3a97fa0e86a891b3fd92b2b68. Non-forced update, fetch,
commit/parent/message/tree/index/worktree verification and local CAS passed;
clean synchronization confirmed. Added RejectedAllocationBump.lean by
instantiating the existing fresh allocation proof at the rejected writer's
local window67, with10 parameters and72 locals. Generic metadata stores
remain shared; byte offsets and capacity semantics are unchanged. The
explicit existing-page budget excludes memory growth.

Pinned Darwin Lean/Lake and wasm-tools paths were validated executable after
compaction; no preload is used. The first focused RejectedAllocationBump
build failed in5.6s at the heap lookup: simplification had not opened the
extra rejectedCloneBody definition. Its log is
euler-grid-rejected-fresh-allocation-first.log; failed draft preserved
externally as work/euler-grid-rejected-fresh-allocation-first.lean. Added
that missing shape definition to the existing bounded simplification.
No timeout or resource increase; failed-build axiom output is not evidence.

RejectedAllocationBump passes in7.3s with standard logical axioms; log
euler-grid-rejected-fresh-allocation-shape.log. Review with the proof shows
only the extra shape unfolding was missing; metadata stores stay shared.
Added FreshRejectedFrame.lean to establish the exact rejected-copy window
after fresh allocation and its returned counter frame.

FreshRejectedFrame passes in4.3s with propext only; log
euler-grid-fresh-rejected-frame-first.log. Added FreshRejectedClone.lean
to compose capacity, fresh allocation and the shared copy_update_spec67,
writing status one and retaining the full memory frame. Only this new
composition target is next; successful dependencies remain cached.

FreshRejectedClone passes in3.8s with standard logical axioms; log
euler-grid-fresh-rejected-clone-first.log. Added FreshWriterRejected.lean
for the complete generated function34 when the cell is rejected and the
free list is empty. Its exact FieldResult retains old-grid preservation
through the existing object-frame theorem; no numerical or byte claim changes.

FreshWriterRejected passes in3.0s with propext, Classical.choice and
Quot.sound, log euler-grid-fresh-writer-rejected-first.log. Reviewed the
complete conditional body, allocation/copy continuation and exact return
against telemetry. Four narrow modules establish this missing fresh outcome;
all previous successful proofs were replayed from cache. Updated README,
aggregate import, notes and both plan substeps. No runtime, source, bytes,
CLOB, full aggregate or release gates were touched.

The91 maintained Markdown files,34 registry/import entries, README links,
no-admission/no-trace scan and whitespace checks pass. Stage/publish exactly
devnotes.md, journal.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,
RejectedAllocationBump.lean,FreshRejectedFrame.lean,FreshRejectedClone.lean,
FreshWriterRejected.lean}.

### 2026-09-08: Clamped neighbor indexing

Published454325c9fc5b89841cb6ed73158dead2a77ccea4, sole parent
e5148ff3a52ce00c13d069bec24a4c52530e182b, tree
cad218785db54a41ce16583a188782ad7122cdea. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed,
with clean synchronization. Inspected all297 top-level instructions of
advance35: its first47 calculate clamped offsets, call25 is instruction236,
and writer34 is instruction288. Added NeighborIndexing.lean with all nine
in-bounds facts, checked-add safety, the next-cell word comparison and exact
model correspondence. Reuses the established scan index/memory lemmas.

NeighborIndexing passes in3.5s with standard logical axioms; log
euler-grid-neighbor-indexing-first.log. Added AdvanceOffsets.lean for the
exact first47 instructions and explicit outgoing frame. Separates endpoint
branches and checked word arithmetic from the subsequent nine memory reads,
keeping the next proof boundary bounded.

AdvanceOffsets first build fails in3.9s at its first typed conditional;
log euler-grid-advance-offsets-first.log and external failed draft
work/euler-grid-advance-offsets-first.lean are preserved. The local peeling
tactic needed wp_iff_control_types before the untyped conditional rule,
as earlier writer proofs already established. Added that normalization,
without changing the program, specification or resource budget.

The typed-boundary variant still stops at the first conditional in3.0s,
log euler-grid-advance-offsets-typed.log; saved its external draft as
work/euler-grid-advance-offsets-typed.lean. Isolating that boundary with
explicit rewrite/application outside the repeat tactic to expose the exact
remaining mismatch. No resource increase or unchanged retry.

The explicit diagnostic identified an earlier obstruction: the straight-line
simplifier had left the concrete prefix appended to abstract rest, so it
could not reach the conditional. The final simpa in prior failures had
partially reduced that goal and obscured this. Preserved boundary log/draft
euler-grid-advance-offsets-boundary; added List.cons_append/List.nil_append
to the local peeling tactic and removed the temporary explicit diagnostic.
Typed conditional normalization remains appropriate once the prefix unfolds.

The append-normalized proof reaches the array-length memory guard in10s,
log/draft euler-grid-advance-offsets-append. Added the explicit negated
out-of-bounds test from generatedLengthBound so the straight-line
simplifier can discharge it. The mathematical bound was already present;
this is the exact Boolean guard form required by emitted load semantics.

The length-guard variant completes both nonzero-index branches in11s but
the two zero-index branches retain the next-cell test. Preserved log/draft
euler-grid-advance-offsets-length-guard. Normalize the comparison lemma's
zero-index encoding explicitly to the literal word1 after substitution,
so simplification matches the generated test. No theorem premise changes.

AdvanceOffsets now passes in11s with standard logical axioms, log
euler-grid-advance-offsets-zero-word.log. Review confirms exact scratch
locals in all endpoint/interior branches, safe checked arithmetic and
unchanged memory. Added AdvanceReads.lean for the following189 instructions: 
nine guarded conservative-word loads and exact reversed cell25 arguments.
The proof supplies each physical bound/read fact explicitly and retains
the complete generated frame.

AdvanceReads exceeded the explicit120s limit without a theorem diagnostic,
exit124, log euler-grid-advance-reads-first.log. Preserved its full draft
externally as work/euler-grid-advance-reads-first.lean. Do not repeat that
unchanged target. Added AdvanceReadFrames and three independent groups of
three single-read proofs, each with its own small exact instruction slice.
The shared staged frame records only emitted local updates; each proof
uses one element's bounds/read facts. This reduces the elaboration boundary
without raising limits. The original composition module will be rewritten
to apply these proved slices.

Whitespace review also found one trailing space in the preceding new journal
paragraph. It is retained under the append-only journal contract; this is
a documented journal-only whitespace exception, not a failed code check.

The first split-read build stopped in3.5s on an unmatched parenthesis in
AdvanceReadFrames, before checking a read theorem. Preserved log
euler-grid-advance-read-left-first.log and external frame draft
euler-grid-advance-read-frames-first.lean; replaced the nested list update
with short sequential let bindings. Rewrote AdvanceReads to compose nine
single-read lemmas and the final10 local gets, replacing its timed-out
monolithic peeling proof. The original failed proof remains preserved.

The split left-read target now finishes diagnostics in15s. Reads1/2
(second/third fields) execute completely but their returned getD expressions
need the known index bound to match dependent array access. Read0 stops at
a not-yet-normalized memory guard. Preserved log
euler-grid-advance-read-left-frames.log and the four affected external
normalization drafts. Added bounded arithmetic simplification to the shared
peeler and explicit Array.getD/hBound normalization at each return.
This addresses representation mismatches; no source, memory premise,
semantic claim or resource limit changed.

The normalized left group finishes in6.7s: read0 passes, while reads1/2
need the bounds of earlier staged fields at their return. The shared
simplifier had reduced those earlier getD expressions using arithmetic,
while the final comparison had not. Preserved normalized log and external
prior-bounds drafts. Supply the maximum-field bound for each of the three
neighbors and use omega in final simplification; these facts derive from
the same hi premise. This also handles earlier neighbors in later stages.

The aggregate-bound version finishes in6.9s with the same final dependent
if mismatch: simplifier discharge does not itself rewrite the earlier
getD conditions. Preserved log euler-grid-advance-read-left-all-bounds.log
and explicit-bounds drafts. Destructure all nine already-proved bounds,
normalize field-zero offsets and pass those facts directly to final simp.
This targets the remaining dependent-if expressions without extra execution.

All nine individual reads now pass: AdvanceReadLeft7.4s, Centre10s and
Right10s, each audited to propext, Classical.choice and Quot.sound. Logs
euler-grid-advance-read-left-explicit-bounds.log,
euler-grid-advance-read-centre-first.log and
euler-grid-advance-read-right-first.log are retained. Review of each exact
slice, staged frame and telemetry confirms no memory mutation and correct
left/centre/right conservative fields. The full AdvanceReads target is
now materially reduced to composition of these checked boundaries.

AdvanceReads composition passes in4.3s, log
euler-grid-advance-reads-composed.log, with standard logical axioms; its
exact instruction-slice identity uses none. Reviewed the accepted proof
and telemetry together: splitting the nine reads into independent slices
removed the120s elaboration bottleneck, and composition is now small.
Retain these fixed generated slices as worked examples; a future shared
compiler-read window could abstract their repeated staging/bounds work.
Updated aggregate import, README, both plan substeps and concise notes.
The complete advance35 calls, initial output and grid loop remain open.
No source, bytes, runtime or unrelated regression work was done.

The91 maintained Markdown files,34 registry/import entries, README links
and new-proof no-admission/no-trace/whitespace scans pass. Tracked source
and documentation whitespace checks pass; the single previously documented
append-only journal trailing space is the only full-diff whitespace finding.
Stage/publish exactly devnotes.md, journal.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,
NeighborIndexing.lean,AdvanceOffsets.lean,AdvanceReadFrames.lean,
AdvanceReadLeft.lean,AdvanceReadCentre.lean,AdvanceReadRight.lean,
AdvanceReads.lean}. No broader checks are required for these proof changes.

### 2026-09-08: Full cell-advance call composition

Publishedcee31f7bdcabcac27a05284b1f480e6ea5f49f60, sole parent
454325c9fc5b89841cb6ed73158dead2a77ccea4, tree
27a629f798fd86aaa04c58dcb8ac0209e60bcc3b. Non-forced update, fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS succeeded;
clean synchronization confirmed. Added AdvanceExecution.lean to connect
the proved offsets/reads to unchanged cell25 and the applicable writer34
contract, then return the exact pointer pair from all of generated
advance35. The writer postcondition stays generic so fresh/reuse and
accepted/rejected storage contracts can instantiate the same control proof.

AdvanceExecution passes in6.5s with standard logical axioms; log
euler-grid-advance-execution-first.log. It proves every instruction of
advance35 using the actual cell25 theorem and an applicable writer theorem.
Added AdvanceAccepted.lean to instantiate it for accepted fresh and reused
writers, returning exact Model.advanceAt output, live/free buffers and
counters while preserving the old-grid array.

AdvanceAccepted passes in3.5s with standard logical axioms for both storage
paths; log euler-grid-advance-accepted-first.log. Added AdvanceRejected.lean
to dispatch the fresh/reuse rejected writers and instantiate the same full
advance35 control proof. Its postcondition includes Model.advanceAt array
contents, exact destination FieldResult and preservation of the old grid.

AdvanceRejected passes in3.7s, log euler-grid-advance-rejected-first.log,
with standard logical axioms. Reviewed complete advance call/return wiring
and all four currently instantiated writer outcomes with the telemetry.
Updated imports, README, notes and plan substeps.

Correction to the earlier working resource agenda: inspecting exact func36
lines4110–4284 shows call35 inside the loop, but release40 only after both
loop/block closures. Its argument is local7, the initial output. There is
no per-iteration release of the previous output. The earlier inference of
a sustained six-node free pool was wrong; no published whole-grid theorem
claimed it. Existing seven-object/fresh and six-reused writer theorems
remain correct under their explicit premises. After a successful first
cell, five intermediates are free; later successful cells must reuse those
five and allocate their final output fresh. For N successful cells the
call pattern suggests N+6 physical output objects, a resource count still
to prove. Initial allocation and outer-loop proofs remain open. The
repository source, exact Program and bytes are unchanged; prove this
actual mixed allocation path before connecting the loop invariant.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Stage/publish exactly devnotes.md, journal.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,
AdvanceExecution.lean,AdvanceAccepted.lean,AdvanceRejected.lean}.

### 2026-09-08: Mixed allocation and heap-aware release composition

Publisheda1230622ec45112866b109191796a7fcfbc5c03d, sole parent
cee31f7bdcabcac27a05284b1f480e6ea5f49f60, tree
d9dc175d130f56883a92cfd16dcb2fa934beb0df. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronization confirmed. Added WriterReleaseSequence.lean as
allocation-independent control for the exact five releases, analogous to
WriterSequence for the six writes. Its generic indexed predicate can retain
the heap pointer needed for each later fresh allocation. This avoids
attempting to infer global changes from ReleaseResult, whose contract is
intentionally a memory frame. Existing worked release proofs remain intact.

WriterReleaseSequence passes in3.4s with standard logical axioms, log
euler-grid-writer-release-sequence-first.log. Added BufferResults.lean
with allocation-result-to-buffer-state lemmas: reuse preserves global0,
fresh allocation advances it exactly, and both retain live/free/counter
state. These postcondition lemmas work for any copied index/value and
avoid re-proving runtime calls for the mixed writer or rejection path.

BufferResults first build finishes in3.5s with two remaining global-list
bounds (index2 below the known length greater than5). Preserved log
euler-grid-buffer-results-first.log and external failed draft. Added the
final omega step used by the existing buffer proofs; all other heap and
state obligations had closed. No timeout or budget increase.

BufferResults passes in3.7s with standard logical axioms; log
euler-grid-buffer-results-global-bounds.log. Added ReleaseHeap.lean,
retaining global0 from release40's exact global update alongside its
existing live/free/memory result. This is a strengthened wrapper over
the complete checked release, not an inference from a memory-only result.

ReleaseHeap passes in3.7s with standard logical axioms, log
euler-grid-release-heap-first.log. Added FreshSpace.lean to derive fresh
allocation validity from one available object and exact globals, without
the earlier seven-slot geometry. This is the space premise needed for the
last write of every later accepted cell in the actual growing arena.

FreshSpace passes in3.8s with propext/Quot.sound, log
euler-grid-fresh-space-first.log. Reviewed the four new modules and
telemetry together: the control sequence is independent of allocation,
postcondition lemmas share live/free/counter bookkeeping, and the exact
heap address survives release. Fresh-space validity uses the existing
checked bump facts. These are support lemmas; mixed writer and whole-grid
resource/execution claims remain open. Added imports, README and notes;
no source, generated bytes, runtime, aggregate or release-boundary changes.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Stage/publish exactly devnotes.md, journal.md, proofs/talos/lean/Project.lean
and EulerGridStep/{README.md,WriterReleaseSequence.lean,BufferResults.lean,
ReleaseHeap.lean,FreshSpace.lean}.

### 2026-09-08: Five-buffer mixed writer stages

Published5c9fb6b9cc83f669b4bb0580559b57514ee86e7f, sole parent
a1230622ec45112866b109191796a7fcfbc5c03d, tree
474850ba1f8f82cd8c41499be26cb9e20f1844db. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree verification and local CAS
passed, with clean synchronization. Added WriterPool.lean for the exact
five-node reusable suffix: consuming a head and prepending a release are
inverse list transitions, and all remaining nodes have distinct later
slot indices. These facts serve both mixed writes and their release tail.

WriterPool passes in3.4s with standard logical axioms; log
euler-grid-writer-pool-first.log. Added MixedCellState.lean for the staged
five-reused/one-fresh writer: exact live prefixes, remaining pool, allocation
count, heap pointer and available fresh space. Each full field call retains
its FieldResult for the later old-grid and page-count frame composition.

MixedCellState first build fails after8.9s at the200000-heartbeat whnf
boundary while elaborating the fresh-call application, log
euler-grid-mixed-cell-state-first.log. Saved the full failed draft
externally. Split the invariant definitions into MixedState.lean and the
two complete call cases into MixedReuseCall.lean and MixedFreshCall.lean;
MixedCellState now dispatches the two proved cases. No heartbeat or timeout
limit is raised, and the unchanged combined proof will not be retried.

MixedReuseCall passes with standard logical axioms, log
euler-grid-mixed-reuse-call-first.log. The isolated MixedFreshCall still
hits the200000-heartbeat whnf limit after9.2s; its log and external failed
draft are preserved. Removing early substitution of field=5 keeps the
prefix arrays symbolic. Added separate small target/pool equalities and
uses the existing size lemmas at the call boundary. This reduces concrete
prefix expansion without changing either resource limit or runtime code.

Recovered the operating contract and validated the existing pinned Darwin
Lean/Lake, wasm-tools and Wasmtime executable paths through macos-env.sh;
Node remains v24.13.0, one Lean thread and the approved inherited-priority
exception, with no preload. MixedFreshCall now passes in3.5s with standard
logical axioms, log euler-grid-mixed-fresh-call-symbolic.log. Keeping the
field symbolic removed the elaboration failure. Added CellReleaseHeap.lean
as a strengthened wrapper for each intermediate release: it retains exact
release memory, buffer state and heap pointer for later writer composition.

MixedCellState dispatch passes in3.6s with standard logical axioms, log
euler-grid-mixed-cell-state-dispatch.log. Added WriterAcceptedSequence.lean
to share complete writer34 control between allocation plans: six checked
field calls, a state bridge, five checked releases and the exact return.
This separates storage invariants from the already verified control flow.

CellReleaseHeap passes in3.7s and WriterAcceptedSequence in3.8s, with
standard logical axioms; logs euler-grid-cell-release-heap-first.log and
euler-grid-writer-accepted-sequence-first.log. Reviewed all seven new modules
and telemetry: symbolic array prefixes keep elaboration small, while the
shared accepted sequence contains exact calls rather than storage-specific
assumptions. Existing worked examples remain intact. Added imports, README
and checkpoint notes. No executable source or generated bytes changed.
The next checkpoint will instantiate complete mixed writer storage and
connect it to advance35. Regression scope stays at changed proof targets
and small documentation/registry checks, as requested by the user.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Reviewed/stage/publish exactly devnotes.md, journal.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,WriterPool.lean,
MixedState.lean,MixedReuseCall.lean,MixedFreshCall.lean,MixedCellState.lean,
CellReleaseHeap.lean,WriterAcceptedSequence.lean}.

### 2026-09-08: Complete mixed writer storage composition

Published bdb576dd7d16f0a6a12ccb616d2b91fac7a3601b, sole parent
5c9fb6b9cc83f669b4bb0580559b57514ee86e7f, tree
7fed2f2e6529f25d1f02ff40a796a6a6e0bfffac. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronization confirmed. A read of the summary's misspelled
FramedCellField.lean path found no file; no state changed. Added
WriterReleaseState.lean: one indexed release state now retains buffers,
heap, exact page count and a property preserved by each ReleaseResult.
This can carry old-grid data and additional initial-output observations
needed by the eventual loop, without duplicating writer control.

WriterReleaseState passes in3.5s with standard logical axioms, log
euler-grid-writer-release-state-first.log. Added MixedWriterFramed.lean
to instantiate the complete accepted control with mixed field calls and
the shared release state. The framed predicate is carried from explicit
FieldResult/ReleaseResult preservation lemmas; exact heap and pages are
retained directly by the checked storage calls.

MixedWriterFramed passes in3.6s with standard logical axioms, log
euler-grid-mixed-writer-framed-first.log. Added MixedWriterAccepted.lean
to discharge both frame callbacks for a separate old-grid array. The
complete theorem reports the actual six allocations/five releases, five
reusable nodes, one-object heap advance and unchanged memory page count.

Added AdvanceMixed.lean to compose the complete mixed writer with the
already checked neighbor reads, numerical cell call and advance35 return.
The public postcondition includes Model.advanceAt, the five-buffer pool,
exact allocation/release counters, heap advance, pages and preserved input.

MixedWriterAccepted first check fails in3.6s on the small fresh-root
equality: simp only substituted field=5 before reducing the literal
5<5 test. Preserved the log and external draft; changed just that leaf
to ordinary simplification of the literal guard. Failed-build axiom output
is not accepted evidence. No timeout, limit increase or runtime change.

MixedWriterAccepted now passes in3.6s and AdvanceMixed in3.7s, both with
standard logical axioms, log euler-grid-advance-mixed-first.log. Reviewed
the complete proofs and telemetry: the only correction was the small
literal guard simplification; full call composition remains small. This
closes the actual later accepted-cell allocation path. Updated plans,
README, aggregate imports and notes, retaining explicit open initialization,
growing-arena and outer-loop claims. No source/byte/runtime changes.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Corrected the earlier README support paragraph to identify the now-complete
mixed writer and still-open arena proof. Reviewed/stage/publish exactly
devnotes.md, journal.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,WriterReleaseState.lean,
MixedWriterFramed.lean,MixedWriterAccepted.lean,AdvanceMixed.lean}.

### 2026-09-08: Growing grid arena bounds

Published e46bb794c9dfbf02627d1bd0415c57952656c719, sole parent
bdb576dd7d16f0a6a12ccb616d2b91fac7a3601b, tree
7352d6b0283c8842034ab2f43c44d712471b25e1. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronization confirmed. Reread the exact outer-loop tail: the
only release follows the loop and targets initial output local7. Added
ArenaBounds.lean to generalize the preserved seven-slot worked geometry
to any explicit slot count, retaining exact word addresses and separation.
A focused search found no existing advanceAt/putCell size lemma in Model
or Outputs; no state changed. Outer-loop resource execution remains open.

ArenaBounds passes in3.4s with propext/Quot.sound, log
euler-grid-arena-bounds-first.log. Added LaterArena.lean: after a positive
number i of accepted cells, writer source slot is i+5, reusable slots stay
1..5 and the next fresh destination is i+6. The seven logical writer roots
are distinct and fit within cells+6 physical slots when i<cells. This is
geometry for the actual retained-output path, still conditional on the
execution invariant and explicit existing-memory budget.

LaterArena passes in3.5s with propext/Quot.sound, log
euler-grid-later-arena-first.log. Added GridSizes.lean for unchanged output
length through putCell, advanceAt and fill. Added LaterArenaState.lean
to retain the current output, fixed five-node pool, growing heap and budget
after accepted cells. Its mixed-writer precondition requests one remaining
object only while another cell remains; terminal state needs no extra slot.

Added AdvanceArena.lean to connect the complete accepted advance to the
growing arena: current output slot i+5 becomes slot i+6, the five-node
pool is restored, the heap becomes slot i+7 and the same whole-grid budget
survives. Restricting the live list records the output needed by the next
iteration; it performs no runtime release of the previous output.

The LaterArenaState dependency check stops at GridSizes: splitting the
advanceAt conditional requires reducing its local cell binding first.
Preserved the failed log and external draft; changed that leaf from unfold
to dsimp only, retaining the symbolic cell model. No execution theorem or
failed-build axiom output is claimed from this run.

GridSizes passes in3.5s and LaterArenaState in3.6s with standard axioms.
AdvanceArena reaches its final address normalization in3.7s; simp already
closes that equality, so the following congr tactic reports no goals.
Preserved log/draft and removed only that redundant tactic. No timeout
or changed proof claim; failed-run audits remain excluded.

AdvanceArena passes in3.7s with standard logical axioms, log
euler-grid-advance-arena-normalized.log. Reviewed all five new modules
and telemetry: variable geometry preserves the seven-slot worked example,
size equalities keep array-dependent addresses fixed, and the full advance
retains the bounded arena without releasing a previous output. Updated
plans, README, imports and notes with the precise completed per-cell claim
and remaining first-cell/rejection/loop boundaries. No runtime code changed.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Aligned the earlier README cross-references with the checked later-cell
arena transition. Reviewed/stage/publish exactly devnotes.md, journal.md,
plan.md, plans/euler-rusanov.md, proofs/talos/lean/Project.lean and
EulerGridStep/{README.md,ArenaBounds.lean,LaterArena.lean,GridSizes.lean,
LaterArenaState.lean,AdvanceArena.lean}.

### 2026-09-08: First-cell heap handoff

Published 47a4be94f9f6ef197d1ab86bb9d454c7bad3aa49, sole parent
e46bb794c9dfbf02627d1bd0415c57952656c719, tree
249d8efb248b7cb9f312fccf42dbaa233600bae8. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronization confirmed. A speculative FreeExecution.lean search
named no existing file; subsequent unknown-path reads must first discover
the actual filenames. Added FreshWriterFramed.lean using the shared complete
writer/release control to retain the first writer's exact heap slot7 and
page count. The earlier accepted writer theorem remains a checked example.

FreshWriterFramed passes in3.5s with standard logical axioms, log
euler-grid-fresh-writer-framed-first.log. Added FreshWriterHeap.lean to
discharge old-grid preservation while keeping exact heap slot7 and pages.
The shared control avoids repeating the first writer’s instruction proof.

Added AdvanceFirstArena.lean to establish LaterArenaState at index1 from
the initialized slot0 and the explicit cells+6 object budget. The first
advance’s exact six fresh writes and five releases supply output slot6,
heap slot7 and the same five-node pool used by later advances. Actual
initial output allocation remains a separate unproved entry boundary.

FreshWriterHeap passes in3.6s and AdvanceFirstArena in3.7s with standard
logical axioms; logs euler-grid-fresh-writer-heap-first.log and
euler-grid-advance-first-arena-first.log. Reviewed proofs/telemetry: the
new shared writer control carries stronger state without duplicating the
instruction sequence, and the first advance now establishes exactly the
invariant consumed by later accepted advances. Updated plans, README,
imports and checkpoint notes. Initial allocation/rejection/outer-loop
claims remain explicitly open. No executable source or bytes changed.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Reviewed/stage/publish exactly devnotes.md, journal.md, plan.md,
plans/euler-rusanov.md, proofs/talos/lean/Project.lean and
EulerGridStep/{README.md,FreshWriterFramed.lean,FreshWriterHeap.lean,AdvanceFirstArena.lean}.

### 2026-09-08: Rejected advance storage transitions

Published b9581224b5a8b05353cc8033566c4045461f0176, sole parent
47a4be94f9f6ef197d1ab86bb9d454c7bad3aa49, tree
8fd7d17d770e905d6e75c996c73c1e364b8719b7. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronization confirmed. Discovered/read the actual FreeChain and
FreeChainExecution paths. Added RejectedBuffers.lean to retain exact live/
free state, counters, heap, pages, memory frame and old grid through the
complete rejected advance, for either a free-node or fresh allocation.
No accepted-path release counts are assumed on rejection.

RejectedBuffers first check reports an untyped singleton in each local
separation predicate. Preserved log and external draft; annotated only
those two binders as LiveBuffer. No failed-build audit is evidence.
Reading Safety.lean also found existing size facts in the Safety namespace:
the previous GridSizes search covered Model/Outputs only. The execution
namespace wrappers are valid, but the existing Safety facts should be
reused rather than independently maintained in future size work.

Added RejectedArenaState.lean with output slot1, exact rejected pool/heap,
whole-grid budget and status one. Added AdvanceLaterRejected.lean to
connect the complete one-node rejected advance to that state: slots2–5
remain free, the heap is unchanged, and no intermediate release occurs.

The typed rejection check rejects the bounded-quantifier syntax after a
parenthesized typed binder. Preserved that log/draft and wrote the two
predicates as explicit typed binders followed by membership implications.
This is a parser correction; no semantic or resource premise changed.

Added AdvanceFirstRejected.lean to establish the other terminal rejection
state from initialized slot0: one fresh status clone in slot1, empty free
list and next heap slot2. The explicit whole-grid budget suffices, and
old-grid/page preservation follows from the complete rejected call.

RejectedBuffers passes in3.6s, RejectedArenaState in3.6s and
AdvanceLaterRejected in3.7s, log euler-grid-advance-later-rejected-first.log.
AdvanceFirstRejected passes in3.7s, log euler-grid-advance-first-rejected-first.log.
All audits use standard logical axioms. Reviewed proofs and telemetry: the
only failed leaves were local binder elaboration/syntax, now explicit;
shared result-to-buffer lemmas retain both allocation choices without
re-proving runtime instructions. Updated plans, README, imports and notes.
The pending actual outer loop must additionally preserve and finally
release the original initialized output; current arena summaries do not
claim that missing composed boundary. No executable source/bytes changed.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Reviewed/stage/publish exactly devnotes.md, journal.md, plan.md,
plans/euler-rusanov.md, proofs/talos/lean/Project.lean and
EulerGridStep/{README.md,RejectedBuffers.lean,RejectedArenaState.lean,
AdvanceLaterRejected.lean,AdvanceFirstRejected.lean}.

### 2026-09-08: Unified arena advance outcomes

Published 0e620143dce9b2b8e276a5464b66369928b5eeed, sole parent
b9581224b5a8b05353cc8033566c4045461f0176, tree
a220cda0758ddaae861bd38d7d1b5217876c562b. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronization confirmed. Read the exact grid initialization and
existing allocator-window support to identify the next entry boundary;
no generated/source/toolchain files changed. Added ArenaAdvance.lean to
compose the four checked first/later and accepted/rejected cases into two
complete cell-call interfaces. This focused target integrates all new
arena modules without invoking the unrelated source aggregate.

ArenaAdvance first check passes the later-case theorem but needs explicit
normalization of UInt64.ofNat0 and zero-plus-index in the first-case
interface. Preserved the log/draft; added only those equality rewrites
and wrapped the long call lines. No failed-build audit is accepted.

ArenaAdvance passes in3.6s with standard logical axioms, log
euler-grid-arena-advance-normalized.log. Reviewed the integrated proof
and telemetry: the first-call literal normalization closes the only
interface mismatch; both complete outcome theorems compose the retained
checked cases. Updated imports, README and notes. This is a focused
integration boundary for all four arena paths, not a full grid-step or
exact-byte theorem. Initial allocation and outer-loop/final-release
composition remain open; source, generated bytes and runtime unchanged.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Reviewed/stage/publish exactly devnotes.md, journal.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,ArenaAdvance.lean}.

### 2026-09-08: Grid initialization allocator

Published 845bcb0c77048a163d929997d3651b24d382c61f, sole parent
0e620143dce9b2b8e276a5464b66369928b5eeed, tree
efdbcab3a124a9d799649a057f5b49c0274eb7b9. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronization confirmed. Read-only Node bracket inspection of the
exact Program finds19 top-level instructions, main iff at17, and102
instructions in the valid arm. Allocation is54..70, length/zero setup71..77,
outer loop92 and final initial-output release101. Added InitializationShape
with kernel-equality boundaries and InitialAllocationBump for the valid
entry's empty-free-list allocation window (params2, locals43). It reuses
checked generic metadata stores and bump facts; no Program edits.

InitializationShape passes with kernel equalities (some list metadata uses
propext); InitialAllocationBump passes in7.2s with standard logical axioms,
log euler-grid-initial-allocation-bump-first.log. Added FillState.lean
for constant-prefix initialization using the existing exact writeWord
semantics, with page/store frame and outside-payload byte preservation.
This supplies the invariant for the emitted zero-fill loop.

Added FillLoop.lean for the emitted constant-fill loop with arbitrary
local indices. It reuses the copy counter/frame/termination machinery,
removes the source-load boundary and advances the checked fill invariant
with each exact scalar store. The initial zero loop is its concrete
34/33/35/36 local-index instance.

FillState first check rejects prefix as a reserved declaration keyword,
causing downstream structure-constructor diagnostics. Preserved log/draft
and renamed that field to filled; no invariant or runtime behavior changes.
Failed-run axiom output is excluded.

FillState’s renamed invariant elaborates; the remaining diagnostic is an
incorrectly qualified get-element lemma name in the completed-array leaf.
Preserved log/draft and removed that nonexistent simp name, retaining the
valid-index simplification already supplied by the standard simp set.

FillState now passes with standard logical axioms. FillLoop reaches the
store address and needs the emitted stride-one multiplication simplified
before using copyRuntimeAddress. Preserved its log/draft and added exactly
UInt64.mul_one at that boundary. No timeout, budget increase or semantic
change. The source-copy loop did not contain this extra multiplication.

Added InitializationFill.lean to compose the exact valid-arm length store
and zero loop from arbitrary existing payload bytes. Its InitializedArray
result includes the replicated zero array, unchanged pages/non-memory
store and byte equality outside the length/payload footprint. No zeroed
allocation assumption is introduced.

FillLoop passes in3.6s with standard logical axioms, log
euler-grid-fill-loop-stride-one.log. InitializationFill passes in3.7s
with standard logical axioms, log euler-grid-initialization-fill-first.log.
Reviewed the five new modules and telemetry: the fill proof shares exact
word-store and counter/termination support, keeps arbitrary initial bytes
and supplies an outside-array frame. Allocator and initializer are checked
regions; entry guards/capacity/arena composition and outer-loop execution
remain open. Updated plans, imports, README and notes. The current changed
proof checks and small docs/registry checks are the full verification scope
for this proof-only checkpoint; no CLOB/runtime/full aggregate/release work.

The91 maintained Markdown files,34 registry/import entries, README links,
new-proof no-admission/no-trace/whitespace scan and git diff --check pass.
Reviewed/stage/publish exactly devnotes.md, journal.md, plan.md,
plans/euler-rusanov.md, proofs/talos/lean/Project.lean and
EulerGridStep/{README.md,InitializationShape.lean,InitialAllocationBump.lean,
FillState.lean,FillLoop.lean,InitializationFill.lean}.

### 2026-09-08: Arena and initialization publication receipt

Published 71e930645f3c7ec18ef3217c29f737955cea053b, sole parent
845bcb0c77048a163d929997d3651b24d382c61f, tree
ab9bd36d467838f233d787106cd3fbeee03518bf. Non-forced update/fetch, exact
commit/parent/message/tree/index/worktree checks and local CAS passed;
clean synchronization confirmed. This closes seven substantive incremental
checkpoints from5c9fb6b through71e9306. The complete cell/arena outcomes and
entry allocation/zero-fill regions are checked; guards, capacity arithmetic,
initialized arena and full loop/final-release composition remain open.
The current regression scope was only changed Euler targets and small
Markdown/registry/import checks, as requested. This single follow-up receipt
stages exactly journal.md and devnotes.md; it makes no new code/proof claim
and needs no repeated Lean or runtime checks. Its identity is verified
externally and will be recorded in the next substantive entry.

### 2026-09-09: Resume the complete agenda through a verified 2D visualization

The user requests the entire agenda without stopping before a polished 2D
visualization like the Lanyon post, and requires all WASM to be properly
verified. Reread AGENTS.md and plans/talosfp-euler-operations.md. The recovered
checkout is clean and synchronized at receipt 23afc282571f992468a2eb0b9878979f3b8bcb22,
parent 71e930645f3c7ec18ef3217c29f737955cea053b, tree
4ffad319fba044828d1a9de76b9d6897ec6e2cd9. This records the terminating receipt
from the preceding checkpoint; no receipt recursion is introduced.

Validated the executable ARM Mach-O paths selected by tools/macos-env.sh:
build/tools/lean-4.34.0-rc2-darwin_aarch64/bin/{lean,lake},
build/tools/wasm-tools-1.251.0-aarch64-macos/wasm-tools,
build/tools/wasmtime-v44.0.0-aarch64-macos/wasmtime and
build/tools/node-v24.13.0-darwin-arm64/bin/node (v24.13.0). No substitutions or
Darwin preload. Repository write and network access were granted for the
session. All proof checks retain tools/leanrun, --timeout 120s, one thread,
local execution and the approved inherited-priority fallback.

Read the primary https://lanyon.ai/research/euler-equations/ post. Its 2D
Riemann problem is a two-spatial-dimensional simulation, beyond the prior 1D
phase. Asked an asynchronous scope clarification and continued shared 1D
proof work; the stated default is a true 2D flow, subject to user steering.
The new request supersedes the earlier 2D non-goal. No claim is made that a
1D plot, host computation, or merely validated binary meets this requirement.

Read-only discovery included three incorrect path guesses: the ProofKit
root lacks Project/, FieldAllocation.lean is named AllocationChoice.lean,
and EulerConservativeSide is named EulerConservative. Those reads failed
without mutation; subsequent reads use discovered paths. No Python, remote
executor, CLOB check, full aggregate, release or cleanup operation was used.

Added InitialCapacity.lean for the actual valid-body instructions 36..53,
InitialDimensions.lean for instructions 0..35, and InitialMemory.lean for
owned metadata, disjoint input and exact allocator-counter preservation
through the completed zero fill. InitialCapacity reuses the normalized
capacity model and InitialDimensions reuses six_mul_guard/small_add_guard.
InitialMemory reuses generic byte frames rather than re-proving stores.

The first focused build of InitialCapacity and InitialDimensions is retained
in tmp/euler-recovery-20260907/euler-grid-initial-dimensions-capacity-first.log.
It found structure-field indentation/parser errors; the dimensions proof
also exhausted its existing 1,000,000 heartbeat budget in 43s. Preserved both
failed drafts outside the checkout with exclusive creation, corrected the
syntax and replaced a repeated broad simplifier with instruction-progress
peeling. No unchanged retry or budget increase. The reduced build log is
euler-grid-initial-dimensions-reduced-memory-first.log: capacity passes in
4.1s with propext, Classical.choice and Quot.sound; dimensions reaches a
nonzero-count branch; memory reaches global list lookups. Failed build axiom
output is excluded even when an individual declaration prints an audit.

Further retained logs are euler-grid-initial-dimensions-nonzero-memory-diagnostic.log
and euler-grid-initial-dimensions-branch-memory-counters.log. These isolate the
remaining instruction normalization and optional-versus-total global list
reads. The temporary memory trace was removed. Preserved failed drafts are
work/euler-grid-initialcapacity-first.lean and
work/euler-grid-initial{dimensions,memory}-{first,second,third,fourth}.lean
under the projectless task directory (the memory first draft is named second;
there is no memory-first file). All writes use exclusive new scratch names.
The next check uses exact getElem? witnesses for the counter frame and a
single bounded allocator-window normalization after instruction peeling.

The window-memory-get check proves InitialMemory with standard logical axioms.
The dimension proof then exposes two remaining representation details: the
division word must normalize before the nonzero branch, and its exact frame
must retain the three earlier header-read scratch assignments. Preserved the
fifth and sixth dimension drafts; division-normalization and exact-frame logs
retain both boundaries. InitialDimensions passes in 5.6s with only propext,
Classical.choice and Quot.sound. No generated Program or WASM changes.

The final focused acceptance command builds InitialCapacity, InitialDimensions
and InitialMemory together under the same 120s local runner into
euler-grid-initial-arithmetic-memory-acceptance.log, so no audit from an
overall failed invocation is used for publication. Updated Project imports,
README, both plans and concise notes; reviewed the final proof structure and
its telemetry. The exact initial counter result reuses existing byte frames;
the dimension theorem follows all emitted checked arithmetic under its stated
bounds. Entry dispatch and complete loop execution remain open.

The intended explicit checkpoint paths are journal.md, devnotes.md, plan.md,
plans/euler-rusanov.md, proofs/talos/lean/Project.lean and
proofs/talos/lean/Project/EulerGridStep/{README.md,InitialCapacity.lean,
InitialDimensions.lean,InitialMemory.lean}. Publication will use exact staged
blobs/tree, a sole current parent, force:false, fetch/content equality and CAS.

Final acceptance exits 0: all three focused targets pass and the public audits
contain only propext, Classical.choice and Quot.sound (or subsets). Existing
linter warnings are retained. The 91 Markdown files, 34 registry/import cases,
README links, changed-proof scans and git diff --check all pass. Reviewed
the exact nine-path diff; no runtime or unrelated regression gate is needed
for this proof-only checkpoint.

### 2026-09-09: Compose the initialized grid output

Published arithmetic/memory checkpoint 86de5ff99b8c782518d9981adc751f2a9b2118a0,
sole parent 23afc282571f992468a2eb0b9878979f3b8bcb22, tree
4ec863dfcbcab999b109d53f98784c8fb22ad1e5. The nine-path non-forced API
publication, fetch, exact parent/message/tree/index/worktree checks and local
CAS passed; clean synchronization confirmed. Added InitialOutput.lean to
compose actual capacity/allocation/length/zero-fill instructions into an
owned initialized output with exact heap/counters and separate input.

InitialOutput first check required making the transformed allocation frame
explicit: supplying the original hParams too early otherwise inferred the
original frame metavariable. Preserved euler-grid-initial-output-first.log
and the same-named scratch draft; euler-grid-initial-output-explicit-frame.log
passes in 5.1s with standard logical axioms. Added InitialArena.lean to compose
dimensions and initialization from the whole-grid cells+6 budget, producing
slot0 ownership and heap slot1 for the first-cell theorem.

InitialArena first check reached the final heap identity but a simp rewrite
from numeral 1 to 0+1 recursively reapplied itself. Preserved the draft and
euler-grid-initial-arena-first.log; replaced it with one instantiated
arena_heap_succ rewrite, without raising recursion or heartbeat limits.
The corrected euler-grid-initial-arena-single-heap-rewrite.log passes in 4.8s
with propext, Classical.choice and Quot.sound. InitialOutput passes in the
same successful dependency chain. A separate read-only attempted Defs.lean
path in the pinned interpreter did not exist and changed nothing.

Reviewed the new composition: no allocator algorithm or generated bytes
changed. The existing whole-grid budget discharges dimension/space bounds;
the theorem establishes the exact first-cell precondition rather than
assuming a preinitialized output. Updated imports, README, plans and notes.
Checkpoint paths are journal.md, devnotes.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,InitialOutput.lean,
InitialArena.lean}. Only the two focused targets and small docs/registry
checks apply; no broad runtime, release or aggregate check is introduced.

### 2026-09-09: Exact grid entry guard dispatch

Published initialized-arena checkpoint 108bfd405bb3c71b27708d13e48e590b5e4b37c1,
sole parent 86de5ff99b8c782518d9981adc751f2a9b2118a0, tree
5c4c3aacb18de4ba138c4c68069cb7c62796037d. Focused proofs, 91 Markdown files,
34 registry/import cases, README links and proof/diff scans passed.
Eight-path non-forced API update/fetch, complete commit/parent/message/tree/
index/worktree verification and local CAS passed; clean synchronization.
Added EntryGuards.lean for the exact positive-ratio, empty-array and remainder
short-circuit prefix, reusing the complete positiveBits call and array reads.

EntryGuards first check needed list-append normalization before the actual
positiveBits call. Preserved draft/log; euler-grid-entry-guards-append.log
passes in 6.5s with standard logical axioms. The prefix handles bad ratio,
empty input, malformed length and the valid branch with exact scratch state.
Read-only bracket parsing identified all 57 invalid-arm instructions. Added
InvalidEntryShape and InvalidEntryAllocation for its distinct local window,
reusing the accepted fresh-allocation proof structure and generic metadata
stores. The exact local remap is allocator window30 to28, capacity39 to37,
selected44 to42, with the returned root in local33; generated code is unchanged.

InvalidEntryShape and InvalidEntryAllocation pass in 4.6s and 7.3s with
standard logical axioms. Reviewed the frame remap before building, including
multiline set calls. InvalidEntry reuses the exact two-store singleton pattern
but proves reads through read64_write64_exact, avoiding the native memory
shortcut in the older generic singleton theorem. The first singleton check
reached only the two runtime memory guards; preserved its log/draft and added
explicit negated bounds using Nat.not_lt.mpr. The corrected
euler-grid-invalid-entry-store-bounds.log passes in 4.1s with standard axioms.

RejectedEntryExecution composes guard dispatch, the invalid body and function
return. Its first check left one unconstrained length argument in the constant
parameter-count lemma. Preserved draft/log and instantiated all guard-frame
arguments explicitly. euler-grid-rejected-entry-execution-frame-arguments.log
passes in 3.0s, including all dependencies, with only propext, Classical.choice
and Quot.sound. This is a complete function36 theorem for entry rejection,
not a whole valid-grid or exact-byte claim. No Program, WASM, compiler, runtime
or trusted-base changes occurred. Reviewed the five modules and shared proof
use, updated imports, plans, README and notes.

The intended eleven checkpoint paths are journal.md, devnotes.md, plan.md,
plans/euler-rusanov.md, proofs/talos/lean/Project.lean and
EulerGridStep/{README.md,EntryGuards.lean,InvalidEntryShape.lean,
InvalidEntryAllocation.lean,InvalidEntry.lean,RejectedEntryExecution.lean}.

### 2026-09-09: Preserve the initial output for the outer loop's final release

Published entry rejection checkpoint 0bb336db352625d989515997e32254059ae0b22a,
sole parent 108bfd405bb3c71b27708d13e48e590b5e4b37c1, tree
70fa7ad68ade01a7f44cdf1503dfb6aa8c46fe54. Eleven-path non-forced update/fetch,
commit/parent/message/tree/index/worktree equality and CAS passed; clean sync.
The focused dependency chain, 91 Markdown files, 34 registry/import cases,
README links, proof scans and diff checks all passed before publication.
Added ProtectedBuffer.lean and MixedWriterProtected.lean to retain a separate
owned array across each field clone and intermediate release, then through
the complete mixed writer. This is needed for actual function36's release
of the initial output after the loop, which the prior current-output-only
arena summaries did not retain. No claim or change to per-iteration release
behavior is made: previous result objects continue to occupy the arena.

ProtectedBuffer and MixedWriterProtected pass in 3.5s and 3.6s with standard
axioms, log euler-grid-mixed-writer-protected-first.log. AdvanceMixedProtected
and AdvanceLaterProtected pass in 3.6s and 3.7s, retaining both the prior output
array for the emitted post-body condition and the initial owned output for
final release; log euler-grid-advance-later-protected-first.log.
AdvanceFirstPreserved, AdvanceFirstRejectedPreserved and
AdvanceLaterRejectedProtected each pass in 3.8s; their shared focused log is
euler-grid-advance-preserved-first-rejected.log. The first-cell cases recover
initial ownership from the exact live-buffer postcondition; the later rejected
case uses the complete field-result byte frame. All audits are standard.
Added ProtectedArenaAdvance to combine both outcomes for the first and later
cells while retaining these observations. No new numerical computation or
source/byte changes.

ProtectedArenaAdvance passes in 3.7s with standard logical axioms; the complete
successful dependency-chain log is euler-grid-protected-arena-advance-first.log.
The eight new modules pass on their first focused checks. Reviewed proof
structure and telemetry: generic field/release frames and the existing framed
writer remain the shared execution machinery, while the new wrappers preserve
observations previously discarded by narrower arena summaries. Those prior
checked interfaces remain intact as examples and callers. This supplies the
actual post-body reads and final-release ownership needed by the next loop
proof, without changing allocator behavior or treating prior outputs as freed.

Updated Project imports, README, plans and notes. Intended checkpoint paths
are journal.md, devnotes.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,ProtectedBuffer.lean,
MixedWriterProtected.lean,AdvanceMixedProtected.lean,AdvanceLaterProtected.lean,
AdvanceFirstPreserved.lean,AdvanceLaterRejectedProtected.lean,
AdvanceFirstRejectedPreserved.lean,ProtectedArenaAdvance.lean}. Only focused
Euler builds and the small docs/registry/import/proof scans are applicable.

### 2026-09-09: Outer-loop invariant construction

Published protected cell outcomes as a43301ba81bca88cfbc844d9be9e329cb0376f25,
sole parent 0bb336db352625d989515997e32254059ae0b22a, tree
dccda950eee92167cbcf41a80a04c23906c8ac12. Fourteen-path non-forced update,
fetch/content/parent/message/tree/index checks and local CAS passed; clean
sync confirmed. The 91 Markdown files, 34 registry/import cases, README links
and changed-proof/diff scans passed. Added GridLoopModel for the remaining
pure recurrence and exact output header, plus GridLoopStorage for initial,
accepted and stopped storage phases and their common pointer/pool/heap facts.

First focused loop model/storage build failed with two local elaboration
diagnostics: simplification unfolded set! before its supplied self-read lemma,
and the live-buffer projection left its buffer implicit. Preserved both drafts
as work/euler-GridLoop{Model,Storage}-first.lean in the task workspace. Applied
the existing rejected-header simpa pattern and supplied the explicit live
buffer. Failed invocation audits are not acceptance evidence.

The corrected GridLoopModel and GridLoopStorage focused build passed, with
only standard logical axioms (storage 3.7s). Added GridLoopTransition to
identify the next canonical pointer and construct the next storage phase from
either checked cell outcome. No WASM/source changes.

GridLoopTransition passes on its first 3.8s check with standard axioms. Added
GridLoopAdvance to dispatch the storage phase into the already checked first
or later call and to retain the initial buffer and the old output after that
call. Its stopped phase is excluded by the explicit zero-status premise.

GridLoopAdvance first check reported dependent case-pattern names already
substituted by existing theorem arguments and an equality composed backwards.
Preserved its draft in task work/euler-GridLoopAdvance-first.lean and used the
existing argument names and corrected composition. Added exact loop extraction
(GridLoopShape) and explicit frame, scratch updates, invariant and decreasing
measure (GridLoopFrame). The invariant keeps the zero-filled initial owned
buffer separately from the current output.

The frame dependency check reached a recursion diagnostic in the broad rfl
region decomposition (GridLoopShape), after the corrected advance compiled.
Preserved the failing shape draft and replaced whole-program reduction with
three standard list decomposition steps using the already checked indexed
loop shape; no recursion/heartbeat limit was increased. Audits from this
failed invocation are not the acceptance gate.

The reduced shape proof exposed an unavailable Nat.reduceMin simp name;
preserved the second draft and replaced it with the explicit closed minimum
equality and the existing addition reducer. No semantic boundary changed.

The final focused chain passed in euler-grid-loop-frame-minimum.log:
GridLoopShape 3.9s and GridLoopFrame 3.8s, with accepted standard logical axioms
for all six new modules and replayed dependencies. Reviewed their proof
structure and diagnostics: generic list decomposition replaces deep whole-code
reduction; the complete cell call supplies memory facts through the existing
framed writer, with no duplicated execution semantics. Harmless simp/linter
warnings remain visible in the retained logs. No source, Program or WASM
changed. Updated Project imports, README, plans and concise notes. Intended
checkpoint paths: journal.md, devnotes.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep/{README.md,GridLoopModel.lean,
GridLoopStorage.lean,GridLoopTransition.lean,GridLoopAdvance.lean,
GridLoopShape.lean,GridLoopFrame.lean}. Next is the actual loop body/termination
composition. Apply only small docs/import/changed-proof checks for this
proof-only checkpoint.

### 2026-09-09: Exact outer-loop execution

Published the loop storage checkpoint as 16c1d68b4e4fc07ab5504252bf2eb72da1122cfd,
sole parent a43301ba81bca88cfbc844d9be9e329cb0376f25, tree
5a2b5a7b8c4f1eae07cf1029aba0783e742efa9f. Twelve explicit paths, non-forced
update, fetch/parent/message/content/tree/index checks and local CAS passed;
clean synchronization confirmed. Small docs (91), registry/import (34), README
links and six changed-proof scans passed before staging. Added GridLoop.lean
to compose the exact body using the checked cell transition, separate before/
after memory-read facts, the decreasing measure and a final no-call iteration.

The first loop check failed in 5.5s with an unavailable UInt64.ofNat_zero
name and mismatches caused by default simplification of word division, array
status indexing and output-size substitutions before matching the memory
facts. Preserved the complete draft in task work/euler-GridLoop-first.lean.
Replaced the closed zero name by rfl, prevented premature division/index
rewrites and normalized the before/after read facts to the actual frame
expressions. No budget increase or unchecked execution claim.

The normalized loop check ran 11s and left only the decreasing-measure goal:
the successor word-to-Nat equality was proved but not supplied to its simp
step. Preserved the second draft and supplied hSuccNat explicitly while
retaining the encoded addition. Every body branch had elaborated, but only a
successful invocation can accept the full theorem. Added GridFinalGeometry
to show the final current root and all remaining free-list nodes are
separate from initial slot zero.

The complete loop and final geometry focused invocation passed:
euler-grid-loop-successor-final-geometry.log, 12s for grid_loop_spec and
3.6s for geometry. All audits contain only propext, Classical.choice and
Quot.sound or subsets. This proves exact loop termination through numerical
rejection and the extra no-call exit iteration, with the finite recurrence as
result and bounded ownership maintained. Reviewed telemetry: precise memory
facts allowed the existing WP engine to handle the body without another
execution abstraction or a larger budget. Added GridFinalRelease to compose
the actual release40 call using separation of root0/current/free nodes and
to establish that every terminal nonempty run has advanced at least once.

The final-release first check found an unavailable Array.getElem!_replicate
name in the terminal-index helper; preserved its draft and used the ordinary
replicate simplifier. The release-call proof itself elaborated, but the whole
invocation must pass. Added GridFinish to connect the exact post-loop return
staging and nonzero-root release guard to that checked call.

The final wrapper first check stopped before matching its release call; the
extracted drop/append program had not been normalized by the loop-only tactic.
Preserved GridFinish-first and added only the explicit list normalization
needed for this concatenated region. The corrected release helper compiled
in the dependency chain; acceptance remains the successful full check.

Correction: explicit append normalization did not resolve the wrapper call
match (3.7s); the prior explanation was a hypothesis, not an established
cause. Preserved the second draft and added one local goal trace to inspect
the exact remaining WP boundary before changing the proof further.

The exact goal trace confirms the nine-instruction finish region remains
behind append after the first peel exposes it. Preserved the traced draft
and normalized that now-visible append before a second peel; removed the
trace from the maintained proof. Also inspected generated export tables:
stepCheckedBits is directly function36 and maxSpeedCheckedBits directly11;
37/12 begin runtime utilities, not extra numerical-entry wrappers. The
maintained runner must account for any utility export it actually invokes.

The final finish check passes in euler-grid-finish-exposed-append.log, with
standard logical axioms throughout the complete loop/release/finish dependency
chain. Reviewed the full accepted proof and telemetry: exact emitted loop
semantics use the earlier framed cell-call theorem, and release uses shared
owned-buffer/free-chain machinery. No changed source, Program or binary; no
new axioms, trusted-base changes, or broader regressions. Updated Project
imports, README and both plans to distinguish checked loop/final regions from
the remaining full entry composition. Intended checkpoint: journal.md,
devnotes.md, plan.md, plans/euler-rusanov.md, proofs/talos/lean/Project.lean,
and EulerGridStep/{README.md,GridLoop.lean,GridFinalGeometry.lean,
GridFinalRelease.lean,GridFinish.lean}. Apply the small docs/import/link/proof
scans, stage only these ten reviewed paths and publish an exact fast-forward.

### 2026-09-09: Complete grid entry composition

Published loop/final release as 4ebfeb8f3b9bf8b42b12f503ddd8cde81c4faed6, sole
parent 16c1d68b4e4fc07ab5504252bf2eb72da1122cfd, tree
0b1a8dfd299b6baad8892002553f80b18353be0b. Ten explicit paths, non-forced update,
fetch/content/parent/message/tree/index verification and local CAS succeeded;
clean sync confirmed. The 91 docs, 34 registry/import cases, README links and
four changed-proof scans passed before publication. Added GridSetup for the
exact fourteen-instruction initialization-to-loop handoff and the concrete
entry frame equality, isolated from the full entry proof.

GridSetup passes on its first 3.8s focused check with standard axioms. Added
GridInitialFacts for its concrete frame facts and valid-entry model guards,
and GridValidBody to join initialization, the fourteen-instruction setup,
the exact loop and final release into the complete valid branch. The body
theorem retains a continuation over its actual return frame and array.

The valid-branch dependency check found only a conjunction-association
mismatch in grid_valid_cells (3.5s). Preserved its draft and added and_assoc
to the guard simplification; concrete initialization frame facts elaborated.

GridInitialFacts and the complete valid-branch composition both pass in 3.7s
with standard axioms. Added GridEntryReady to state the exact host-visible
array, page, arena, counter, empty-free-list and separation assumptions and
its invalid-singleton bound. Added GridExecution to compose the complete
export for valid entry and unify all invalid ratio/shape paths with the
already checked rejection function. These declarations cover all raw inputs
under the stated memory preconditions, including numerical cell rejection.

GridEntryReady and GridExecution pass on their first 3.8s checks. The complete
stepCheckedBits_exact_in_module and valid-entry theorem audit to standard
logical axioms. Added public ExactSpecFor/SafeSpecFor and both registered
behavior declarations in Spec.lean, explicitly quantifying the bounded arena
preconditions and transferring accepted payload state/Courant safety.
Source registration remains incomplete until this public target and its
focused source/WAT gate pass. Exact bytes are the following separate gate.

The public Spec target passes in 3.6s; both registered behavior audits contain
only propext, Classical.choice and Quot.sound. Marked euler_grid_step complete
and added its public Spec plus new composition modules to Project imports,
pending the focused tools/talos-proof.js check euler_grid_step source/WAT gate
before publication. Expected Program SHA c05b49f9b1dcbeeb1b17beb5477e321a48796a34bcb7c29b19125ce5c034560f
and WASM SHA bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297
(8,866 bytes) are unchanged. An inventory search named nonexistent
docs/verifying-artifacts.md and made no mutation; recovered the actual
docs/verifying.md through rg --files before further inspection.

Updated current inventories and grid completion claims in README, DEVELOPING,
docs/{status,spec,verifying}.md, proofs/talos/README.md, both plans and the grid
README. Counts are 34 complete source cases/34 Program caches/29 packages,
with fourteen completed raw-bit floating-point registrations. Kept historical
aggregate results and the pending current aggregate explicit. The new grid
inventory row records all memory assumptions and leaves exact-byte freezing
pending. The source/WAT gate remains running; publication waits for it.

The focused source gate passed with exit zero in
euler-grid-full-source-gate-first.log: pinned compiler regeneration, exact
tracked WAT-model comparison and completed public Spec build all passed. No
full source/artifact aggregate or unrelated regression was run. The initial
JSON serialization expanded unrelated single-element registry arrays; saved
that draft in task work/euler-grid-cases-expanded-draft.json, verified parsed
equality to the sole intended complete-flag change, and retained the original
registry formatting with only that flag changed. Fixed the new inventory row
to remain in its existing Markdown table. Intended explicit checkpoint paths:
README.md, DEVELOPING.md, docs/{status,spec,verifying}.md, proofs/talos/README.md,
proofs/talos/cases.json, proofs/talos/lean/Project.lean, plan.md,
plans/euler-rusanov.md, devnotes.md, journal.md and
EulerGridStep/{README.md,GridSetup.lean,GridInitialFacts.lean,GridValidBody.lean,
GridEntryReady.lean,GridExecution.lean,Spec.lean}. Exact-byte packaging follows
publication of this complete source/WAT checkpoint.

### 2026-09-09: Grid exact-byte package and invoked reset coverage

Published complete grid source/WAT proof as 6c987917df904a382cce8e61bc6a1d8c533262bd,
sole parent 4ebfeb8f3b9bf8b42b12f503ddd8cde81c4faed6, tree
f465b85434b00e7d70ef0fd96832886bdb5d15bc. Nineteen explicit paths passed the
non-forced update, fetch/parent/message/content/tree/index verification and
local CAS; clean synchronization confirmed. Small docs (91), registry/import
(34/34, fourteen FP), six changed-proof scans and unchanged Program/WASM SHA
checks passed. Preparing exact bytes now. The planned maintained runner can
write input memory from the host and invoke the proved numerical exports;
added GridReset to verify the only additional intended WASM utility call,
reset38. It resets six allocator globals without touching memory, and its
ready-state lemma reconstructs the step preconditions at base4096. Added the
public reset contract before freezing so the package can cover this actual
repeated-step execution path as well.

Reset first check (3.5s) needed explicit valid-index witnesses for the six
existing global slots and a discharger for bounded set/get reductions.
Preserved GridReset-first.lean in task work and supplied those finite index
facts; no runtime instruction or memory behavior changed.

The reset execution now elaborates; ready-state simplification leaves the
five explicit index inequalities as goals. Preserved the second draft and
closed those residual arithmetic goals after the bounded simplifier.

The complete reset/ready and public Spec check passes in
euler-grid-reset-ready-arithmetic.log (3.8s and 3.7s); all three public
behavior declarations use standard logical axioms. Registered reset_exact
and its Project import. Prepared task work/freeze-euler-grid-step.mjs by
adapting the previously reviewed scoped scan freezer for exactly the nine
new grid-step package paths, 29 preserved packages, one new registry row and
one CheckFile arm/import. It checks the 8,866-byte SHA, expected-path
membership, exclusive output creation and unchanged verifier/release/earlier
manifest/WASM identities. It invokes only serialized pinned local decoder
preparation, not migration/cleanup of existing packages.

Created nine fresh grid-step exact-package files using the output
preparer, with exclusive writes and exact expected-path membership. Added
one registry row and one CheckFile import/arm. All 29 prior manifest/WASM
pairs and the protected historical release draft remain byte-identical.
The verifier source did not change. This is pending the focused package gate.

{
  "case": "euler_grid_step",
  "sha256": "bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297",
  "byteLength": 8866,
  "newFiles": [
    "proofs/talos/lean/Project/EulerGridStep/ArtifactBytes.lean",
    "proofs/talos/lean/Project/EulerGridStep/ArtifactCache.lean",
    "proofs/talos/lean/Project/EulerGridStep/ArtifactDecoded.lean",
    "proofs/talos/lean/Project/EulerGridStep/ArtifactRawCache.lean",
    "proofs/talos/lean/Project/EulerGridStep/ArtifactDecode.lean",
    "proofs/talos/lean/Project/EulerGridStep/ArtifactValidation.lean",
    "proofs/talos/lean/Project/EulerGridStep/ArtifactTranslation.lean",
    "proofs/artifacts/euler_grid_step/bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297/manifest.json",
    "proofs/artifacts/euler_grid_step/bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297/program.wasm"
  ],
  "oldPackagesUnchanged": 29,
  "protectedRelease": [
    "proofs/artifacts/release.json",
    "fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1"
  ]
}

The exact-byte artifact theorem and embedded-byte comparison have passed;
the scoped package driver is walking its 191 local behavioral dependencies
before final declaration checks. In parallel, without another Lean process,
created and ran task work/sod-frozen-grid-preliminary.mjs using only the
frozen scan export11 and grid exports36/38. The 100-cell run reaches t=0.2
in 93 accepted steps, all 300 final words match the independent host oracle,
max rounded CFL is 0.4500000000000001, minima are density0.125/pressure0.1.
Input at519728 is beyond the reserved arena ending519680, within 1MiB;
observed per-step counters are601 allocations/501 releases/501 frees. Saved
the full raw history and result with exclusive creation. This is runner
prototype regression evidence, not the maintained runner theorem/data gate.
Prepared separate frozen-runtime/reference/refinement drafts in task work to
check N100/200/400/800 against the independent exact-Riemann cell averages
while the single package gate remains serialized.

The complete scoped package gate exited zero in euler-grid-package-first.log.
It checks the matching 8,866 embedded bytes, the exact artifact theorem, all
191 local behavioral dependencies, the public Spec target and all eight
manifest theorem declarations. The decoder/validation cache witnesses use
the existing generated native-decision policy; decode_sound/validate_sound,
translation equality, and all three execution/safety/reset behavior audits
meet their accepted axiom policies. No full aggregate, release, conformance
or unrelated regression was run. Earlier package pairs and release/verifier
identities remained protected by the freezer. Updated all current maintained
package inventories to30 and closed the exact-grid-byte agenda row. Added
explicit reset and byte-proof scope to the grid README. New package files
are still the freezer's exact nine paths; no existing package was replaced.

Pre-publication checks: node tools/check-docs.js passed 91 maintained files;
loadRegistry/checkAggregateImports passed; all30 artifact manifests passed
metadata validation. The Program and historical release hashes remain exactly
c05b49f9b1dcbeeb1b17beb5477e321a48796a34bcb7c29b19125ce5c034560f and
fae0891f6c0694dae3d0b7855c8844e3cab12cf0277634b4d272dc78c88256f1.
GridReset/Spec contain no sorry/admit/newaxiom or trace; links resolve and
git diff --check passes. Frozen refinement finished: N100/200/400/800 use
93/190/385/774 accepted steps, each final raw grid matches the independent
host implementation. L1 density errors decrease .023762708/.016645769/
.010889543/.006977522; momentum and energy errors also strictly decrease.
All reported CFL maxima are .4500000000000001. This is numerical validation.

Reviewed explicit checkpoint staging: DEVELOPING.md, README.md, devnotes.md,
docs/spec.md, docs/status.md, docs/verifying.md, journal.md, plan.md,
plans/euler-rusanov.md, proofs/artifacts/registry.json, proofs/talos/README.md,
proofs/talos/cases.json, proofs/talos/lean/Project.lean,
proofs/talos/lean/Project/Artifact/Binary/CheckFile.lean, and the grid README,
Spec, GridReset, seven generated Artifact modules and exact manifest/WASM
pair listed above. Publish as “Freeze and independently verify Euler grid-step WASM”.

Published exact-grid checkpoint 783412ef92193baa76c4fcc640fb7e1744dee693,
sole parent6c987917df904a382cce8e61bc6a1d8c533262bd, tree
719be03360c40671d9fc938b5726f2d4480c626b. The nonforced API update, fetch,
commit/parent/message/tree/index/worktree equality and CAS local ref passed;
status clean. Closed publication session93776 and refinement session80202.

Created only EulerGridStep/Runner.lean for the generic checked recurrence.
It projects the conservative fields and stops before copying rejected output;
the intended inductive certificate records exact IEEE outputs, finite/admissible
intermediate grids and each output's pressure/speed/CFL safety. Raw ratio
selection and host execution remain explicitly separate from this pure proof.

Runner first focused build failed in5s on a nonexistent Array-qualified
getElem!_pos and normalization of the zero-field projection. Preserved the
exact draft in task work/euler-Runner-first.lean; use the global theorem and
normalize h0 before rewriting. Failed-build axiom output is not accepted.

Runner projection/recurrence build passes in3.8s; both public audits use only
propext/Classical.choice/Quot.sound. Added RunnerExecution.lean: a separate
WASM call trace transfers the exact grid-step contract at every recurrence
step, universally over correctly prepared host stores. The stationary100-cell
Sod corollary specializes initial raw words without unrolling a numerical run.

RunnerExecution first build rejected the induction nil pattern: cells is a
fixed parameter, leaving one constructor binder. Preserved the draft; use
the single input binder and infer cells. No audit accepted from this failure.

Added ArtifactRunner.lean to transfer the generic recurrence contract through
the existing exact-byte theorem, without modifying any frozen package bytes
or manifest. Added Runner/RunnerExecution imports and their scope to README.

RunnerExecution passes in3.7s with standard logical axiom audits for both
generic and Sod-specialized public declarations. ArtifactRunner passes in3.7s
and adds only the existing three native decoder/validation cache witnesses.
Logs: euler-runner-projection.log, euler-runner-execution-induction.log,
euler-runner-artifact-first.log. Reviewed the89-line recurrence,58-line call
bridge and15-line byte transfer alongside telemetry; reuse of the per-call
contract and pure induction avoids redoing allocator or instruction proofs.
No new automation or source-case registration is needed: this composes the
existing exact grid module without changing its bytes. Scope now splits the
completed recurrence proof from pending maintained runtime/data publication.

Stage exactly journal.md, devnotes.md, plan.md, plans/euler-rusanov.md,
proofs/talos/lean/Project.lean and EulerGridStep README.md, Runner.lean,
RunnerExecution.lean, ArtifactRunner.lean. Intended checkpoint:
“Prove guarded Euler runner traces and intermediate-state safety”.

Published runner checkpoint d9f1ad801b61b35db230a0f3a80e938e0cc4ffc4, sole
parent783412ef92193baa76c4fcc640fb7e1744dee693, tree
2c5a7f7362cf2c4e590c1e038390f56509e8c913; all nonforced publication, fetch,
identity/index/worktree/CAS checks passed and status clean. A read-only
exploratory examples directory lookup was absent; no state changed.
Created maintained tools/euler-sod-oracle.mjs, euler-sod-riemann.mjs and
euler-sod-runtime.mjs from the retained successful prototypes. Runtime loads
only the two frozen verified modules, calls only scan11/step36/reset38, checks
the explicit arena layout and allocator counters, and records raw ratios,
outputs, extrema and host-derived boundary-flux balance diagnostics. It
compares every final conservative word to the independent host oracle.

Created tools/euler-sod-data.mjs and exclusively generated six canonical files
in data/euler-sod-v1: raw.json, summary.json, cells.csv, history.csv,
refinement.csv, cell-averages.svg. Write log euler-sod-data-write-first.log
passes all4 resolutions, full word matches, per-step guards/counters, strictly
decreasing conservative L1 errors and balance equality to the independent
host oracle. Raw100-cell outputs are captured at every accepted step.
Rendered the SVG using the already bundled Sharp library to the task outputs
euler-sod-100-cell.png, visually inspected all six panels, axes, title,
legends, numerical limits and proof-scope footer: legible and unclipped.
Copied that derivative exclusively to the dataset as cell-averages.png and
added its README with reproducibility, exact-byte contracts and host boundary.
PNG SHA256 d113f943caa9936646365fee905a3946b5365afc8b16e9715b1833682b31c9f7.

Canonical check euler-sod-data-check-first.log exited zero: rerunning every
resolution reproduces all six text files byte for byte. No further numeric
regression is necessary for these unchanged verified kernels. Updated the
Euler/root plans, status and grid README to close the1D runner/data scope.
Reviewed generated columns, raw word fields, source provenance and plot.
Checkpoint files and SHA256:
tools/euler-sod-data.mjs 6b48ea7ccf47047dfa2f9a07db37eaef7ad33482fbb62cd7c4b59c9a71e5ce46
tools/euler-sod-runtime.mjs 6ecf112582587f74bf1b0e29fd630b182d98cdedad6d39e989465fc32732c3a9
tools/euler-sod-oracle.mjs 1e67a363b2135711d83705f3507c22c6d0cfc17148e4baae1db0415c5a1f0545
tools/euler-sod-riemann.mjs 9c85ce5c2cdd82375a4c5c9abec24b208256478be438076535fdd7c0e0b1e8ad
data/euler-sod-v1/raw.json 4f74f8d88c1e24496801c1d4461a19d619e816a822de21556b89f37edd2a89e6
data/euler-sod-v1/summary.json 306ba46c61d2ac0ce5ab336e133f072d8dba9c6c8b4da20b3538780d6d7df061
data/euler-sod-v1/cells.csv c87789d159a79e209c8a9912906ea8842effcc92a834433df0b60a2ce1df1735
data/euler-sod-v1/history.csv 0700e5fb42ceb6334432fd6c0d798e93ec18d625ed6c158e907a23ce80baaa44
data/euler-sod-v1/refinement.csv 79e39b182339aea99272216f8a87a1300ef3bfb3380fec62f20d793e034fe5a9
data/euler-sod-v1/cell-averages.svg 021bfa33446ea7a178befa71ec346f36397a39839f8da01c32691cf6478ca3ce
data/euler-sod-v1/cell-averages.png d113f943caa9936646365fee905a3946b5365afc8b16e9715b1833682b31c9f7
data/euler-sod-v1/README.md 193e621b528434298460257ac4af58154e706d5b1552b151f552e98288215863
Stage exactly these12 paths plus journal.md, devnotes.md, plan.md,
plans/euler-rusanov.md, docs/status.md, and the grid README.md. Intended
checkpoint “Publish reproducible verified Sod runs and refinement plots”.
