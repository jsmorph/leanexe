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
