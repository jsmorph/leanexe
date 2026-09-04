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
