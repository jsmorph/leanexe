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
- Treat the scratch workspace as disposable.  External workspace maintenance
  already deleted the first checkout, including `.git`; it was not initiated
  by the user or by a repository command.  Do not run workspace cleanup or
  delete, reset, or overwrite user files.  Inspect repository status before
  mutations, preserve unrelated changes, and commit and push every coherent
  checkpoint promptly so another external prune cannot erase accepted work.
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
   was already removed by external workspace maintenance.  Scratch and ignored
   caches are therefore treated as disposable, while every coherent source or
   proof checkpoint is journaled, committed, and pushed promptly.  Unrelated
   user changes are preserved.
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
