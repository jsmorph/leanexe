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
