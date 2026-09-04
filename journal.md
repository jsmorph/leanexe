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

