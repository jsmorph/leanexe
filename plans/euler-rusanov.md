# Verified Euler Rusanov Data

**Status:** Active on branch `talosfp-euler`.  The exact conservative flux,
genuine Fréchet Jacobian, and complete strictly ordered eigenbasis are proved
and integrated; the decoded finite-volume error layer is complete and direct
compiled-update WebAssembly is next.  This document
expands phase 8 of the root [Development Plan](../plan.md).

## Purpose

Build a small but substantive compressible-Euler numerical artifact whose
floating-point behavior is proved for the generated WAT and for the exact
distributed WebAssembly bytes.  The first artifact is a guarded one-dimensional
ideal-gas Rusanov flux followed by one fixed Sod finite-volume step.  It emits
raw binary64 result words from WebAssembly; a separate host presentation tool
may render those words as CSV or a plot.

This phase does not attempt to verify a complete CFD solver or claim that a
finite grid is the entropy solution of the Euler PDE.  Its initial claim is
narrow and executable:

> The exact registered WebAssembly module terminates, implements the specified
> IEEE-754 Rusanov calculation, returns only finite results on its accepted
> domain, and satisfies explicit real-valued roundoff bounds.

## Motivation and comparison target

The public Lanyon `CompressibleEuler` repository contains generated local
flux, wavespeed, artificial-wave, fluctuation, and reconstruction kernels.  Its
six C entry points end in placeholder `main` functions and do not contain a
mesh, boundary conditions, a CFL policy, a finite-volume update loop, a stopping
rule, or a data writer.  Consequently the repository cannot reproduce the
simulation figures in the accompanying research note.

The open reports identify three failures that set the acceptance criteria for
this work:

- the generated Lean theorems use `Real`, while a cancellation example accepted
  by the C validator makes a positive exact internal energy negative in
  binary64 and then produces NaNs;
- C `fmax` can suppress a one-sided NaN, select the wrong Lax--Friedrichs speed,
  reverse a fluctuation sign, and still pass the generated self-checks; and
- the generated hyperbolicity propositions merely witness that already-real
  scalar expressions are real and do not state an eigenvalue equation or a
  complete eigenbasis for the flux Jacobian.

Componentwise minmod reconstruction is outside the first phase.  A published
counterexample constructs a negative-internal-energy reconstructed state from
three individually admissible states.  Reconstruction enters only after an
invariant-domain-preserving formulation has its own theorem.

## Existing LeanExe and Talos foundation

The `talosfp` parent already supplies:

- `UInt64` bit-pattern intrinsics for binary64 addition and multiplication;
- native compiler lowering through the reinterpret/add-or-multiply/reinterpret
  instruction sequence;
- independent binary decoding, validation, validity, and Talos translation for
  `f64.add`, `f64.mul`, and both i64/f64 reinterpretations;
- scalar multiplication, guarded two-term dot, and runtime-length dot source
  and generated-WAT theorems;
- reusable raw-bit range reasoning, finite-result/error composition, checked
  array loads, loop invariants, and fuel-independent store-preserving execution;
  and
- Talos IEEE64 subtraction, division, and square-root semantics and numerical
  theorems for the later conservative-state solver.

The multiplication, dot, and Horner floating-point cases are source-driven
generated-WAT proof cases.  Euler is now the first f64 case registered in
`proofs/artifacts/registry.json`: its exact 1,808-byte module exercises the
complete decode, validation, Talos-translation, and behavior path rather than
calling regenerated WAT alone a verified distributable binary.  This proves the
behavior of the frozen bytes; it does not by itself prove a general
source-to-Wasm compiler-correctness theorem.

The existing guarded quadratic Horner checkpoint remains the final prerequisite
from phase 7.  It is completed before Euler implementation so the shared
add/multiply numerical layer reaches its already selected stable point.

## First kernel

Fix the ideal-gas ratio of specific heats to the exact real value

```text
gamma = 7/5.
```

The executable accepts left and right primitive states

```text
q = (rho, velocity, pressure)
```

as raw binary64 words and constructs the conservative state and physical flux
without division or square root:

```text
U(q) = (rho,
        rho * velocity,
        (5/2) * pressure + (1/2) * rho * velocity^2)

F(q) = (rho * velocity,
        rho * velocity^2 + pressure,
        ((7/2) * pressure + (1/2) * rho * velocity^2) * velocity).
```

For a fixed dissipation speed `alpha = 7/4`, the exact-real numerical flux is:

```text
H(qL, qR) = (1/2) * (F(qL) + F(qR) + alpha * (U(qL) - U(qR))).
```

The implementation evaluates the same real expression in a proof-friendly
dyadic order.  It forms `5/2 * p` as `(p + p) + (1/2) * p`, forms
`7/2 * p` by adding one more `p`, and evaluates the Rusanov result as

```text
(1/2) * (FL + FR)
  + (1/2) * (UL - UR)
  + (1/4) * (UL - UR)
  + (1/8) * (UL - UR).
```

This keeps every exact multiplication result below two and every exact sum
below four on the guarded domain, matching the ranges of the existing checked
IEEE64 rounders.  It uses only the admitted f64 addition and multiplication
operations and the exactly representable constants `1/2`, `1/4`, and `1/8`.
Binary64 negation is exact sign-bit toggling, and subtraction is addition of
the negated word.  The emitted accepted branch has exactly 22 `f64.mul`, 27
`f64.add`, and three `i64.xor` instructions.

The public result is a fixed structure containing a status word and the three
raw flux words.  Status zero denotes acceptance.  Rejection returns a distinct
status and zero payloads before executing any floating-point instruction.

## Guarded domain and signal-speed certificate

The initial guard is expressed entirely over raw bits and integer comparisons.
For each primitive state it enforces a normalized domain containing the
canonical Sod states:

```text
1/8 <= rho <= 1
1/16 <= pressure <= rho
abs velocity <= 1/2
```

All fields must be finite encodings, with density and pressure positive.  The
real proof interprets the accepted binary64 words as their exact dyadic values.
Because `pressure / rho <= 1`, the ideal-gas sound speed satisfies

```text
c = sqrt ((7/5) * pressure / rho) < 5/4,
abs velocity + c < 7/4 = alpha.
```

Thus the fixed executable dissipation is a proved characteristic-speed bound on
the whole admitted domain rather than a benchmark-specific guess.  The guard
also supplies explicit magnitude and headroom facts for every rounded event.

## Required theorem layers

### Real Euler mathematics

Define the mathematical primitive-to-conservative map, physical flux, flux
Jacobian, characteristic values, right-eigenvector matrix, and Rusanov flux
independently of the executable expression tree.

The derivative and eigensystem are stated in conservative coordinates
`U = (rho, momentum, totalEnergy)`.  The standard Euler eigenvectors are not
an eigensystem for the derivative of the existing primitive-coordinate helper
`eulerFluxReal`.  A separate conservative flux is therefore differentiated on
`rho != 0`, then proved to agree with the primitive flux after applying the
primitive-to-conservative map.  In the eigenvectors, `H` is the specific total
enthalpy `(E + p) / rho`; it must not be confused with the existing IEEE-side
field called `enthalpy`, whose value represents the density `E + p`.

For `U = (rho, m, E)` and exact `gamma = 7/5`, use the independent
conservative flux

```text
F(U) = (m,
        (4/5) * m^2/rho + (2/5) * E,
        (7/5) * E*m/rho - (1/5) * m^3/rho^2)
```

and its explicit Jacobian

```text
J(U) = [ 0,                                      1,                         0
        -(4/5)*m^2/rho^2,                       (8/5)*m/rho,               2/5
        -(7/5)*E*m/rho^2 + (2/5)*m^3/rho^3,     (7/5)*E/rho-(3/5)*m^2/rho^2,
                                                                         (7/5)*m/rho ]
```

At a primitive-derived state, set `u = m/rho`,
`c = sqrt ((7/5) * p/rho)`, and `H = (E+p)/rho`.  The right-eigenvector
columns and characteristic matrix are

```text
R = [ 1,          1,       1
      u-c,        u,       u+c
      H-u*c,      u^2/2,   H+u*c ]

Lambda = diag (u-c, u, u+c).
```

The algebraic core proves `J * R = R * Lambda` from
`c^2 = (2/5) * (H - u^2/2)`.  The determinant identity
`det R = 2*c*(H-u^2/2) = 7*c*p/rho` then gives a complete, strictly ordered
eigenbasis under `rho > 0` and `p > 0`.

Prove:

- accepted primitive states map to conservative states with positive density
  and positive internal energy/pressure;
- the displayed Jacobian is the derivative of the displayed physical flux on
  the admissible domain;
- `A * R = R * Lambda` and `det R != 0`, so the claimed characteristic values
  have a complete real eigenbasis;
- `alpha` bounds every left and right characteristic speed on the guarded
  domain;
- consistency `H(q, q) = F(q)`; and
- a generic exact-real two-cell, three-interface update has exact boundary-flux
  balance, and the concrete rational Sod quarter-step is Euler-admissible.

A generic invariant-domain theorem under a symbolic Rusanov CFL condition is
a separate follow-on result.  Do not infer or claim it from the concrete
quarter-step calculation.

The derivative and matrix certificate may be completed after the executable
kernel theorem, but they are required before the Euler phase is called complete.
They must not block the first generated artifact while independent Mathlib
matrix bookkeeping is underway.

### Pure IEEE64 source model

Freeze the precise operation order as a pure expression over Talos
`Wasm.IEEE64` operations.  Prove for every input word tuple:

- rejection is exact and performs no floating-point operation;
- guard acceptance implies input finiteness, the real domain facts, and every
  primitive error theorem's magnitude/headroom premises;
- every intermediate and output word is finite;
- returned words equal the pure modeled computation exactly; and
- decoded mass, momentum, and energy fluxes satisfy explicit componentwise
  absolute-error bounds relative to the independent real Rusanov flux at the
  exact dyadic input values.

Error constants are derived from the checked operation graph and retained only
after Lean proves them.  They are not selected by runtime tolerances or by
comparison with native `Float` output.

### Generated WAT

For the actual compiler-generated WAT, prove a total specification quantifying
over every input word tuple, host environment, and admissible initial store:

- fuel-independent termination;
- preservation of the complete store for the scalar kernel;
- exact result-stack/ABI words equal to the pure IEEE64 source model; and
- the same finite-result, signal-bound, and real-error conclusions.

Native Lean floating point and Wasmtime remain regression oracles only.

### Exact binary artifact

Freeze the generated `.wasm` bytes and add the first floating-point entry to the
exact-artifact registry.  The package must prove:

- binary decoding succeeds on those exact bytes;
- validation accepts the decoded module;
- translation produces the Talos module used by the behavior theorem; and
- execution of that exact translated module satisfies the WAT numerical
  specification.

A changed byte sequence requires regeneration and re-verification.  Registry
membership, hashes, and manifests are identity aids rather than substitutes for
the behavior theorem.

## Early verified interface dataset

Publish `euler-rusanov-interface-v1` immediately after the exact binary is
registered.  This is a deliberately small proof-to-data milestone before the
finite-volume stencil: a host driver invokes the registered scalar WASM once
per frozen row and writes the returned raw words.  The numerical computation
must occur in WASM; the host only iterates, checks artifact identity, and
formats data.

The authoritative CSV schema is:

```text
case,rho_l_bits,u_l_bits,p_l_bits,rho_r_bits,u_r_bits,p_r_bits,status_u64,mass_bits,momentum_bits,energy_bits
```

Every binary64 word is lowercase fixed-width 16-digit hexadecimal without
`0x`, rows have a stable order, and the file uses LF endings.  The frozen cases
cover equal left and right Sod states, both Sod interface orientations, a
moving equal-state consistency check, both admitted guard extremes, and a NaN
rejection.  In particular the Sod right pressure word is
`3fb999999999999a`, interpreted as its exact dyadic value rather than silently
as the rational `1/10`.

An adjacent manifest records the schema version, registry entry and exact WASM
SHA-256, exported function, `gamma = 7/5`, `alpha = 7/4`, round-to-nearest-even
semantics, generator revision, and CSV digest.  A concrete Lean theorem
specializes the universal exact-artifact and numerical theorems to every row.
Thus the returned tuples, termination, store preservation, accepted finiteness,
signal bound, real-error bounds, and exact rejection payload are formal claims.
Host iteration, CSV serialization, decimal rendering, plotting, Wasmtime/native
agreement, hashes as identity plumbing, and C comparisons remain explicitly
regression-only unless separately formalized.

Two C comparisons keep unlike methods separate.  First, a tiny C mirror uses
the same fixed `alpha` and operation order and should agree bit-for-bit under
conservative compiler flags.  Second, a driver pins Lanyon's public 1D C at
commit `a736aa5f8b17efd225c4692404e2442361d06729` and reports its dynamic-speed
Lax flux side by side without requiring equality: that code uses division,
square root, and `fmax`, whereas this kernel uses the globally certified fixed
speed `7/4`.  The comparison must not claim reproduction of Lanyon's displayed
100-cell run, whose `uL = 0.75` lies outside the current `|u| <= 1/2` guard.
The published conservative-state cancellation and one-sided-NaN cases remain
targets for the later dynamic conservative-state solver, not for this guarded
primitive-state kernel.

The completed comparison is generated by
`tools/euler-rusanov-c-compare.js`.  It publishes the eight-row
`data/euler-rusanov-interface-v1/regression/c-comparison-v1.csv` and an
adjacent regression-only manifest.  The fixed-speed mirror is required to
match all eight verified raw tuples bit-for-bit.  The pinned Lanyon adapter is
called only on the seven accepted rows, receives the exact dyadic conservative
words, and reports both independently rounded reconstructions.  Its C
expression `7.0 / 5.0` is checked as binary64 word `3ff6666666666666`, which is
an approximation rather than the exact real `7/5` used by the proof.  The
compiler and system `libm` are not proof inputs, so the Lanyon columns are a
supported-host snapshot and no cross-method or cross-host equality is claimed.

## First verified finite-volume data artifact

Instantiate the universal kernel in a small first-order finite-volume program
using the canonical Sod initial states:

```text
domain       [0, 1]
discontinuity 1/2
gamma        7/5
left         (rho, velocity, pressure) = (1, 0, 1)
right        (rho, velocity, pressure) = (1/8, 0, binary64(1/10))
alpha        7/4
dt / dx      1/4
```

The future artifact theorem interprets `binary64(1/10)` as the exact dyadic
encoded by the input word; it never silently replaces that value by the
rational `1/10`.  The exact-real reference stencil deliberately uses rational
`1/10`.  `StencilNumerical` now proves the separate bridge: the encoded value
is exactly `1/10 + 1/180143985094819840`, and that representation bias remains
distinct from the certified floating-point flux errors.

First prove generic two-cell update algebra with three spatial interfaces and
instantiate it for the exact rational Sod pair.  Then propagate the three
certified artifact interface rows through a decoded-real update.  These stages
are complete: the shared-interface error cancels from the balance residual,
and each quarter-step cell is within half of the applicable scalar-flux budget
of the decoded-input exact stencil.  This assembly still occurs in Lean's
mathematical reals and is not described as executed stencil arithmetic.  Only
after this explicit boundary, compile a fixed-grid stencil whose WASM output is a
flat sequence of raw binary64 words containing the initial conservative
states, interface fluxes, updated states, status, and balance diagnostics.
Required results for that compiled artifact are:

- exact execution equals one application of the specified checked recurrence;
- every emitted word required to denote a number is finite;
- each updated cell has positive density and pressure/internal energy;
- the decoded update is compared with the exact reference and has an explicit
  admissibility argument at the selected fixed input; and
- the floating mass, momentum, and energy balance residuals have explicit
  bounds rather than an unjustified claim of bit-exact conservation.

A small host program may decode the words and produce CSV and a static plot.
That formatting is presentation outside the verified numerical boundary.

### Selected direct-artifact shape

The first compiled step is a separate fixed case,
`LeanExe.Examples.EulerRusanovStep`, with a no-argument export
`sodQuarterStepCheckedBits`.  It returns seven `i64` slots: status followed by
the six updated conservative-state words.  It calls the checked scalar
Rusanov kernel three times for `(L,L)`, `(L,R)`, and `(R,R)`, rejects if any
status is nonzero, and otherwise applies this exact binary64 operation graph
to each component:

```text
difference = round(fluxRight - fluxLeft)
scaled     = round((1/4) * difference)
updated    = round(state - scaled)
```

The association is part of the specification and must not be changed by
scaling the two fluxes independently or reassociating the update.  The
expected successful words are:

```text
status 0000000000000000
left   3fe9e00000000000 3fbccccccccccccc 4000100000000000
right  3fd4400000000000 3fbcccccccccccce 3fe7c00000000000
```

The artifact may emit rounded residual words only if they are labeled as such.
For this fixed step the natural floating residual calculation rounds all three
components to positive zero, even though the exact decoded-real balance errors
against the dyadic-input stencil are momentum `+epsilon/32` and energy
`-epsilon/16`.  The publishable conservation certificate is therefore the
Lean theorem over decoded reals, never the zero residual bits alone.

Compiler lowering already supports repeated direct calls, multi-result calls,
and seven result slots.  The medium-risk proof task is to expose the existing
call-free Rusanov execution theorem in a module/function-index-parametric form
so both the current scalar artifact and the embedded helper can instantiate
it without duplicating the 335-instruction proof.

## Follow-on full shock-tube generator

Only after the fixed-kernel and exact-byte milestones pass:

1. expose binary64 subtraction, division, and square root through the restricted
   source profile, IR, emitters, binary verifier, Talos translation, regression
   tests, and primitive WAT proofs;
2. implement checked conservative-state pressure, sound speed, and dynamic
   Rusanov-speed calculations;
3. reject every nonfinite input or intermediate, nonpositive density or
   internal energy, invalid square-root radicand, and failed CFL check;
4. make the published cancellation and one-sided-NaN examples explicit
   rejection regressions;
5. implement a first-order double-buffered array step with no reconstruction;
6. prove a successful step equals the pure IEEE recurrence and leaves every
   emitted cell finite and physically admissible;
7. prove the corresponding exact WAT and exact-byte artifact specifications;
8. iterate the checked step on the 100-cell Sod problem to time `0.2`; and
9. emit density, momentum, energy, velocity, pressure, CFL, minimum density and
   pressure, and boundary-flux balance data.

The generic runner theorem states that successful execution equals repeated
application of the checked IEEE step and that every accepted intermediate grid
satisfies the checked invariant.  The fixed 100-cell run instantiates that
theorem and is evaluated separately; the proof must not unroll thousands of
instructions into a benchmark-specific manual trace.

Independent exact-Riemann output and grid-refinement measurements are regression
and scientific-validation evidence.  They are not initially formal convergence
theorems.

## Ordered checkpoints

Every checked row ends in a passing commit, an update to this plan and
`devnotes.md`, and a push to `origin/talosfp-euler`.

- [x] Complete the phase-7 guarded quadratic Horner source, WAT, and numerical
      theorem checkpoint.
- [x] Add the guarded scalar Euler source entry, ABI, extraction/IR/WAT checks,
      and Wasmtime regression cases.
- [x] Prove the raw-bit guard and real characteristic-speed bound.
- [x] Prove the pure IEEE64 finite-result and componentwise real-error contract.
- [x] Prove exact, fuel-independent execution of every accepted and rejected
      path in the current generated WAT.
- [x] Transfer the numerical contract to generated-WAT execution and audit its
      axioms.
- [x] Freeze the generated WAT, register its exact binary artifact, and prove
      decoded/validated/translated module identity.
- [x] Generate and prove the frozen `euler-rusanov-interface-v1` raw-word
      dataset and its regression-only CSV.
- [x] Add pinned, regression-only C comparison tooling without conflating the
      fixed-speed verified kernel with Lanyon's dynamic-speed implementation.
- [x] Prove the independent Jacobian derivative and complete eigendecomposition.
- [x] Add the generic two-cell/three-interface balance theorem and prove the
      concrete rational Sod quarter-step values and admissibility.
- [x] Propagate the three certified interface-flux budgets through the
      decoded-real update and balance theorem, compose them with the exact
      input-representation bias, and prove robust admissibility of both
      assembled quarter-step cells.
- [ ] Add a symbolic CFL/invariant-domain theorem only if a later claim needs
      generic positivity beyond the proved fixed step.
- [ ] Compile and prove the fixed Sod one-step artifact and emit its raw data.
- [ ] Add host CSV/plot presentation and independent numerical comparisons.
- [ ] Extend subtraction, division, square root, classification, and safe
      comparison support as demanded by the checked multi-step solver.
- [ ] Implement and prove the checked first-order 100-cell Sod runner.
- [ ] Reconcile maintained documentation and proof inventories with the final
      implemented scope.

## Verification gates

Every checkpoint follows the repository gates relevant to its files.  In
addition:

- run every Lean command directly on the local host with exactly one global
  Lean/Lake/compiler process at a time; direct Lean is user-authorized through
  this pinned envelope (substitute only the focused `TARGET`):

  ```sh
  env LEANRUN_LOCAL=1 \
    LEAN_SYSROOT=/root/.elan/toolchains/leanprover--lean4---v4.34.0-rc2 \
    LD_PRELOAD=/tmp/leanexe-proc-self-readlink.so \
    LEAN_NUM_THREADS=1 \
    WASM_TOOLS=/workspace/scratch/9df984ece5a1/leanexe/build/tools/wasm-tools-1.251.0-x86_64-linux/wasm-tools \
    tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build TARGET
  ```

  The wrapper preserves the shared lock and priority controls while warning
  that unavailable systemd cgroup limits are not enforced.  The compatibility
  preload maps numeric `/proc/<pid>/exe` reads to `/proc/self/exe`; never pass
  it to unrelated process inspection.  The prior read-only `ps` failure from
  doing so is recorded in `journal.md` and is not to be repeated;
- never invoke, probe, or assume the existence of `tools/leanrun-dev`, a
  `dev` host, or any other remote executor; GitHub is only the publication and
  recovery remote for this work;
- after a timeout without a theorem diagnostic, do not repeat the same target
  against unchanged dependencies: identify a smaller missing dependency,
  build that boundary under its own timeout, and retry the parent only after
  the proof state or cache has materially changed;
- treat the entire active checkout—including `.git`, tracked and untracked
  sources, generated and ignored files, submodules, dependencies, build
  products, caches, evidence receipts, and partial work—as user-owned
  persistent project state, never as a disposable workspace or a maintenance
  target; no generic “workspace maintenance”, repair, reclamation, or
  reproducibility rationale authorizes cleanup, truncation, movement,
  invalidation, pruning, deletion, `git clean`, destructive reset,
  checkout-overwrite, stash, or an equivalent worktree rewrite; any deletion
  or destructive operation requires fresh user authorization for the exact
  named target;
- inspect `git status` before every mutation, preserve unrelated and
  pre-existing changes, and stage only explicitly reviewed paths; commit each
  coherent checkpoint and push it promptly;
- because ordinary HTTPS write authentication is unavailable in this
  environment, publish through the GitHub Git-data API without altering the
  worktree: create exact blobs, create a tree based on the current remote
  parent, require that API tree to equal the staged local tree, create a commit
  with that exact remote parent, update `refs/heads/talosfp-euler` with
  `force: false`, fetch the published commit, and require full fetched-tree,
  local-index, and worktree equality before advancing the local ref;
- record commands, elapsed boundaries, proof failures, timeouts, warnings,
  axiom audits, commit identities, and publication verification in
  `journal.md`, retain a concise durable checkpoint in `devnotes.md`, and
  commit and push both when changed; a timeout is never recorded as a theorem
  failure or pass;
- reject new `sorry`, `admit`, and axiom declarations in changed Lean files;
- require public numerical and execution theorems to report only the project's
  accepted standard logical axioms;
- inspect the emitted WAT and exact binary opcode sequence rather than relying
  only on numerical examples;
- test rejection paths and guard boundaries, including signed zero and adjacent
  encodings where material;
- preserve all pre-existing integer and floating-point proof cases; and
- do not invoke the experimental self-hosted emitter as part of this work.

Hash, manifest, release-receipt, and self-host bookkeeping are not implementation
gates for this branch.  Exact embedded bytes remain semantic proof input where
an exact-artifact theorem is claimed.

## Feasibility and controlled scope

The guarded scalar kernel, real-domain proofs, generated-WAT theorem, first f64
exact-byte package, and fixed one-step data are expected to be tractable with
the existing infrastructure.  The straight-line kernel is simpler at the WAT
level than the completed runtime-length dot loop.  The main new work is its
domain/error algebra and exercising the exact-byte FP path.

The full checked grid step is a larger but compatible extension.  Its main cost
is proof structure for two array buffers, boundary conditions, nested loops,
and state-dependent guards rather than a missing semantic foundation.

The following are explicit non-goals of this phase:

- proving that a finite-grid output is the exact Euler entropy solution;
- a global floating-point forward-error or convergence theorem for the full
  shock-tube run;
- entropy stability, high-order accuracy, Roe or HLLC fluxes;
- componentwise minmod or another unproved reconstruction;
- two- or three-dimensional solvers;
- general Lean `Float` compilation or a complete WebAssembly FP profile; and
- claiming general verified compilation without the separate source-theorem
  transport chain.
