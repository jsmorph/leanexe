# Verified Euler Rusanov Data

**Status:** Active on branch `talosfp-euler`.  This document expands phase 8
of the root [Development Plan](../plan.md).

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

The current floating-point cases are source-driven generated-WAT proof cases.
No f64 case is yet registered in `proofs/artifacts/registry.json`.  The first
Euler artifact must therefore exercise the complete exact-byte path rather than
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

For a fixed dissipation speed `alpha = 7/4`, compute the numerical flux directly:

```text
H(qL, qR) = (1/2) * (F(qL) + F(qR) + alpha * (U(qL) - U(qR))).
```

The first implementation uses only the admitted f64 addition and multiplication
operations.  Binary64 negation is exact sign-bit toggling, and subtraction is
addition of the negated word.  The constants `1/2`, `5/2`, `7/2`, and `7/4`
are exactly representable binary64 values.

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
independently of the executable expression tree.  Prove:

- accepted primitive states map to conservative states with positive density
  and positive internal energy/pressure;
- the displayed Jacobian is the derivative of the displayed physical flux on
  the admissible domain;
- `A * R = R * Lambda` and `det R != 0`, so the claimed characteristic values
  have a complete real eigenbasis;
- `alpha` bounds every left and right characteristic speed on the guarded
  domain;
- consistency `H(q, q) = F(q)`; and
- the exact-real one-step finite-volume update preserves the Euler admissible
  set under the stated Rusanov CFL condition.

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

## First verified data artifact

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

The theorem interprets `binary64(1/10)` as the exact dyadic encoded by the
input word; it never silently replaces that value by the rational `1/10`.

First prove a generic three-cell stencil and instantiate it for a compact fixed
grid.  The WASM output is a flat sequence of raw binary64 words containing the
initial conservative states, interface fluxes, updated states, status, and
balance diagnostics.  Required results are:

- exact execution equals one application of the specified checked recurrence;
- every emitted word required to denote a number is finite;
- each updated cell has positive density and pressure/internal energy;
- the real update meets the Rusanov positivity theorem; and
- the floating mass, momentum, and energy balance residuals have explicit
  bounds rather than an unjustified claim of bit-exact conservation.

A small host program may decode the words and produce CSV and a static plot.
That formatting is presentation outside the verified numerical boundary.

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

- [ ] Complete the phase-7 guarded quadratic Horner source, WAT, and numerical
      theorem checkpoint.
- [ ] Add the guarded scalar Euler source entry, ABI, extraction/IR/WAT checks,
      and Wasmtime regression cases.
- [ ] Prove the raw-bit guard and real characteristic-speed bound.
- [ ] Prove the pure IEEE64 finite-result and componentwise real-error contract.
- [ ] Freeze the generated WAT and prove exact, fuel-independent execution of
      every accepted and rejected path.
- [ ] Transfer the numerical contract to generated-WAT execution and audit its
      axioms.
- [ ] Register and prove the exact binary artifact.
- [ ] Prove the independent Jacobian derivative and complete eigendecomposition.
- [ ] Add the generic one-step stencil and its exact-real positivity theorem.
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

- run every Lean command serially through `tools/leanrun` with an explicit
  timeout;
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

