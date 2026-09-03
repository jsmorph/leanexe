# Proof-Grade Floating-Point Artifact Semantics

**Status:** Active on branch `talosfp`.  This document expands phase 7 of the
root [Development Plan](../plan.md).

## Decision and current foundation

LeanExe will consume Talos's proof-visible IEEE-754 support through its existing
Lake dependency and exact-artifact proof boundary.  It will not copy the
floating-point model, make native `Float` part of the trusted result, or require
general Lean `Float` source support.

The branch starts from `selfhost` revision
`bc0f619c83d3a10e34fefce219ad17483a4cd6fe`.  That base retains the canonical
module-image experiment, but floating-point development uses the native
compiler and independent exact-artifact boundary.  The self-hosted emitter is
optional regression evidence and does not block this phase.

The validated Talos floating-point foundation is fork revision
`87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`.  It provides pure bit-pattern
IEEE32 and IEEE64 execution, finite real-value interpretations, shared integer
rounding, f64 addition, subtraction, multiplication, division, and square-root
error theorems, reusable perturbation and relative-error composition, fixed
Horner and dot kernels, and a runtime-length generated f64 dot-product proof.
The arithmetic foundation, shared rounding proof, and representative numerical
kernels therefore belong to Talos and are prerequisites rather than LeanExe
implementation milestones.

LeanExe's missing layer is exact artifact closure and compiler access: its
independent binary syntax currently admits integer values and instructions, and
its source IR and structured emitter currently expose integer operations only.

## Ownership and trust boundary

| Layer | Owner | Checked responsibility |
|-------|-------|------------------------|
| IEEE execution and numerical algebra | Talos | Pure bit-level operations, finite real interpretation, primitive error theorems, composition, and kernel bounds. |
| Restricted source profile | LeanExe compiler | Recognize named bit-pattern intrinsics and reject unsupported floating-point source forms. |
| Structured lowering | LeanExe compiler | Emit an exact reinterpret/arithmetic/reinterpret instruction sequence while preserving the integer public ABI. |
| Exact binary boundary | LeanExe artifact verifier | Decode embedded bytes, prove grammar agreement, validate, translate into Talos, and reject malformed or out-of-profile modules. |
| Artifact behavior | LeanExe proof package | Prove fuel-independent execution of the exact translated module and preserve its complete store contract. |
| Numerical refinement | Talos plus artifact specification | State explicit finite, magnitude, headroom, normality, and denominator assumptions and derive the advertised real bound. |
| Annotations and certificates | Untrusted producer, checked consumer | Suggest regions, guards, and numerical facts whose exact statements Lean verifies against frozen bytes and sound lemmas. |

The Lean kernel checks every accepted theorem.  LeanExe, the self-hosted emitter,
the annotation and certificate generators, Codex, native `Float`, Wasmtime, and
the source program remain untrusted producers or regression oracles.  Exact
artifact theorems continue not to assume compiler correctness.

## Toolchain and dependency migration

The compiler root, proof workspace, generated proof packages, and active tool
checks will pin:

```text
leanprover/lean4:v4.34.0-rc2
```

The migration will be divided so failures remain attributable:

1. Move the native LeanExe compiler from Lean 4.31.0 to exact 4.34.0-rc2 without
   changing the Talos proof dependency.  Recheck extraction, IR, ownership,
   native emission, and every registered byte identity.  A self-host run may be
   recorded but is not an acceptance gate.
2. Move the proof workspace to Talos revision
   `fda69ca67a81ea4f1fa4e376bdc5861d9fe5479a`, the closest useful pre-FP 4.34
   baseline, and make all existing source-driven and exact-artifact proofs pass.
3. Advance only the immutable Talos pin to
   `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47` and repeat the complete integer
   proof and conformance gates before LeanExe emits any floating-point opcode.

Active manifests, conformance configuration, release identity, kernel review,
and warm receipts must follow the new pins.  Historical demo, benchmark, and
bootstrap records retain their original 4.31 pins and results as provenance.
The working dependency may use a local path during development, but every
pushed checkpoint uses an immutable Git revision.  A canonical upstream Talos
revision may replace the fork pin only after it contains the identical tree.

## Bit-pattern ABI and restricted source profile

The first profile exposes compiler-recognized operations over raw words, for
example:

```lean
LeanExe.Float64.addBits : UInt64 -> UInt64 -> UInt64
LeanExe.Float64.mulBits : UInt64 -> UInt64 -> UInt64
```

The public values remain `UInt64`; reinterpretation happens inside the emitted
artifact.  A multiplication has the semantic instruction shape:

```wat
local.get 0
f64.reinterpret_i64
local.get 1
f64.reinterpret_i64
f64.mul
i64.reinterpret_f64
```

The compiler may provide executable native definitions for source comparison,
but artifact and numerical theorems depend only on the emitted bytes and Talos's
pure operations.  The extractor accepts only the documented intrinsic names and
exact signatures.  General `Float`, implicit coercions, f32/f64 promotion and
demotion, and native floating evaluation remain outside the initial language.

The first implementation can keep each intrinsic result represented as an i64
word in IR and locals.  Nested arithmetic may consequently contain adjacent
reinterpretations.  Their exact presence is part of the frozen artifact until a
separately reviewed typed-float IR optimization proves and tests a byte change.

## Minimal exact-binary profile

The first artifact increment admits an internal f64 validation-stack type and
only these arithmetic instructions:

| Instruction | Opcode |
|-------------|--------|
| `f64.add` | `0xa0` |
| `f64.mul` | `0xa2` |
| `i64.reinterpret_f64` | `0xbd` |
| `f64.reinterpret_i64` | `0xbf` |

Function parameters, results, storage, and public locals remain i64.  This
avoids f64 constants, parameters, results, locals, loads, and stores in the
first closure.  The new cases must cross binary syntax, grammar, executable
decoding, decoder soundness, executable validation, declarative validity,
validator soundness, Talos translation, structural equality, fixtures, and
mutation tests.  Talos's WAT decoder is an auxiliary source-driven check and
does not replace this independent `.wasm` byte boundary.

The experimental self-hosted emitter's module-image schema v2 remains frozen.
The production `moduleBytes` route uses the direct native serializer, so the
initial floating-point profile is native-only: `compile-image` does not need to
encode the new instructions, and extending that experimental wire format is a
separate follow-on decision.  Before the shared instruction datatype grows, the
frozen v2 image implementation must be decoupled from it or convert unsupported
instructions to an explicit `compile-image` error; it must never silently emit an
empty or corrupt artifact.  Existing registered program bytes remain unchanged.

## First accepted kernel

The plumbing artifact is a raw two-operand multiplication.  It proves that
embedded bytes decode, validate, and translate; execution terminates
independently of fuel; the complete store frame is preserved; and the returned
i64 word equals `Wasm.IEEE64.mul` on the two input words.  A corollary supplies
finiteness and the Talos real-error bound under explicit finite and magnitude
hypotheses.

The first numerically meaningful artifact is a guarded two-term dot product:

```lean
dot2CheckedBits a0 b0 a1 b1
```

For each operand the generated program checks the raw-bit predicate

```text
(bits & 0x7fff_ffff_ffff_ffff) <= 0x3fe0_0000_0000_0000
```

which denotes a finite binary64 value with absolute value at most one half.
The accepted branch evaluates two multiplications and one addition.  The public
result uses two i64 words: tag zero and the result bits on success, tag one and
payload zero on domain rejection.

The exact artifact theorem proves both branches terminate.  Rejection reaches
no floating-point operation.  Success returns exactly the Talos modeled dot
result, preserves the required store and memory frame, produces a finite word,
and proves

```text
|value(result) - (value(a0) * value(b0) + value(a1) * value(b1))|
  <= 3 * 2^-52.
```

The finite half-domain excludes overflow, infinity, and NaN at every arithmetic
event.  The theorem is therefore independent of WebAssembly's permitted choice
of NaN payload.  A complete allowed-NaN relation remains a later scalar-profile
task rather than a prerequisite for finite numerical kernels.

The first certificate is deliberately fixed and small: it records the half
guard, the two multiplication edges, the addition edge, and the claimed error
budget.  Lean checks the guard-to-range bridge and instantiates Talos's existing
dot theorem.  A general interval language begins only after this fixed exact
artifact passes.

## Runtime-length and follow-on kernels

After the fixed kernel, LeanExe will compile a runtime-length dot product over
its existing `Array UInt64` representation.  The artifact specification fixes
the vector layout and defines the empty dot product as positive zero.  The
artifact proof must establish LeanExe's emitted allocation, array-header, loop,
load, and result behavior; the hand-written Talos `F64Dot` proof is a structural
reference, not a substitute for the generated artifact proof.

The numerical conclusion reuses Talos's list-shaped dot theorem.  Its public
hypotheses state finite and bounded inputs, aggregate exact headroom, normal or
zero exact products where the relative model requires it, and
`(2*n - 1) * 2^-53 < 1`.  It proves a finite result and

```text
|computed - exact| <= gamma (2*n - 1) 2^-53 * sum |x_i * y_i|.
```

For a nonzero exact result, a corollary states the corresponding condition-number
relative bound.  A guarded affine or Horner artifact then exercises sequential
composition.  Division, square root, f32 arithmetic, comparisons, conversions,
and broader certificate automation enter only after these representative f64
kernels pass.

## Ordered checkpoints

Each checked row is a separately committed and pushed passing state.  The plan
and `devnotes.md` record exact commands, tool pins, axiom reports, artifact
digests, and any deliberate byte changes.

- [x] Migrate the native compiler to exact Lean 4.34.0-rc2 and preserve every
      registered artifact byte.  The scoped legacy `do` option on the frozen GCD
      fixture compensates for the 4.34 elaborator default change.
- [ ] Move the proof workspace to pre-FP Talos `fda69ca67a81ea4f1fa4e376bdc5861d9fe5479a`;
      repair compatibility and pass every existing integer source and
      exact-artifact gate.
- [ ] Advance the immutable Talos dependency to FP revision `87e3aa5`; repeat
      all existing integer proof, conformance, and identity gates.
- [ ] Add the internal f64 binary syntax, decoder, grammar, and decoder proofs
      for add, multiply, and the reinterpret pair.
- [ ] Add executable validation, declarative validity, translation, equality,
      successful fixtures, and boundary/mutation rejection tests.
- [ ] Add `addBits` and `mulBits` source intrinsics, IR operations, structured
      emission, binary and WAT encoding, reports, annotations, and focused
      compiler tests.
- [ ] Freeze and prove the scalar multiplication artifact, including exact
      execution, store preservation, finite-domain error, and axiom audit.
- [ ] Freeze and prove `dot2CheckedBits`, including its rejected path, guard
      bridge, finite result, `3 * 2^-52` error theorem, corrupt-certificate
      tests, and independent package verification.
- [ ] Compile and prove a runtime-length dot artifact with absolute,
      gamma-times-mass, and conditioned relative-error contracts.
- [ ] Compile and prove a representative affine or Horner artifact and extract
      reusable floating ProofKit, annotation, and LTG support from both kernels.
- [ ] Extend the exact profile and compiler intrinsics to subtraction, division,
      square root, and representative f32 operations as demanded by accepted
      kernels.
- [ ] Refresh maintained language, compiler, ABI, artifact, numerical, status,
      and trust-boundary documentation; refresh active release evidence and
      verify the pushed branch tree.

## Verification gates

Every source checkpoint runs `git diff --check`, rejects new `sorry`, `admit`,
and axiom declarations in changed Lean files, and records `git status --short`.
Every public theorem receives a `#print axioms` check whose result contains only
standard Lean logical axioms already admitted by the project.

Compiler changes require focused builds, extraction/report/IR/ownership checks,
the complete execution suite, WAT round trips, registered-corpus equality, and
all affected Talos proofs.  The experimental self-host checks are required only
when its image boundary is deliberately changed.  Exact-artifact changes additionally
require focused decoder and validator targets, mutation tests, all source-driven
proofs, all exact-artifact packages, and semantic conformance.

All Lean and Lake processes use the repository runner serially with explicit
timeouts.  A timed-out unchanged target is divided before retry.  A checkpoint
is pushed only after its required gates pass; after each push, a fetch must show
that the remote commit and tree equal the validated local `HEAD` and tree.

## Completion and nonclaims

This phase completes only when exact Lean 4.34.0-rc2 builds the compiler and
proof workspace, every prior integer gate still passes,
the scalar and representative multi-operation artifacts have exact byte proofs,
the fixed and runtime-length numerical theorems pass their axiom audits, active
release evidence names the new immutable dependencies, maintained documentation
describes the implemented subset, and the remote `talosfp` tree equals the
validated local tree.

Completion does not claim support for arbitrary Lean `Float`, the entire
WebAssembly floating-point instruction set, every permitted NaN result, compiler
correctness, a verified certificate generator, transcendental functions, SIMD,
or proof-grade f32/f64 promotion and demotion.
