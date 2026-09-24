# Certified scalar64 compilation

`correct` adds a proof-carrying compiler path for UInt64 programs. For every
accepted package, Lean proves that the **exact packaged WASM bytes** decode to a
valid module and that its entry function terminates, returns the original Lean
function's result for every input, and preserves the surrounding store.

The command uses the proved scalar backend. Source-to-core and source-to-IR
correspondence are supplied by a checked `Certificate`; an untrusted generator
can produce these proofs. The five included certificates name the original Lean
declarations. The ordinary `leanexe` compiler is outside this guarantee.

## Run

Install the repository's pinned Lean toolchain and fetch the dependencies in
`proofs/talos/lean`. These commands use `tools/leanrun` and its normal limits:

```sh
tools/compile-certified --profile scalar64 affine --output tmp/certified/affine
tools/verify-certified tmp/certified/affine
tools/check-correct --packages tmp/certified --mutations --cold
```

The other pilot names are `choose`, `mix`, `helper`, and `gcd`. The gate creates
missing packages, verifies all five, runs engine smoke tests and dependency
audits, rejects modified packages, and verifies all five again from a clean
checkout. `--verify-only` prevents the gate from running compilation. Output
paths must be new; compilation publishes a package only after verification.

Where direct local execution has been explicitly authorized, set
`LEANRUN_LOCAL=1`; `LEANRUN_TOOLCHAIN` may select the directory containing the
pinned toolchain. The runner keeps the shared lock and timeout. It does not
silently enable local mode. A failed proof or exceeded timeout is a failed gate.

## Scope

The formal backend supports any fixed scalar function signature with UInt64
arguments and a UInt64 result. The package CLI currently limits signatures to
32 arguments and bounded package sizes. Booleans are internal branch conditions.
There is no heap, memory, mutable global, import, allocator, closure, or host effect.

Supported operations include modular add/subtract/multiply, unsigned comparisons,
bitwise operations, shifts, strict bindings, branches, acyclic direct helper
calls, and structured loops with termination evidence. Division by zero produces
zero; remainder by zero produces the dividend. The lowerer guards these cases.
Shift counts are reduced modulo 64. `Nat` is allowed in proof measures, not as a
runtime argument or result. Unsupported profiles or missing certificates fail.

UInt64 values map to WASM i64 bit patterns in source argument order. Talos's
internal operand stack represents arguments in reverse order; the theorem states
that convention explicitly. JavaScript returns i64 as a signed BigInt, so use
`BigInt.asUintN(64, result)` to view the source UInt64 value.

## What is proved

| Layer | Checked statement |
|---|---|
| Admission | Independent scalar grammar plus ordinary typing, with a sound and complete checker. |
| Source | Actual Lean declaration computes the independent scalar core result for every input. |
| IR | Each certificate proves total execution of its scalar IR, including source result equality. |
| Backend | Structural expression/command proofs transfer IR execution through locals, scratch space, branches, calls, and loops to Talos WASM execution. |
| Module | Checked signatures, local bounds, scratch capacity, acyclic calls, and scalar-only assembly. |
| Bytes | Formal decoding, independent WASM validity, and equality of the entire decoded module to the module produced by proved lowering. |
| Composition | `Artifact.valid_and_correct` combines these facts with universal source correspondence and store-preserving termination. |

Loops use invariants and decreasing measures stated in IR semantics. The GCD
source proof separately unfolds the original Lean `while` implementation and
relates it to well-founded Euclidean iteration. No pilot contains an instruction-
by-instruction WASM correctness proof.

The source core and IR are two independently specified execution models. Their
certificate proofs meet at the **original source result**, rather than treating
an evaluator embedded in the compiler as the language specification. Certificate
construction is per translation; the backend proof is shared.

## Portable package and independent verification

A package contains `program.wasm`, `translation.json`, `decoded.json`, the source
snapshot, canonical `Check.lean`, and `manifest.json`. It records the original
source and certificate declarations, core and IR, signatures, entry/export, ABI,
file hashes, theorem names, repository revision, Lean pin, and dependency pins.

The verifier checks pins and source identity, reads strict data schemas, and
reconstructs the canonical checking module. It does **not** execute package-
supplied Lean text. The supplied `Check.lean` must match the reconstruction.
It checks the certificate's dependent type against the named source declaration,
checks core/IR/ABI/export equalities, and proves exact byte closure using the
independent decoder and validator. It never invokes the encoder, package emitter,
or source/IR certificate generator. Axiom audits cover the final theorem and
binding equalities. Hashes identify files; the Lean proofs establish semantics.

Verify against the recorded repository revision with its pinned dependencies.
Later documentation-only changes are allowed; changed proof or compiler sources,
source snapshots, dependency revisions, ABI, or theorem names are rejected.
The cold gate creates a detached checkout at the package revision, shares only
pinned **external** dependency caches, and rebuilds project/source proofs from
scratch. It uses no project oleans or generator from the producing checkout.
Packages are portable proof-carrying data, not self-contained Lean installations.

## Add a source program

Provide a tracked Lean declaration and a tracked module defining
`Project.Correct.Scalar64.Certificate Input args source`. Use `Unit` for zero
arguments, `UInt64` for one, and a right-nested product for multiple arguments.
The argument mapping lists projections in source order. Reuse the compositional
source rules and `Executes` constructors to prove source/core and IR execution.
A loop requires an invariant and termination measure. Then invoke:

```sh
tools/compile-certified --profile scalar64 \
  --source-module LeanExe.Examples.MyProgram \
  --source LeanExe.Examples.MyProgram.run --arity 2 \
  --certificate-module Project.MyProgramCertificate \
  --certificate Project.MyProgramCertificate.cert \
  --output tmp/my-certified-program
```

Commit the declaration and certificate before packaging so the revision identifies
them. This version selects checked pilot certificates or an explicit custom
certificate. It does not automatically discover invariants or prove arbitrary
Lean source correspondence. Failed or absent proofs cannot fall back to the
ordinary compiler.

## Trust and limits

The claim relies on Lean's kernel and the reviewed definitions: the independent
source semantics, scalar IR semantics, binary grammar/validator, and pinned Talos
WASM model. Actual engines must implement those WASM semantics. Engine tests are
additional compatibility checks, not the universal proof. The theorem is about
execution in that model, not operating-system resource limits or engine bugs.

The independent TypeSafety/admission proofs retain their `propext`-only policy.
The loop bridge and Talos proofs allow only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`; Lean's own `repeatM` already uses choice.
No new axioms, `sorryAx`, native evaluation certificates, or compiler-trust proof
shortcuts are accepted. Dependencies and normal toolchain/cache integrity remain
part of the trusted build environment. The cold gate removes dependence on
producer project caches.

The concrete acceptance corpus is affine arithmetic, branching, Prng.mix,
helper calls, and the unchanged TalosGcd.gcd. Wider words, signed instructions,
heap objects, arbitrary recursive calls, and the full Lean language are future
extensions requiring additional statements and proofs.
