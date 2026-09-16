# Real Lean proof exports: M0.11–M1.1

`identity.ndjson` is the unchanged output of pinned lean4export on the minimal
`prelude` module `LeanExe/KernelCheck/Fixtures/Identity.lean`. It declares
`implicationIdentity : ∀ p : Prop, p → p`. `provenance.json` records source and
fixture SHA-256 hashes, exporter revision, Lean version and commit.

The original export has 17 records: metadata, names and expressions, and one
theorem. It has no constants, universe parameters, axioms, or other declarations.
The adapter checks these restrictions over the entire input; no dependency is
skipped. `identity.decoded.json` fixes the exact graph and both roots.

`identity-corrupt.ndjson` changes only the inner lambda body's expression ID
from 1 (the proof hypothesis) to 2 (the outer proposition). It remains
well-scoped and structurally valid but has the wrong type. The same adapter
and WASM checker reject it; there is no host-side expected-verdict shortcut.

## Build and run the checker

Follow the toolchain and authorized execution setup in `AGENTS.md` and
`DEVELOPING.md`. From the repository root:

```sh
node test/kernel_export.js
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m0-11.wasm test/fixtures/kernel-check/identity.ndjson
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m0-11.wasm test/fixtures/kernel-check/identity-corrupt.ndjson
```

The first runtime command prints an `accepted` report and exits 0; the second
prints `rejected` and exits 1. Other checker outcomes or adapter failures exit
2. Optional final argument: a decimal UInt64 fuel budget. Fuel 1 produces
`exhausted`, not `rejected`. A runtime trap is an execution failure, never an
accepted or rejected proof.

After preparation these runtime commands require only Node, the adapter, the
WASM file and the repository's Wasmtime C host/runtime. No Lean, lean4export,
or Tenet process is called. The WASM has no imports. The first fixture artifact
is 2,429,809 bytes, SHA-256
`aa1353e70bdbf4a101efe57beb1220ca603820d19c0c7a767638a0bc1645350d`.
This records measured bytes; it is not a formal artifact theorem.

## Reproduce the original export

Preparation uses [lean4export at the pinned revision](https://github.com/leanprover/lean4export/tree/483e011449cce37c3f8ad5e2aae434cbb1d2e53c)
and its [NDJSON 3.1.0 format](https://github.com/leanprover/lean4export/blob/483e011449cce37c3f8ad5e2aae434cbb1d2e53c/format_ndjson.md).
The exporter toolchain matches LeanExe's Lean 4.34.0-rc2 exactly.

```sh
git clone https://github.com/leanprover/lean4export.git build/tools/lean4export
git -C build/tools/lean4export switch --detach 483e011449cce37c3f8ad5e2aae434cbb1d2e53c
tools/leanrun --timeout 180s lake -d build/tools/lean4export build
node tools/kernel-export-fixture.js
```

Skip cloning if this checkout already exists. The last command checks the
clean exporter revision, builds the fixture, reruns the exporter through the
guarded Lake environment, and requires byte-for-byte equality with the frozen
export. It does not overwrite the committed fixture.

## Adapter scope and trust boundary

The narrow adapter supports names, concrete zero/successor levels, and Sort,
bvar, Pi, lambda, application and let expressions. Table IDs and bvars must be exactly represented
JavaScript safe integers; larger values are rejected rather than rounded.
Successor levels are decoded with BigInt and checked against UInt64 capacity.
It validates metadata versions, record fields, sequential IDs and references.
Binder names/info are validated then omitted from the kernel graph because
they do not affect these typing judgments. The raw export remains available.

Other expression/declaration/level forms, including constants and symbolic
universes, are explicitly rejected at this adapter boundary. No inference, normalization,
axiom insertion, or acceptance decision occurs in the adapter.

Adapter fidelity and overall checker soundness remain operational assumptions,
not proved results. Current universal source proofs cover only the scalar sort
and concrete universe primitives. Larger source proofs are deferred and no
WASM proof work is being attempted in this PoC.


## M1.0: implication composition

`composition.ndjson` is the unchanged pinned export of
`implicationComposition : (p q r : Prop) → (q → r) → (p → q) → p → r`.
Its body `fun p q r f g hp => f (g hp)` contains two nested applications,
with no globals, universe parameters or axioms. The source is
`LeanExe/KernelCheck/Fixtures/Composition.lean`; the hashes and pins are in
`composition-provenance.json`, and the exact graph is in
`composition.decoded.json`.

`composition-corrupt.ndjson` changes only application node 14's argument
from expression 13 (bvar 0, `hp`) to expression 12 (bvar 2, `f`). This gives
`g f`, a well-scoped application with an incorrect argument type. Both raw
files pass through the same adapter and checker.

```sh
node test/kernel_export.js composition
node tools/kernel-export-fixture.js composition
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m1-0.wasm test/fixtures/kernel-check/composition.ndjson
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m1-0.wasm test/fixtures/kernel-check/composition-corrupt.ndjson
```

The runtime commands report accepted/exit 0 and rejected/exit 1. The first
command checks both native/WASM verdicts, scope, exhaustion, exact decoding,
provenance hashes and nineteen malformed/unsupported adapter inputs. The
second reproduces the frozen raw export. The checker artifact has exactly
the M0.11 size and SHA-256 above: this milestone extends the adapter, while
using the existing application inference implementation. The same runtime
requirements and unproved soundness boundaries apply.


## M1.1: an unused let with a checked value

`let.ndjson` preserves a real letE record for
`fun p hp => let unused : p := hp; hp`. The source is
`LeanExe/KernelCheck/Fixtures/Let.lean`, with pins and hashes in
`let-provenance.json`. `let-corrupt.ndjson` changes only the let value from
expression 1 (`hp`) to expression 2 (`p`). The binding is unused, but its value
still must have the annotated type. This corruption is scoped and rejected.

```sh
node test/kernel_export.js let
node tools/kernel-export-fixture.js let
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m1-1.wasm test/fixtures/kernel-check/let.ndjson
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m1-1.wasm test/fixtures/kernel-check/let-corrupt.ndjson
```

The adapter preserves the annotation/body using a synthetic lambda node and
then emits a let node. Consequently export expression 7 maps to graph node 8;
`let.decoded.json` fixes this mapping explicitly. Binder names and the Boolean
nondep optimization flag are validated but omitted; no flag authorizes skipping
value checking. The gate covers twenty-one malformed/unsupported variants,
exhaustion, exact decoding, native/WASM scope/verdict comparisons and no imports.
The kernel code is unchanged. No new formal correctness claim is made.
