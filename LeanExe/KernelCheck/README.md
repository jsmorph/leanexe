# Lean kernel checker: executable checkpoints

Executable coverage reaches M1.0, including real identity and composition proof exports. Formal source proofs currently cover only
sort typing and concrete max/imax (P0/P1); binding, checker soundness and
exact-WASM correctness remain unproved. See the [proof coverage ledger](PROOFS.md)
and run `node test/kernel_proofs.js` to check the ten universal theorems.

Run the complete focused suite with `node test/kernel_all.js`. For the real
export demo, run `node test/kernel_export.js`, then use the runtime command
in the M0.11 section below.

## M0.0: concrete sort typing

This is the first executable checkpoint toward a full Lean kernel checker
implemented in LeanExe. It checks one rule for concrete universe levels:

    Sort u : Sort (u + 1)

`Sort.lean` defines `LeanExe.KernelCheck.checkSort`. Its two `UInt64`
arguments encode the universe level and its claimed type's universe level.

| Returned word | Meaning |
|---|---|
| 0 | The claimed type is the successor sort. |
| 1 | The claimed type is incorrect. |
| 2 | The successor exceeds this initial UInt64 representation. |

The function checks the representation boundary before addition. It never
accepts a wrapped successor. These words are function results, not shell
exit statuses. This checkpoint does not parse declarations, check proofs,
or implement symbolic universe parameters.

### Build and check

Use the repository's pinned tools and execution rules from `AGENTS.md` and
`DEVELOPING.md`. Install Wasmtime with `tools/download-wasmtime.sh`, then:

```sh
node test/kernel_sort.js
```

The focused driver builds the source checks and compiler, emits
`.lake/build/kernel-check/checker-m0-0.wasm`, and invokes it with caller-supplied
arguments. It checks small levels, the signed i64 boundary, the largest
representable successor, and overflow against both mathematical BigInt succession
and standard Lean evaluation of the same 32 inputs.
It fails if the returned word differs from the expected result.

`SortTest.lean` also checks the source function's boundary behavior and asks
Lean to validate `Sort 0 : Sort 1`, `Sort 1 : Sort 2`, and `Sort 2 : Sort 3`.
These are focused source checks, not a generic compiler-correctness theorem.

### Run the generated artifact

Once built, only the WASM file and Wasmtime are required:

```sh
build/tools/wasmtime/current/wasmtime run --invoke checkSort .lake/build/kernel-check/checker-m0-0.wasm 0 1
build/tools/wasmtime/current/wasmtime run --invoke checkSort .lake/build/kernel-check/checker-m0-0.wasm 0 0
build/tools/wasmtime/current/wasmtime run --invoke checkSort .lake/build/kernel-check/checker-m0-0.wasm 1 2
```

Expected results: `0`, `1`, and `0`. These accept `Prop : Type`, reject
`Prop : Prop`, and accept `Type : Type 1`.

Wasmtime's CLI accepts signed i64 arguments. To supply UInt64 maximum,
use its two's-complement spelling `-1`; `checkSort ... -1 0` returns `2`.
The regression driver converts boundary inputs automatically.

## M0.1: concrete universe operations

`node test/kernel_universe.js` builds `checker-m0-1.wasm` and checks 98
WASM results against mathematical expectations and standard Lean.
The scalar entry is `checkLevelOp op u v expected`: operation 0 is `max`,
1 is `imax`; results are 0 for a correct claim, 1 for an incorrect claim,
and 3 for an unsupported operation. In particular, `imax u 0 = 0`.

```sh
build/tools/wasmtime/current/wasmtime run --invoke checkLevelOp .lake/build/kernel-check/checker-m0-1.wasm 1 7 0 0
build/tools/wasmtime/current/wasmtime run --invoke checkLevelOp .lake/build/kernel-check/checker-m0-1.wasm 0 7 0 0
```

These return 0 and 1. No symbolic universe expressions are supported yet.

## M0.2: validated term graphs

`node test/kernel_graph.js` builds `checker-m0-2.wasm` and checks 17
WASM/standard-Lean cases. Build the existing array host once with
`tools/build-wasmtime-host.sh`. The entry is `validateGraph graph root`.

Each zero-based node occupies three UInt64 words:

| Tag | First payload | Second payload |
|---|---|---|
| 0: Sort | concrete universe level | 0 |
| 1: bvar | de Bruijn index | 0 |
| 2: Pi | domain node ID | body node ID |
| 3: lambda | domain node ID | body node ID |
| 4: application (from M0.8) | function node ID | argument node ID |
| 5: let (from M0.10) | value node ID | lambda node carrying annotation/body |

Every child must precede its parent. The entire array is validated, including
unreachable nodes; the root must exist. Result 0 means structurally valid;
4 means malformed. An open bvar is structurally valid: scope and typing
are separate operations.

```sh
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-2.wasm validateGraph i64 array-u64:0,0,0 i64:0
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-2.wasm validateGraph i64 array-u64:2,0,0 i64:0
```

These return 0 and 4 (the second graph contains a self-reference).

## M0.3: scope and shifting

`node test/kernel_binding.js` builds `checker-m0-3-scope.wasm` and
`checker-m0-3-shift.wasm`. It checks 13 scope results and 12 exact shift
outputs against standard Lean and independently specified expectations.

- `checkScope graph root depth fuel` checks the reachable term with `depth`
  surrounding binders. A binder extends scope only in its body.
- `shiftGraph graph root cutoff delta fuel` raises free indices at or above
  `cutoff`. A successful result is `[0, newRoot, ...newGraph]`; failure is
  `[status]`. The original graph is retained and new nodes appended.

Both use explicit traversal stacks. Fuel counts visited frames (including
reconstruction frames for shifting), so sharing cannot evade the budget.
Status 1 means an out-of-scope variable, 2 means index/depth overflow,
4 means malformed structure, and 5 means exhausted fuel. Success is 0.
Neither operation establishes that the term is well typed.

```sh
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-3-scope.wasm checkScope i64 array-u64:0,0,0,1,0,0,3,0,1 i64:2 i64:0 i64:10
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-3-shift.wasm shiftGraph array-u64 array-u64:1,0,0 i64:0 i64:0 i64:1 i64:10
```

These return `0` and `[0, 1, 1, 0, 0, 1, 1, 0]`, respectively. The second
result appends bvar 1 and returns its node ID (1).

## M0.4: validated contexts and variable typing

`node test/kernel_infer.js` builds `checker-m0-4.wasm` and checks 14 exact
WASM/standard-Lean results. `inferOpen graph context root fuel` returns
`[0, inferredTypeRoot, ...graph]` or `[status]`. Context entries are node IDs
of assumption types, oldest first; each type is expressed relative to the
preceding context. The checker admits them in order only after inferring a
Sort for each. They remain explicit local assumptions, not closed theorems.

Variable lookup lifts the stored type across the variable itself and every
newer binder. Unsupported forms return 3; out-of-scope variables and non-type
assumptions return 1. Fuel is shared across admission, inference and shifting.

```sh
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-4.wasm inferOpen array-u64 array-u64:0,1,0,1,0,0 array-u64:0,1 i64:1 i64:20
```

This checks `A : Sort 1, x : A |- x : A`. It returns
`[0, 3, 0, 1, 0, 1, 0, 0, 0, 2, 0, 1, 1, 0]`:
the inferred type at node 3 is bvar 1, referring to A across x's binder.

## M0.5: Pi formation

`node test/kernel_pi.js` builds `checker-m0-5.wasm`; its `inferPi` entry uses
the same graph/context/root/fuel interface as `inferOpen`. Ten cases check
formation of `∀ p : Prop, p → p : Prop`, concrete-universe identity types,
large impredicative domains, invalid domains/bodies, and resource limits.
`PiTest.lean` also asks Lean itself to check the stated universe judgments.

Both the domain and body must infer to Sorts; their levels are combined by
`imax`. Inference uses explicit frames with a shared work budget. The earlier
inference command now supports Pi types too, including Pi context entries.
These commands infer a proposition's sort; they do not yet check its proof.

```sh
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-5.wasm inferPi array-u64 array-u64:0,0,0,1,0,0,1,1,0,2,1,2,2,0,3 array-u64: i64:4 i64:100
```

This returns a success packet whose inferred root is `Sort 0`.

## M0.6: the first closed proof

`node test/kernel_check.js` builds `checker-m0-6.wasm`. The entry is
`checkProof graph proofRoot claimedTypeRoot fuel`. It validates the claimed
type, infers the proof's type, and compares their structure with shared fuel.
Lambdas check their annotations even if the bound variable is unused.
No global declarations, universe parameters, axioms, or native Lean calls
are involved in the generated checker.

```sh
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-6.wasm checkProof i64 array-u64:0,0,0,1,0,0,1,1,0,2,1,2,2,0,3,3,1,1,3,0,5 i64:6 i64:4 i64:200
```

This returns 0 for `fun (p : Prop) (hp : p) => hp : ∀ p : Prop, p → p`.
The 12-case corpus also checks Type identity, equal types represented by
different IDs, a false `p → q` claim, wrong bodies, invalid annotations,
invalid claimed types, malformed input, and exhaustion. Standard Lean checks
the same observable results and the genuine identity theorems in the source.

This fragment has Sort, bvar, Pi and lambda only. Structural comparison is
sufficient for its well-typed types. Beta conversion, applications, lets,
globals, inductives, and symbolic universes are still absent. When those
forms arrive, missing conversion must be reported as inconclusive.

## M0.7: capture-avoiding substitution

`node test/kernel_substitution.js` builds `checker-m0-7.wasm` and checks 12
exact graph outputs in WASM and standard Lean. `instantiateGraph graph body
argument fuel` removes the outermost binder from body: index 0 is replaced by
the argument, outer indices decrease, and the argument is lifted under nested
binders. Open terms are allowed. The result packet matches `shiftGraph`.

```sh
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-7.wasm instantiateGraph array-u64 array-u64:0,0,0,1,0,0 i64:1 i64:0 i64:10
```

This replaces bvar 0 by Sort 0 and returns `[0, 0, 0, 0, 0, 1, 0, 0]`.
Substitution and every nested shift consume one shared work budget.
This operation does not itself check types or normalize terms.

## M0.8: application typing

`node test/kernel_application.js` builds `checker-m0-8.wasm`; the entry
`checkApplication` has the same graph/proof/type/fuel arguments as `checkProof`.
Seven cases accept implication composition, dependent application and applied
identity, reject clear argument/type errors, and report unsupported (3) for
cases requiring beta conversion. The genuine composition and dependent
application terms are also checked by Lean in `ApplicationTest.lean`.

Tag 4 adds application. Its two children share the surrounding scope; it binds
no variable. Inference requires an exposed Pi, checks the argument against its
domain, then instantiates the codomain using the tested substitution operation.
Structural mismatches below applications are conservative: missing conversion
or proof irrelevance must not be reported as a definite rejection.

## M0.9: beta reduction and bounded conversion

`node test/kernel_conversion.js` builds `checker-m0-9.wasm` (entry
`checkConversion`, same proof interface) and `checker-m0-9-reduce.wasm`
(entry `reduceHead graph root fuel`, returning a graph packet).
Five conversion and four reduction cases pass in WASM and standard Lean.
The two formerly unsupported application-suite beta cases now pass too.

Reduction maintains an argument spine, reuses capture-avoiding instantiation,
and shares the work budget. Conversion normalizes each compared head and
then compares children. Type inference also reduces before requiring a Sort
or Pi. The corpus checks capture avoidance, a type-level identity application,
a function type exposed by beta reduction, a definite universe mismatch,
and an untyped looping term that exhausts its reduction budget.

```sh
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-9-reduce.wasm reduceHead array-u64 array-u64:0,0,0,1,0,0,3,0,1,4,2,0 i64:3 i64:100
```

This reduces `(fun x : Prop => x) Prop` syntactically to `Prop`; the standalone
reducer makes no typing claim about its input. The checker always checks
original subterms before using reduction on their types. Eta/proof irrelevance
remain incomplete; the test requiring eta returns unsupported (3).
Fuel exhaustion returns 5, never an incorrect-proof verdict.

## M0.10: checked lets and zeta reduction

`node test/kernel_let.js` builds `checker-m0-10.wasm`; `checkLet` has the
same proof/type/fuel interface. Eight cases check ordinary proof lets,
dependent local definitions, lets in function/type positions, malformed
binder containers, and invalid annotations/values, including unused values.

A tag-5 node points to its value and a tag-3 binder container. The container's
domain is the declared type and its body is the let body. This preserves the
three-word graph format and makes binding behavior explicit. Inference checks
the annotation as a type and the value against it **before** substituting into
and checking the body. Reduction also supports zeta substitution.

```sh
build/tools/leanexe-wasmtime-host call .lake/build/kernel-check/checker-m0-10.wasm checkLet i64 array-u64:0,1,0,0,0,0,1,0,0,3,0,2,5,1,3 i64:4 i64:0 i64:100
```

This returns 0 for `let A : Type := Prop; A : Type`.

## M0.11: a real Lean export

`node test/kernel_export.js` builds `checker-m0-11.wasm`, decodes the unchanged
pinned-Lean export of `implicationIdentity`, and passes its type and body to
WASM. It accepts the real proof and rejects a well-scoped corruption through
the same path. Fourteen malformed/unsupported adapter cases are rejected;
exhaustion remains separate from rejection. The binary has no imports.

```sh
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m0-11.wasm test/fixtures/kernel-check/identity.ndjson
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m0-11.wasm test/fixtures/kernel-check/identity-corrupt.ndjson
```

The reports are `accepted` (exit 0) and `rejected` (exit 1), with zero globals,
universe parameters and axioms. After preparation these commands require no
Lean or Tenet. See the [fixture receipt](../../test/fixtures/kernel-check/README.md)
for the exact exporter revision, hashes, decoder limits, and reproduction command.

The host adapter handles syntax only. Inference, checking and conversion stay
in the LeanExe-compiled artifact. Adapter fidelity and overall soundness are
not formally proved; the source proof coverage remains limited to P0/P1.

## M1.0: exported applications

`node test/kernel_export.js composition` builds `checker-m1-0.wasm` and checks
an actual exported implication-composition proof, `fun p q r f g hp => f (g hp)`.
Its two application records exercise the existing application checker. Changing
`g hp` to `g f` stays well scoped and is rejected. The gate also covers nineteen
adapter failures, exhaustion, exact decoding, and the import-free artifact.
No kernel implementation or source-proof coverage changed.

```sh
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m1-0.wasm test/fixtures/kernel-check/composition.ndjson
node tools/kernel-check-export.js .lake/build/kernel-check/checker-m1-0.wasm test/fixtures/kernel-check/composition-corrupt.ndjson
```

These return accepted/exit 0 and rejected/exit 1. Reproduce the frozen export
with `node tools/kernel-export-fixture.js composition`.

## Next checkpoint

M1.1 extends the adapter to lets before tackling symbolic levels
and global declarations. See the [full plan](../../plans/lean-kernel-checker.md).
This remains a PoC: larger source proofs may be deferred, and no WASM proof
work is planned now.
