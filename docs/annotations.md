# WebAssembly Annotations

LeanExe emits a JSON sidecar that describes selected regions of its structured WebAssembly instruction output.  The sidecar gives proof-generation tools stable names, locations, local roles, control information, and scalar descriptors without requiring them to infer every region from WAT.  Every retained proof checks the selected region against the exact decoded artifact before using its semantic theorem.

## Files and trust boundary

The compiler writes `program.annotations.json` beside the compiled WASM when the caller requests annotations.  `tools/leanexegen annotate` validates that document, checks its regions against the proof package's decoded Talos module, writes `proof-recipes.json`, and generates `AnnotationMatches.lean` inside the proof workspace.  The generated Lean module contains the equalities, descriptor equations, frame facts, and adapters selected for that artifact.

The JSON sidecar is untrusted input to the artifact proof.  Its byte length, function indexes, structured paths, instruction intervals, parameters, and descriptor contents must agree with the frozen package and decoded program.  A stale or fabricated annotation cannot establish a theorem because its generated Lean equality fails against the exact artifact region.

Compiler declarations named in `generatedBy` explain where a region came from and support maintenance and retrieval.  They do not become proof premises.  The retained package may be verified after deleting the compiler, source program, and original annotation file because the checked generated declarations and exact artifact remain sufficient.

## Schema

The compiler emits annotation schema 1.  A document contains artifact metadata and a list of defined functions.  Each function records source and WASM identities, signature dimensions, combined local count, exports, and semantic regions.

```json
{
  "schemaVersion": 1,
  "artifact": { "byteLength": 1938 },
  "functions": [
    {
      "wasmIndex": 0,
      "definedFunction": 0,
      "sourceName": "Example.Source.helper",
      "exports": [],
      "parameters": 1,
      "results": 1,
      "locals": 23,
      "regions": [
        {
          "id": "function-0.scalar-post-test-loop-0",
          "kind": "leanexe.loop.scalar-post-test.v1",
          "location": {
            "listPath": [],
            "startIndex": 14,
            "endIndex": 15
          },
          "parameters": {},
          "generatedBy": [
            "LeanExe.Wasm.Binary.CoreWasm.emitLoopFoldMultiSlot"
          ]
        }
      ]
    }
  ]
}
```

`listPath` traverses nested structured instructions.  Each path step names an instruction index and one field, such as the body of a block or loop or one branch of an `if`.  `startIndex` is inclusive and `endIndex` is exclusive within the selected instruction list.

Region identifiers are unique within a document and stable for a fixed emitted structure.  A kind name includes a version because changing its semantic interpretation requires a new kind rather than a silent reinterpretation.  Unknown kinds, unknown fields, malformed coordinates, duplicate identifiers, and inconsistent dimensions make strict validation fail.

## Compiler-emitted region kinds

The current compiler emits twelve region kinds.  The parameter object differs by kind and records only data required for validation, semantic adapters, or proof retrieval.  Human labels and source expressions may guide a proof agent, but numeric and structural fields determine generated checks.

| Region kind | Described structure |
|-------------|---------------------|
| `leanexe.call.direct.v1` | A direct call with argument sources, callee index, result locals, result placement, and continuation. |
| `leanexe.array.map-add.v1` | A complete bounded fixed-array wrapper that adds one constant to each accepted input element. |
| `leanexe.array.filter-lt.v1` | A complete bounded fixed-array wrapper that retains elements below a constant threshold. |
| `leanexe.loop.fold.v1` | A recognized general loop-fold emission with accumulator, staging, completion, release, and result locals. |
| `leanexe.array.fold.v1` | A fixed-array fold with traversal bounds, direction, source width, accumulator layout, scalar descriptor, and result placement. |
| `leanexe.loop.while.v1` | A source while loop whose condition and body reify into a supported scalar descriptor. |
| `leanexe.loop.scalar-post-test.v1` | A post-test scalar loop produced from a multi-slot fold or counter-transfer shape. |
| `leanexe.array.length-dispatch.v1` | A fixed-size or bounded-length public input check and its valid and invalid branches. |
| `leanexe.array.search-key.v1` | One indexed key load within a fixed-array search. |
| `leanexe.array.eq-node.v1` | One equality decision node with operand order and branch roles. |
| `leanexe.array.lt-node.v1` | One unsigned comparison node with operand order and branch roles. |
| `leanexe.array.pair-result.v1` | Construction and return of a two-word fixed-array result. |

Structured LTG also uses semantic labels such as `leanexe.array.allocator.v1`, `leanexe.array.allocator-window.v1`, and `leanexe.array.singleton-wrapper.v1`.  Those labels identify artifact-side matched or composed proof motifs rather than additional compiler-emitted region records.  The distinction prevents the LTG vocabulary from being mistaken for the sidecar schema.

## Scalar descriptors and compiler theorems

Scalar loop and array-fold regions may carry a versioned descriptor for their expressions, conditions, statements, and post-test control.  Constants use decimal strings so JSON number limits cannot change `UInt64` values.  The descriptor also identifies scratch-local boundaries and the accumulator or result locals needed to state frame preservation.

`LeanExe.Wasm.ScalarDescriptor` defines the descriptor syntax and structured instruction emission.  `LeanExe.Wasm.ScalarCertificate` proves that successful reification from supported IR expressions, conditions, statements, and loops agrees with the compiler emitter.  These theorems detect drift inside annotation production, while the artifact package separately proves equality between the descriptor program and the decoded instruction region.

The proof consumer evaluates a descriptor over a compact `UInt64` state and generates named condition and body equations.  Neutral ProofKit theorems connect those equations to Talos locals and weakest-precondition execution.  The application proof supplies the invariant, measure, representation facts, and terminal mathematics.

## Recipe generation

`proof-recipes.json` is a strict generated plan over the validated regions.  Each recipe names its region kind, exact match theorem, compatible ProofKit theorem, required imports, generated semantic facts, applicable LTG entries, and the premises left to the artifact proof.  Composition records connect compatible recipes when a checked theorem spans several regions or a region plus a recognized suffix.

The consumer currently generates support for these recurring boundaries:

| Boundary | Generated support |
|----------|-------------------|
| Direct calls | Exact selected-program equality plus argument and result placement data. |
| Length dispatch | Exact valid and invalid branch equality, fixed or bounded input facts, and compatible dispatch tactics. |
| Search trees | Key-load, equality-node, less-than-node, and result-construction equalities used by chain and tree theorems. |
| Map and filter | Whole-function equality to neutral bounded-wrapper programs. |
| Scalar loops | Exact descriptor-program equality, evaluated transition equations, read and write sets, and frame preservation. |
| Array folds | Setup, traversal, continuing body, exit, frame accessor, allocation, result suffix, and completion adapters where their structural matchers succeed.  A matched forward fold also receives a checked equality from `FixedArrayFold.forwardSetupFrame` over its generated continuing frame to the initialized continuing frame. |
| Results | Singleton or pair representation support, result-local placement, stores, and public return. |

A recipe records optional help rather than a mandatory script.  A proof agent may select the direct semantic theorem, a lower-level generated equality, a tactic, or ordinary Talos reasoning according to the residual goal.  Independent acceptance checks the imports and theorem result regardless of the route taken.

## Controlled annotation runs

The standard command validates every compiler region and exposes every compatible recipe:

```sh
tools/leanexegen annotate \
  -o ./tmp/annotated.proof \
  demos/demo-9/program.proof
```

`--only-region <region-id>` retains one semantic region plus mandatory direct-call coverage.  Repeating the flag retains several named regions.  This mode supports fixed-artifact comparisons that isolate one annotation family while preserving the specification, source, WASM bytes, decoded module, ProofKit, toolchain, and outer verification.

```sh
tools/leanexegen annotate \
  --only-region function-0.scalar-post-test-loop-0 \
  -o ./tmp/scalar-loop.proof \
  demos/demo-1/program.proof
```

The command does not regenerate the source or WASM.  It fails when the input package cannot support current annotations, a requested region does not exist, the compiler sidecar is malformed, a matcher rejects the decoded instructions, or a generated Lean declaration fails.  `tools/leanexegen verify` performs the independent package check after proof construction.

## Retrieval and evidence

Every validated region contributes task features and candidate annotation kinds to knowledge retrieval.  Extractor version six records fixed-array length dispatches emitted in the equality-normalized, inequality-normalized, and unsigned-bound forms, including the input local, expected size, and encoding.  The task snapshot includes each selected package's entries after exact-artifact exclusions, while category indexes, features, maturity, consumers, and annotation kinds guide the agent's file search.  Proof recipes name declarations and tactics so the agent can retrieve detailed guidance after inspecting its residual goal.

The demonstrations retain fixed-artifact experiments showing successful and failed uses of annotation support.  Evidence includes proof-generation time, outer-check time, journal observations, retrieval, revisions, proof structure, shared theorem use, and transfer across programs.  [Artifact Proving](artifact-proving.md) defines this evaluation, while the [benchmark index](../benchmarks/README.md) and demo experiment directories preserve individual runs.

## Extension rules

A new region kind begins with a recurring emitted motif and a structural matcher over `LeanExe.Wasm.Instr`.  Its schema must identify every local role, bound, continuation, and descriptor field required by the proposed proof theorem.  The change must include compiler JSON tests, strict consumer validation, positive artifact matches, opcode and coordinate mutations, generated Lean checks, LTG metadata, and at least one independently accepted proof package.

A matcher must reject ambiguous or partial structures rather than issue a broad recipe.  Generated semantic theorems must remain neutral with respect to one source function, and application-specific mathematics belongs in the artifact proof or a checked worked example.  Promotion and automatic selection require transfer evidence according to the root [Development Plan](../plan.md).
