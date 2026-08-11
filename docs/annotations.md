# WebAssembly Annotation Sidecar

Date: 2026-08-06

## Objective

LeanExe should optionally emit a machine-readable annotation file beside each WebAssembly module.  The file should describe generated functions, local-variable roles, ABI representations, nested code-generation regions, control-flow relationships, and the compiler definitions responsible for those regions.  An artifact prover can use this information to divide a function, select checked lemmas, instantiate tactics, and construct a proof outline without rediscovering the compiler's decisions from thousands of WebAssembly instructions.

The annotations constitute untrusted proof-search guidance.  The artifact theorem must continue to quantify over the module decoded from the exact WASM bytes, without importing the Lean source, trusting the compiler, or assuming any annotation is true.  An annotation consumer must match every region it uses against the decoded instruction tree, and Lean must reject any incorrect semantic conclusion.

This work addresses a measured proof-generation bottleneck.  `leanexegen` currently scans the WAT-derived Talos program for fixed instruction patterns, including fixed-array search nodes and length dispatches, even though the compiler knew those structures while emitting them.  The current extractors recover a small portion of that information through JavaScript pattern matching and do not explain arbitrary loops, calls, nested results, ownership operations, or continuations.

## Design

### Outputs and trust boundary

Compilation should produce `program.wasm` and, when requested, `program.annotations.json`.  The initial CLI should accept an explicit `--annotations <path>` argument so ordinary compilation retains its current output behavior, while `leanexegen` always requests the sidecar.  Once the schema and consumers stabilize, a separate decision can determine whether sibling annotation output becomes the default.

The sidecar should identify the artifact by byte length and SHA-256 digest.  The current vertical slice emits the byte length, while the proof package manifest binds both the WASM and the sidecar by SHA-256.  Standalone sidecar distribution requires the compiler output to include the WASM digest, and the proof tool must reject a mismatched identity before reading any region.

The sidecar should remain separate from the WASM module rather than use a custom section.  A separate file leaves the executable bytes unchanged, permits annotation improvements without recompiling the artifact, and lets an artifact verifier discard the sidecar after producing a checked proof.  A custom section could be added later for distribution convenience, but it should contain the same schema and should not become part of the proof's trust boundary.

The proof consumer must treat annotation failures as diagnostics rather than assumptions.  A missing region, invalid path, mismatched parameter, or unrecognized instruction sequence prevents that annotation from selecting a theorem.  `leanexegen` should use a strict mode during development so annotation defects fail visibly instead of disappearing behind slower heuristic analysis.

### Annotation coordinates

Each annotated region should name a function and a location in its structured instruction tree.  `location.listPath` selects nested instruction lists through explicit block-body, loop-body, then-branch, or else-branch steps, while `startIndex` and `endIndex` delimit a half-open interval in the selected list.  This coordinate system matches the structured `LeanExe.Wasm.Instr` value produced before serialization and the nested instruction lists used by Talos.

The serializer should also calculate an optional half-open byte range for each region.  Absolute byte offsets help a person correlate the sidecar with a disassembler and locate the generated code in the distributed binary.  Proof matching should use the structured path because variable-length encodings and section framing make byte ranges a poor representation of semantic nesting.

Regions form a tree.  A child region lies inside its parent's instruction subtree, siblings do not overlap, and control-flow references use region identifiers rather than overlapping ranges.  This constraint gives the proof consumer an unambiguous decomposition and prevents multiple incompatible descriptions of the same instructions.

### Vocabulary and versioning

Region kinds should use a stable, versioned, compiler-neutral vocabulary such as `leanexe.array.get.checked.v1`.  The compiler must not emit names of Lean proof theorems or tactics.  The proof tool maps a region kind to the current proof-kit theorem, allowing the proof library to change without revising the annotation format.

Each region kind owns a typed parameter schema.  A checked array load records the array local, index expression or local, element width, payload slot, scratch-local window, and result location.  A consumer rejects missing, additional, or ill-typed parameters for a recognized schema version.

Schema versions and region-kind versions serve different purposes.  `schemaVersion` changes when the JSON representation changes, while the suffix on a region kind changes when the generated instruction template or parameter meaning changes.  Consumers should reject unsupported major schema versions and unknown versions of any region they attempt to use.

The first vocabulary should cover the regions already responsible for most of the proof text in Demos 1, 2, and 3.  It should also include loop metadata because loops are the next general proof boundary beyond the fixed, unrolled examples.  The following table defines the initial scope.

| Kind | Required information | Intended proof use |
|---|---|---|
| `leanexe.entry.fixed-array.v1` | Export, input local, result local, element width, and child mask. | Establish the public ABI frame and choose the wrapper proof strategy. |
| `leanexe.array.length-dispatch.v1` | Input local, expected length, valid branch, invalid branch, and continuation. | Apply the fixed-length dispatch theorem and expose two semantic obligations. |
| `leanexe.array.search-key.v1` | Array local, element index, key local, and scratch window. | Establish a saved key consumed by a matched search node. |
| `leanexe.array.get.checked.v1` | Array local, index, result local or stack result, element width, slot, and scratch window. | Apply a checked indexed-load theorem with the correct frame. |
| `leanexe.array.eq-node.v1` | Local-window offset, element index, key local, operand order, branch roles, and continuation. | Select the equality-node theorem and preserve branch continuations. |
| `leanexe.array.lt-node.v1` | Local-window offset, element index, key local, unsigned comparison, branch roles, and continuation. | Prove one binary-search decision without rediscovering the checked load. |
| `leanexe.array.pair-result.v1` | Constant or indexed-input value form, allocator window, destination local, and continuation. | Apply the complete two-word allocation and represented-result theorem. |
| `leanexe.array.map-add.v1` | Maximum input size, wrapping addend, complete function boundary, and return continuation. | Apply the complete bounded-map wrapper theorem. |
| `leanexe.array.filter-lt.v1` | Maximum input size, unsigned threshold, complete function boundary, and return continuation. | Apply the complete bounded-filter wrapper theorem and its heap-reserve model. |
| `leanexe.array.fold.v1` | Source and result widths, direction, bounds, accumulator and element locals, body expressions, scratch layout, exact structured path, and result placement. | State a prefix-fold invariant from compiler-known local roles and prove its application-specific transition. |
| `leanexe.runtime.allocate.v1` | Size expression, allocator locals, globals, memory-growth branch, and destination. | Select the allocator theorem and establish its post-frame. |
| `leanexe.runtime.retain.v1` | Pointer location, runtime function index, and continuation. | Apply the retain theorem at the emitted ownership boundary. |
| `leanexe.runtime.release.v1` | Pointer location, runtime function index, and continuation. | Apply the release theorem at the emitted ownership boundary. |
| `leanexe.call.direct.v1` | Callee index, argument locations, result locations, and continuation. | Apply a previously proved function theorem and restore the caller frame. |
| `leanexe.loop.while.v1` | Structured region, IR condition and body, scratch-local start, and continuation. | Recover the machine-state transition map before selecting an invariant and measure. |
| `leanexe.loop.scalar-post-test.v1` | Exact block-wrapped body-first loop, scalar descriptor, accumulator frame, result slot, and continuation. | Apply the checked post-test transition and generated function-entry theorem. |
| `leanexe.loop.fold.v1` | Accumulator locals, initial and next-state expressions, body lets, done expression, staging locals, release offsets, results, and continuation. | Construct the loop invariant and decreasing measure from compiler-known structure. |

The sidecar should record the compiler revision when the build can identify one, together with whether the compiler tree contained uncommitted changes.  A stable, fully qualified compiler definition such as `LeanExe.Wasm.Binary.CoreWasm.emitArrayGetSlot` is more useful than a source line number, which changes during unrelated edits.  A generator chain may name several definitions when one semantic region combines expression emission, comparison normalization, and branch construction, while proof generation must remain independent of this diagnostic provenance.

### Module, function, and local descriptions

Module annotations should describe the memory index, runtime-global roles, generated runtime functions, and public ABI representations.  Function annotations should record the full WASM function index, the defined-function ordinal, exports, parameter and result types, source declaration when available, and local roles.  These facts let the proof generator create the initial frame without inferring stable compiler conventions from each artifact.

Local roles should describe meaning without claiming values.  Examples include `input-array-pointer`, `search-key`, `array-index`, `loaded-element`, `allocator-root`, `result-pointer`, `loop-index`, and `loop-accumulator`.  Region parameters then refer to local numbers and make the circumstances under which a role has its intended value explicit.

ABI representation annotations should describe data layout independently of a particular source program.  An array annotation records its length-header offset, payload offset, element slot width, child-pointer mask, and ownership convention.  A result region can refer to that representation rather than repeat the same constants and assumptions.

### Control flow and continuations

Region boundaries alone will not solve the branch-composition cost observed in Demos 2 and 3.  Each branch region should identify its semantic successors and the continuation reached after fallthrough.  A proof consumer can then construct the nested weakest-precondition outline before asking Codex to prove branch-specific facts.

Branch roles should remain descriptive.  Values such as `valid-input`, `invalid-input`, `equal`, `unequal`, `less`, `greater-or-equal`, `allocation-failed`, and `allocation-succeeded` explain compiler intent and determine which continuation applies.  The consumer still checks the branch condition and instruction sequence against the artifact.

Loop annotations need enough structure to propose an invariant without embedding a source theorem.  The compiler should report the induction local, initial value, bound expression, step, direction, accumulator locals, element locals, body region, exit region, and continuation.  The proof kit can map those fields to a general counted-loop theorem, while Codex supplies the application-specific invariant relating the accumulator to the desired result.

### Example

The following fragment illustrates the intended full representation for part of Demo 2.  The implemented direct-call slice uses the same `location` form, while the other region kinds, byte ranges, compiler identity, representations, parents, and successors remain planned fields.  Numeric instruction paths and byte ranges are illustrative, and a complete sidecar must define every referenced identifier.

```json
{
  "schemaVersion": 1,
  "artifact": {
    "byteLength": 7336,
    "sha256": "ceb37cd3d61158e7f4162c97cac9b79022518a4e67f895d45a3619c7b5a29712"
  },
  "compiler": {
    "name": "LeanExe",
    "revision": "<compiler revision>",
    "modified": false
  },
  "representations": {
    "array.u64.v1": {
      "lengthOffset": 0,
      "payloadOffset": 8,
      "elementSlots": 1,
      "elementBytes": 8,
      "childMask": 0
    }
  },
  "functions": [
    {
      "wasmIndex": 0,
      "definedFunction": 0,
      "exports": ["compute"],
      "parameters": ["i64"],
      "results": ["i64"],
      "locals": {
        "0": "input-array-pointer",
        "2": "search-key",
        "15": "input-array-pointer",
        "16": "array-index",
        "18": "loaded-element"
      },
      "regions": [
        {
          "id": "entry",
          "parent": null,
          "kind": "leanexe.entry.fixed-array.v1",
          "location": {
            "listPath": [],
            "startIndex": 0,
            "endIndex": 412
          },
          "byteRange": { "start": 117, "end": 6041 },
          "parameters": {
            "inputLocal": 15,
            "resultLocal": 1,
            "elementWidth": 1,
            "childMask": 0
          },
          "generatedBy": [
            "LeanExe.Wasm.Binary.CoreWasm.emitFuncInstrs"
          ]
        },
        {
          "id": "length-dispatch",
          "parent": "entry",
          "kind": "leanexe.array.length-dispatch.v1",
          "location": {
            "listPath": [
              { "instructionIndex": 0, "field": "then" }
            ],
            "startIndex": 0,
            "endIndex": 37
          },
          "parameters": {
            "inputLocal": 15,
            "expectedLength": 21
          },
          "successors": {
            "valid": "search-key",
            "invalid": "not-found-result",
            "continuation": "return"
          },
          "generatedBy": [
            "LeanExe.Wasm.Binary.CoreWasm.emitCondWithRelease",
            "LeanExe.Wasm.Binary.CoreWasm.emitStmt"
          ]
        },
        {
          "id": "search-key",
          "parent": "length-dispatch",
          "kind": "leanexe.array.key-load.v1",
          "location": {
            "listPath": [
              { "instructionIndex": 0, "field": "then" }
            ],
            "startIndex": 3,
            "endIndex": 17
          },
          "parameters": {
            "arrayLocal": 15,
            "elementIndex": 0,
            "keyLocal": 2,
            "scratchWindow": 10
          },
          "generatedBy": [
            "LeanExe.Wasm.Binary.CoreWasm.emitArrayGetSlot"
          ]
        },
        {
          "id": "search-node-0",
          "parent": "length-dispatch",
          "kind": "leanexe.compare.eq-branch.v1",
          "location": {
            "listPath": [
              { "instructionIndex": 0, "field": "then" }
            ],
            "startIndex": 7,
            "endIndex": 31
          },
          "parameters": {
            "left": { "arrayLocal": 15, "elementIndex": 1 },
            "right": { "local": 2 },
            "operandOrder": "loaded-first",
            "scratchWindow": 10
          },
          "successors": {
            "equal": "found-result-0",
            "unequal": "search-node-1",
            "continuation": "return"
          },
          "generatedBy": [
            "LeanExe.Wasm.Binary.CoreWasm.emitArrayGetSlot",
            "LeanExe.Wasm.Binary.CoreWasm.emitCondWithRelease"
          ]
        }
      ]
    }
  ]
}
```

### Human inspection

The JSON file should remain readable, but a small repository tool should render it as an indented function and region tree after validation.  Each rendered row should show the structured path, byte range, region kind, principal parameters, branch destinations, and generator definitions.  This view gives a maintainer a direct route from one WASM region to the lowering functions that emitted it without placing prose in the schema.

The renderer should use the same parser and structural matcher as the proof consumer.  It should distinguish reported metadata from regions that matched the artifact and print mismatches as errors with the exact function and path.  A human explanation produced from unchecked JSON would conceal stale or incorrect annotations and would provide little evidence during proof debugging.

### Compiler implementation

The compiler already lowers the IR to the structured instruction type in `LeanExe/Wasm/Instr.lean`.  Functions such as `emitExpr`, `emitStmt`, and `emitFuncInstrs` in `LeanExe/Wasm/Binary.lean` produce `List Instr`, and `encodeInstrs` serializes that tree.  Annotation production belongs in this lowering layer, before byte serialization and without inspecting WAT.

The recommended internal representation is an emitted fragment containing code and relative regions.  Fragment combinators should concatenate instruction lists, prefix paths when wrapping a block or loop, distinguish then and else paths when constructing an `if`, and add a parent region around a completed fragment.  Serializing the fragment's `code` must produce the same bytes as the current emitter.

```lean
structure Emitted where
  code : List LeanExe.Wasm.Instr
  regions : Array RelativeRegion

def Emitted.append : Emitted → Emitted → Emitted
def Emitted.block : Emitted → Emitted
def Emitted.loop : Emitted → Emitted
def Emitted.iff : Bool → Emitted → Option Emitted → Emitted
def Emitted.mark : RegionKind → RegionParameters → Emitted → Emitted
```

The compatibility path should expose `emitFuncInstrs` as the `code` projection of an annotated function emission during migration.  Untouched helpers can initially lift an ordinary `List Instr` into an unannotated fragment, allowing instrumentation to proceed region by region.  The annotated path should eventually become canonical so later emitter changes cannot update code while silently leaving a parallel annotation analysis stale.

The serializer should resolve relative structured paths after it assembles a complete function body.  A traversal over `encodeInstr` lengths can assign instruction-byte ranges, after which module assembly adds the code-section and function-body offsets.  This calculation should share the existing encoder rather than duplicate opcode or LEB128 length logic.

This representation fits the planned [Emitter Restructuring](emitter.md).  That work introduces a structured module value between IR lowering and byte serialization, while annotations add provenance and semantic regions to the same value.  The two designs should use one structured emission path rather than create separate models of the generated module.

### Proof-consumer implementation

`leanexegen` should parse and validate the sidecar before constructing the artifact-proof task.  It should resolve each function and structured path in the decoded Talos module, confirm that parent and successor references are valid, and run a kind-specific structural matcher over every region it plans to use.  The matcher checks instruction constructors and annotation parameters, including local indices, constants, operand order, branch bodies, and continuations.

A successful match produces a proof plan rather than a theorem assumption.  The plan selects proof-kit imports, theorem names, tactic arguments, helper-theorem order, and a deterministic weakest-precondition skeleton.  Codex receives the remaining semantic obligations, the checked plan, and the ordinary Lean command used to test its work.

No generated Lean declaration should assert an annotation as a fact.  A region matcher may generate an equality between an exact instruction subtree and a proof-kit template, but Lean must prove that equality by reduction or decision.  The final behavioral theorem should continue to compile if the sidecar and compiler are removed after proof generation.

The existing WAT pattern extractors should remain temporarily as a comparison and fallback for artifacts compiled without annotations.  Annotated benchmark runs should disable that fallback so the experiment measures the new path and exposes incomplete metadata.  Once annotation coverage exceeds the old extractor and the measured results justify the change, the duplicated pattern rules can be removed.

### Proof-recipe registry

The proof repository should maintain a versioned recipe registry from validated region kinds to proof methods.  The compiler sidecar should continue to use neutral region kinds and parameters, while the registry names the current proof-kit modules, theorems, tactics, supporting declarations, expected postcondition shapes, and guidance sections.  This division lets compiler metadata remain stable while the proof library improves.

A recipe's applicability check must include the kind-specific structural matcher and every side condition that can be decided from the artifact.  Direct methods include a theorem whose program argument matches the region or a tactic that performs the same checked decomposition.  Indirect methods include representation lemmas, frame-preservation results, continuation combinators, arithmetic facts, and guidance that becomes relevant through a parent, child, predecessor, or successor region.

The planner should attempt recipes in a bounded order.  It should first apply an exact semantic theorem, then a registered composition theorem for adjacent or nested regions, then a registered tactic whose applicability check passed.  It should give Codex only the guidance associated with the residual regions and goals after those deterministic attempts.

Each attempt should record the region, recipe version, method, applicability result, Lean result, elapsed time, and resulting goal shape.  These records distinguish a missing theorem from an inapplicable theorem, an expensive tactic, and a guidance failure.  The records also support removal of recipes that increase total proof time despite succeeding locally.

| Region | Direct recipe | Indirect support | Focused guidance |
|---|---|---|---|
| Fixed-array length dispatch | `FixedArrayLengthDispatch.program_spec` or `wp_fixed_array_length_dispatch` | `UInt64Array.At.lengthRead`, `generatedLengthBound`, and `FixedArrayEqNode.branchPost` | Array representation, frames, memory, and branch continuation. |
| Search-key load | `FixedArrayEqNode.loadKeyProgram_spec` or `wp_fixed_array_search_key` | `UInt64Array.At.generatedElement` and `FixedArrayEqNode.keyFrame_get_key` | Array bounds and local-frame normalization. |
| Equality search node | `FixedArrayEqNode.program_spec`, `keyFirstProgram_spec`, or the corresponding `wp_fixed_array_*_eq_node` tactic | `branchFrame` facts and `branchPost` composition | Branch organization and result-region selection. |
| Fixed-array result | `FixedArrayPairResult` or `FixedArrayResult` semantic theorem selected by an exact result-region match | Allocation facts, store-preservation lemmas, and represented-array constructors | Allocation, memory writes, and final postcondition conversion. |
| Counted loop | A general counted-loop theorem selected by loop kind and parameters | Index arithmetic, frame invariants, accumulator updates, and call summaries | Invariant construction and termination measure. |

The registry should distinguish a general proof asset from an artifact-specific observation.  A residual goal recurring across at least two artifacts or compiler templates justifies an attempted general lemma or tactic, while one program's semantic branch belongs in its generated proof or focused guidance.  Proof-generation time determines whether an accepted generalization remains in the active recipe set.

## Iterative implementation plan

Development should proceed through narrow vertical slices rather than complete one subsystem before starting the next.  Every iteration must add compiler emission, sidecar serialization, independent validation, structural matching, recipe selection, proof planning, an end-to-end artifact proof, and a timing result for one new region family.  This order exposes interface mistakes and proof-time effects while the schema and emitter representation remain inexpensive to change.

Each iteration should finish the same eight tracks.  Compiler changes mark one semantic region during structured instruction emission, the CLI writes that annotation beside byte-identical WASM, and the consumer validates its artifact identity and exact instruction path.  The proof registry then selects direct and indirect methods, the planner produces Lean proof structure, `leanexegen` completes and independently checks the proof, and the timing record determines the next iteration.

| Track | Required result in every iteration |
|---|---|
| Compiler | Emit one additional versioned region kind from the lowering function that creates its instructions. |
| Artifact | Preserve WASM bytes and write a deterministic sidecar through `--annotations`. |
| Validator | Reject malformed metadata, stale artifact identity, invalid paths, and parameter mismatches. |
| Matcher | Confirm the reported region and parameters against the decoded instruction tree. |
| Recipes | Select direct theorems or tactics, indirect support, expected postconditions, and focused guidance. |
| Planner | Produce a deterministic Lean starter or helper proof for the matched region. |
| Proof | Complete and independently check the artifact theorem without source or compiler access. |
| Measurement | Compare total proof-generation time with the preceding method on frozen inputs. |

### Iteration 1: Direct calls

The first slice should annotate user-function calls in Demo 1, including calls nested in structured branches and compound expression emission.  The compiler should report a `leanexe.call.direct.v1` region with the caller function, callee index, argument locations, result locations, and continuation, then write it through the new CLI option.  This region is small enough to implement the complete path before general fragment annotations alter much of the emitter.

The consumer should match each call sequence against the decoded function and select `Wasm.wp_call_tw`.  A function with one top-level decoded call may also select `Project.ProofKit.Control.wp_entry_single_call`, while a branch-local call must retain its surrounding branch proof.  The indirect recipe should include the callee theorem requirement, caller-frame restoration, call guidance, and the relation between the call result and the enclosing postcondition.

The iteration ends with a controlled Demo 1 reproof and independent verification against the unchanged WASM.  The timing result may show little improvement because the wrapper occupies a small part of Demo 1's proof, but it will exercise the full compiler-to-proof path.  Any failure in sidecar association, path matching, recipe application, or proof isolation must block expansion to the next region kind.

### Iteration 2: Fixed-array entry and result

The second slice should cover fixed-array ABI entry, length dispatch, allocation, stores, and result return across Demos 2 and 3.  Compiler annotations should name array representation parameters, local roles, valid and invalid branches, allocator windows, result elements, and continuations.  The validator and matcher should confirm each nested region before selecting `FixedArrayLengthDispatch`, `FixedArrayAllocatorWindow`, `FixedArrayPairResult`, or `FixedArrayResult` methods.

The planner should compose the wrapper and result regions into one deterministic proof outline.  Codex should receive the remaining relationship between branch values and the formal specification, together with guidance selected for those residual goals.  The iteration ends with one screened run on each fixed artifact, followed by repeated trials only if the screened method finishes and improves the complete proof path.

### Iteration 3: Search branches and composition

The third slice should annotate search-key loads, checked element loads, equality comparisons in both operand orders, unsigned less-than decisions, branch roles, and continuation relationships.  Demo 2 supplies the linear association-list search, while Demo 3 supplies the binary-tree branch structure.  Their shared region kinds must retain different successor graphs without embedding either program's result function.

The recipe registry should attempt `FixedArrayEqNode` theorems and tactics directly, then apply registered branch-frame and continuation-composition lemmas indirectly.  Residual goals recurring in both demos justify a new general theorem or tactic, while one demo's leaf semantics remain in its generated proof.  The iteration measures whether a compiler-provided branch graph eliminates the composition delay observed after individual node tactics succeeded.

### Iteration 4: Loop structure and invariants

The fourth slice should return to Demo 1's computational helper and annotate its loop entry, induction locals, bound or exit conditions, updates, recursive or back-edge behavior, and continuation.  The first recipe should use the existing control-flow tactics, supporting arithmetic and frame lemmas, and a focused invariant guide derived from accepted loop proofs.  The planner should formulate the structural invariant skeleton while leaving the prime-factor relation as the application-specific obligation.

Later examples should exercise counted array folds, byte-array folds, range folds, and loop folds through the same vertical path.  Repeated invariant components should become general lemmas only after at least two artifacts expose the same goal shape.  Each added loop family receives its own end-to-end proof and timing result before another loop form enters the vocabulary.

### Iteration 5: Broader calls, ownership, and emitter integration

The fifth slice should extend calls beyond the simple wrapper and cover retain, release, and allocator-helper boundaries.  Annotations should report argument and result locations, ownership roles, runtime-function identities, and continuations, while matchers confirm the exact emitted templates.  The proof registry should compose callee and runtime theorems without reconstructing caller frames through unrestricted symbolic execution.

This iteration should also integrate the accumulated annotation representation with the structured module value planned in [Emitter Restructuring](emitter.md).  Module assembly, Talos translation, byte serialization, WAT rendering, and sidecar generation should consume one instruction tree.  Byte-identity and corpus checks must prevent the executable, proof model, and annotations from acquiring independent lowering implementations.

### Timing method across iterations

Hold the request, specification, source, WASM, model, Codex model, reasoning effort, runner limits, proof kit, and task timeout fixed for each comparison.  Count the complete artifact-proof stage, including Codex activity and independent outer Lean acceptance, as proof-generation time.  Use one run per demo to screen an iteration, then run two more unchanged trials when the screened method finishes and warrants further evaluation.

Every applicable iteration should retain four configurations: current WAT analysis, annotations alone, annotations with direct recipes, and the full registry with indirect support and focused guidance.  Report the per-demo median, range, failures, and timeout-censored attempts, without excluding failures or pooling raw times from different demos.  The configuration split identifies whether structural metadata, theorem selection, or proof guidance produced the measured change.

The current unannotated reference points are 372.474 seconds for Demo 1, 512.533 seconds for Demo 2, and 278.656 seconds for Demo 3.  Demo 3's repeated pair-result runs varied from 278.656 to 1,243.846 seconds, so one favorable run does not establish a reliable time effect.  Each comparison reports the per-demo median proof-generation time and worst per-demo ratio alongside retrieval, revisions, proof structure, shared abstraction use, compiler-derived evidence use, and applicability.

The future compiler-verification theorem may use region boundaries to organize lowering lemmas, but the sidecar does not constitute that theorem or a source certificate.  Artifact proofs continue to use annotations without trusting the compiler, while compiler verification may later prove that a region kind implements its corresponding IR operation.  The two uses share the region vocabulary and structured emitter without sharing a trust assumption.

## Implemented iterations and evidence

The compiler now emits `leanexe.call.direct.v1`, `leanexe.array.length-dispatch.v1`, `leanexe.array.search-key.v1`, `leanexe.array.eq-node.v1`, `leanexe.array.lt-node.v1`, `leanexe.array.pair-result.v1`, `leanexe.array.map-add.v1`, and `leanexe.array.filter-lt.v1` regions through `lean-wasm compile --annotations`.  Annotated emission remains the canonical instruction-emission path, and each corpus migration requires the recompiled bytes to equal the frozen WASM before accepting a sidecar.  The JavaScript consumer checks the structured location, exact top-level instruction sequence, checked-loader branches, Boolean-normalization branches, local window, operand order, branch roles, and continuation before selecting a proof recipe.

Package schema 5 retains `program.annotations.json` and `proof-recipes.json` under the package manifest's file digests.  `leanexegen annotate` converts an older package by recompiling its frozen Source, requiring byte-for-byte equality with the frozen WASM, matching the new sidecar against the frozen Program, and writing a separate annotated package.  A subsequent `reprove` regenerates recipes from the frozen annotations and omits Source and the compiler from the proof task.

Pair-result regions receive an additional checked module under the artifact's generated namespace.  Each theorem resolves the annotation's structured path and half-open interval through `Project.ProofKit.Annotation.region`, then proves by `rfl` that the resulting decoded program equals `FixedArrayPairResult.constResultProgram` or `inputResultProgram` with the reported values, input index, and destination local.  The proving agent receives the theorem name in the recipe, and independent package verification rebuilds the same equality from the frozen Program.

The direct-call slice found two Demo 1 calls and selected `Wasm.wp_call_tw`, with `wp_entry_single_call` available for a single top-level call.  Its first annotated reproof took 279.110 seconds, compared with 372.474 seconds for the retained reference, but both sessions produced the same 532-line Behavior source.  The single timing difference does not establish a causal improvement.

The length-dispatch slice covers both emitted encodings: normalized equality in Demo 1 and normalized inequality in Demos 2 and 3.  `FixedArrayLengthDispatch.eqProgram_spec`, `program_spec`, `wp_fixed_array_length_eq_dispatch`, and `wp_fixed_array_length_dispatch` prove the length read, encoding, Boolean normalization, branch choice, and enclosing continuation.  The compiler originally searched for `eqzI64`, while the internal emitter uses `eqzI32`; exact comparison with the emitted instruction type found and corrected that recognizer defect.

The length recipes shortened the accepted proofs but increased total proving time.  Demo 1 fell from 532 to 517 lines while Stage 5 rose from 372.474 to 637.770 seconds.  Demo 2 fell from 900 to 508 lines while Stage 5 rose from 512.533 to 1,387.816 seconds.  These results show distinct structural and timing effects that the current scorecard preserves separately.

The search slice adds a checked key load, equality nodes in both operand orders, and key-first unsigned less-than nodes.  `FixedArrayEqNode.SearchFrame` records the input, local shape, empty stack, and saved key; `afterLoad` and `branch` preserve those facts; `branchN` and `FixedArraySearch.pairPost_branchN_conseq` represent nested continuations.  `FixedArrayLtNode.program_spec` and `wp_fixed_array_lt_node` extend the same frame across a checked indexed load and expose the semantic ordering branches.

The recipe planner sorts regions by structured instruction location, producing depth-first program order instead of compiler-kind order.  Demo 3 now receives length and key-load recipes followed by equality and less-than recipes interleaved at indices 1, 3, 7, 9, 5, 11, and 13.  Exact matching rejects a malformed less-than comparison, an incorrect operand order, a changed checked-loader branch, or a changed Boolean-normalization branch.

Optional search recipes did not improve the first Demo 3 screen.  The accepted proof ignored them, retained the 672-line reference proof with one added blank line, and took 392.544 seconds instead of 278.656 seconds.  An experimental deterministic starter applied a partial structural outline and reduced the proof to 604 lines, but Stage 5 rose to 1,221.892 seconds; leanexegen no longer emits that starter behavior.

The current compiler was run from scratch over the retained Demo 1, Demo 2, and Demo 3 Sources.  Each run reproduced its frozen WASM digest, matched every sidecar region against the decoded Program, and passed independent package verification under the managed Lean runner.  The accepted region counts appear below.

| Demo | Frozen WASM SHA-256 | Matched regions |
|---|---|---|
| 1 | `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7` | One length dispatch and two direct calls. |
| 2 | `ceb37cd3d61158e7f4162c97cac9b79022518a4e67f895d45a3619c7b5a29712` | One length dispatch, one search-key load, ten equality nodes, and twelve pair results. |
| 3 | `1a93ec55974666ad54fad73d321b8b9e1f7d67970b272c13bcc77055c8e7631d` | One length dispatch, one search-key load, seven equality nodes, three less-than nodes, and twelve pair results. |

Cross-demo validation exposed an overbroad search-key recognizer: Demo 1's ordinary load of its single input initially matched the loader shape.  The compiler now requires a search-key candidate's local window and saved local to match an equality or less-than consumer in the same function, removing the Demo 1 false classification while preserving Demos 2 and 3.  The proof consumer still treats this classification as untrusted guidance and checks every selected instruction region independently.

A fresh Demo 3 reproof with the complete tree recipe set could not start because headless Codex reported an account usage limit until August 10, 2026.  Two attempts failed before proof generation or Lean execution, so they provide no timing result.  The package, annotation, recipe, proof-kit, and independent theorem checks completed without that service.

The next slice should compose the checked entry, search, and pair-result boundaries into one artifact-specific structural theorem.  Its generated proof should follow the complete branch tree and leave only equations relating comparison facts to `FormalSpec.expected`, avoiding the partial starter's requirement that Codex reconstruct the remaining continuations.  Demos 2 and 3 will screen this composition independently before any similar generator handles loops.

A later journaled Demo 3 run used the shared search-frame and pair-result declarations throughout its accepted 421-line proof.  The proof was 251 lines shorter than the 672-line pair-result reference, but Stage 5 increased from 278.656 to 770.948 seconds.  The journal attributes two failed builds to unstable tactic premises and records about seven minutes spent reconstructing the annotated tree's continuation graph before writing the first complete body.

The proof kit now provides explicit-premise forms for the search-key and less-than tactics.  These forms remove numeric key-local goals and bind the less-than frame, input, and index facts before either subtree, and a transformed 403-line proof builds through `ArtifactResult`.  This change removes two recorded failure modes while retaining the complete tree-composition step as the larger target.

The composition experiment requires a Lean theorem whose statement contains the exact checked branch graph and one equation between the public expected result and the graph's semantic lookup function.  The generated theorem may depend on `AnnotationMatches`, `SearchFrame`, `PairResultContext`, and the registered node theorems, while its program equality must follow from the frozen decoded artifact.  A Demo 3 timing screen will determine whether moving graph reconstruction out of the Codex session reduces total proof-generation time.  Demo 2's linear search needs a different composition descriptor.

The first composition theorem now exists as `FixedArraySearchTree.Tree.program_spec`.  A generic `Tree` descriptor determines the exact equality, less-than, found-result, and missing-result program and defines the corresponding array lookup semantics.  Its proof composes the existing node and pair-result theorems by induction without importing a generated program or formal specification.

Demo 3's complete seven-node search program is definitionally equal to one descriptor after the checked search-key load.  The annotation consumer now derives that descriptor from the parent-child paths, emits an `rfl` region equality in `AnnotationMatches`, and names the descriptor, equality, and composition theorem in `PROOF_RECIPES.json`.  A transformed 155-line proof using the generated descriptor builds through `ArtifactResult`, leaving a fresh Codex run to measure the complete proof time.

Three fresh composition runs produced the same 144-line proof and completed Stage 5 in 405.385, 326.320, and 303.478 seconds, giving a 326.320-second median.  The preceding journal-guided node proof took 770.948 seconds and 421 lines, while the historical pair-result reference took 278.656 seconds and 672 lines.  Every journal confirms that the agent selected the composition first and passed its first build after one proof edit, establishing a stable proof method while leaving headless-agent latency as the largest remaining cost.

Those three journals also show that Codex reconstructed the same outer proof around the tree: fixed-length dispatch, invalid pair allocation, saved-key load, search-frame construction, and public return.  `Tree.wrapperProgram_spec` now proves that composition generically, and the recipe planner recognizes the complete decoded wrapper only when the annotated branches cover the function body through its final result-local read.  A version-two composition causes the deterministic starter to apply this theorem and leave three semantic goals concerning invalid input, descriptor validity, and agreement with the formal result; a fresh timing run must determine whether this reduction lowers total proof-generation time.

The first version-two run completed Stage 5 in 253.644 seconds, including 215.383 seconds in Codex and 29.284 seconds in outer acceptance, and independent package verification succeeded.  Its 76-line proof preserved the 7,186-byte artifact and exact digest, reducing time by 22.3 percent from the 326.320-second composition median and by 9.0 percent from the 278.656-second historical pair-result result.  The journal records one avoidable failed build caused by removing the starter's three elaboration holes, so later runs must test a complete semantic starter before treating this single timing result as representative.

The complete semantic starter now supplies those three simplification proofs and fixes all wrapper parameters by name.  Its focused Demo 3 copy builds through `ArtifactResult`, and its import set contains only the generated specification, decoded Program, checked annotation module, and `FixedArraySearchTree`.  The proof prompt instructs Codex to leave a starter unchanged when the initial check succeeds, record that result in the journal, and perform the required final check.

Three complete-starter runs finished Stage 5 in 109.607, 121.976, and 131.413 seconds, giving a 121.976-second median and a 21.806-second range.  Every journal reports that the initial build succeeded and that Codex left the same 77-line candidate unchanged; the accepted source had SHA-256 `18c1d84f94723f6db76d5ad701c951472fcc80c5c76acade4d91f558d9f4ee2a`, and independent verification accepted the first package.  The median is 62.6 percent below the 326.320-second complete-tree median and 56.2 percent below the 278.656-second historical pair-result result.

Demo 2's journals expose the same wrapper around a different search graph: ten loaded-first equality nodes form a linear first-match chain.  `FixedArraySearch.wrapperProgram_spec` now contains the wrapper proof shared by tree and chain descriptors, while `FixedArraySearchChain.Chain.program_spec` proves an arbitrary equality chain by induction.  The annotation planner derives a version-two chain composition from exact nested unequal branches and result regions; the generic module and JavaScript tests pass, while a fresh Demo 2 proof-time result remains pending.

The first fresh chain run stopped while compiling generated annotation support because the ten-node descriptor equality exceeded Lean's default recursion depth.  Generated `AnnotationMatches` modules now use the same `maxRecDepth 1048576` setting as behavior proofs, allowing Lean to elaborate the exact nested descriptor and `rfl` region equality.  The interrupted run reached no artifact-behavior candidate and supplies no timing result.

Three corrected Demo 2 chain runs finished Stage 5 in 110.332, 110.165, and 110.711 seconds, giving a 110.332-second median and a 0.547-second range.  Every initial build succeeded, Codex made no proof edit, and each package contained the same 76-line proof with SHA-256 `7f47dc8d68291f4e3c08b565478119cfa1b33f230cb4a0ffc572a8cc08f60f2c`; independent verification accepted the first package.  The median is 78.5 percent below the 512.488-second journal-derived reference, and the proof is 81.3 percent shorter than that reference's 406 lines.

Those three journals also report two identical in-session builds despite making no candidate edit.  The proof prompt now returns after the successful initial check and journal update in that case, leaving the existing outer-acceptance build as the independent final check.  Proofs that require a candidate edit retain the required post-edit build before Codex returns.

Three runs under the single-check prompt finished Stage 5 in 107.144, 114.390, and 124.539 seconds, giving a 114.390-second median and a 17.395-second range.  Each journal records one successful in-session check, no proof edit, and no repeated in-session check; outer acceptance rebuilt the unchanged proof independently.  The median is 4.058 seconds above the preceding 110.332-second result, so removing the redundant incremental check produced no measured reduction in total Stage 5 time.

### Held-out loop baseline

Demo 4 froze a bounded `Array UInt64` map before any loop-oriented annotation or proof-kit change.  Its 1,913-byte artifact has SHA-256 digest `c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff` and contains one reachable 456-instruction function with 16 locals and three loops.  The compiler emitted no regions for that function, leaving both `compositions` and `recipes` empty in the checked proof plan.

The baseline artifact proof took 2,364.735 seconds, including 2,255.687 seconds in Codex and 98.593 seconds in independent outer acceptance.  Its accepted 457-line source has SHA-256 digest `6bd050aab0f4e1124e9ed2a2ef6e75a6020e7ab7b90ce82d2315dc0668b08488`.  The journal records 27 edited checks and a complete proof of bounded-length dispatch, dynamic capacity calculation, result allocation, a transformed-prefix map loop, wrapping payload stores, and empty-array allocation.

The journal identifies five candidate reusable boundaries.  A bounded-length dispatch theorem should expose the semantic size cases, a dynamic capacity theorem should normalize the emitted allocation expression, and the allocator-window theorem should accept unused trailing locals.  A dynamic length-store theorem and a parameterized word-map loop theorem should cover the remaining repeated instruction and invariant work before a complete wrapper composition is attempted.

## 2026-08-07: Demo 4 allocator-window iteration

`FixedArrayAllocatorWindow.region_spec_withTail` generalizes the allocator theorem from exactly `offset + 14` internal locals to `offset + 14 + tail` locals.  Its compatibility theorem retains the former exact-frame statement, and both the defining module and its downstream pair-result module build under Lean 4.31.0.  The proof prompt and catalog now direct the agent to select the generalized theorem before symbolic execution when an allocator has unused trailing locals.

A controlled reproof preserved Demo 4's formal specification, source, 1,913-byte WASM artifact, decoded Program, and artifact theorem.  Stage 5 fell from 2,364.735 seconds to 1,191.695 seconds, a 49.6 percent reduction, while the number of journaled edited checks fell from 27 to 19.  The generated proof applies the shared allocator theorem at offset two with no tail and at offset zero with a tail of two.

The controlled journal attributes the remaining work to three compiler templates.  Ten checks handled the unsigned bounded-length dispatch, capacity normalization, and entry into the successful allocator, while seven more handled the array-map loop after allocation.  The next iteration will add checked annotations and generic theorems for those templates, then reprove this same frozen artifact before screening the shared changes on the earlier demos.

## 2026-08-07: Bounded-length dispatch

`FixedArrayLengthDispatch.leProgram_spec` proves the direct unsigned upper-bound encoding used by Demo 4.  Its tactic converts the emitted pointer save, length load, `leUI64`, and branch into semantic premises for `input.size ≤ maximumSize` and its negation.  The existing equality and normalized-inequality theorems remain unchanged.

The compiler emits `le-unsigned-v1` through the existing fixed-array length-dispatch region kind when its IR condition compares an input array's size with a constant upper bound.  The JavaScript consumer validates the exact eight-instruction decoded prefix before selecting `leProgram_spec` and `wp_fixed_array_length_le_dispatch`.  Unit tests reject a changed bound or comparison opcode and accept all three length-dispatch encodings.

Annotating the frozen Demo 4 package recompiled the source to the same WASM digest and produced one bounded-length region at top-level instructions zero through eight.  Its checked recipe names input local five, maximum size eight, the valid then branch, and the invalid else branch.  The proof-kit module, compiler emitter, consumer tests, and byte-identity annotation run all pass under the repository toolchain.

## Bounded map composition

The held-out Demo 4 journal identified the complete bounded map wrapper as the remaining proof boundary after the allocator-window and length-dispatch increments.  `Project.ProofKit.FixedArrayMapAdd.wrapperProgram_spec` now proves the canonical wrapper for arbitrary `maximumSize`, wrapping `UInt64` `addend`, input contents, heap position, allocation count, and memory size.  The checked proof contains the dynamic capacity arithmetic, both allocator continuations, result-length store, transformed-prefix loop invariant, wrapping payload stores, and empty-result construction.

The compiler recognizes the exact extracted IR form `if input.size ≤ n then input.map (fun element ⇒ element + c) else #[]`.  It emits one `leanexe.array.map-add.v1` whole-function region containing `n`, `c`, and the function-return continuation while retaining the nested length-dispatch region.  The consumer verifies that the region covers the decoded top-level function and generates an `AnnotationMatches` equality between the selected artifact region and `FixedArrayMapAdd.wrapperProgram n c`; Lean accepted that equality for the frozen Demo 4 artifact.

The proof planner selects `wrapperProgram_spec` from that equality and generates a complete artifact-behavior starter.  Three controlled `leanexegen reprove` runs accepted the unchanged 66-line starter on their first checks and completed Stage 5 in 103.123, 144.173, and 109.165 seconds, giving a 109.165-second median and a 41.050-second range.  The median reduces total time by 95.4 percent from the 2,364.735-second held-out baseline and by 90.8 percent from the 1,191.695-second allocator iteration.

All three packages retain the same 1,913-byte WASM artifact and SHA-256 digest `c538d40936b426ba875b3dae1913e62ff00a44b34adff2adcd70922e5a4c95ff`.  Their proof sources have SHA-256 digest `bf07793985539b6c0a7e9076c97f836050c859b47b13ab3f70a3383270b29d56`, and every journal records no proof edit or repeated in-session check.  Independent `leanexegen verify` runs accepted each packaged specification, decoded artifact, annotation equality, behavior theorem, and final artifact theorem.

## Bounded filter composition

The held-out Demo 5 baseline left the complete stable-filter loop outside the annotation vocabulary.  Its length-dispatch recipe did not cover input-sized capacity allocation, the value-dependent output counter, the retained and rejected predicate branches, the final length store, or the empty-result allocation.  Codex needed fourteen edited Lean checks and 1,635.679 seconds to prove those boundaries for one artifact.

`Project.ProofKit.FixedArrayFilterLt.wrapperProgram_spec` now proves the canonical wrapper `if input.size ≤ maximumSize then input.filter (fun element ⇒ element < threshold) else #[]` for arbitrary bounds and unsigned thresholds.  Its checked program contains the exact allocator window and filter loop emitted by LeanExe, while its invariant represents the output payload as the filtered processed prefix.  The theorem uses `FixedArrayFilterLt.heapReserveBytes` to account for input-sized reserved capacity even when the final filtered result is smaller.

The compiler recognizes the exact extracted `arrayFilterSlots` form and emits a `leanexe.array.filter-lt.v1` whole-function region containing `maximumSize`, `threshold`, and the function-return continuation.  The consumer validates the complete top-level boundary and generates a Lean equality between the decoded artifact region and `FixedArrayFilterLt.wrapperProgram maximumSize threshold`.  The deterministic starter checks equality with both the formal result and the schema-6 heap reserve before applying `wrapperProgram_spec`.

Recompiling the frozen Demo 5 source produced the same 1,975-byte WASM digest and added the filter region beside the existing length dispatch.  Three controlled reproofs preserved every frozen source and artifact input, accepted the unchanged 70-line starter on each first check, and completed Stage 5 in 86.795, 90.745, and 95.718 seconds.  Their 90.745-second median reduces the measured baseline by 1,544.934 seconds, or 94.5 percent, while their range is 8.923 seconds and independent verification accepted the first and third final packages.

## Fixed-array fold annotations

The compiler emits `leanexe.array.fold.v1` for a direct fixed-array fold assignment and for a fold used as an array-literal slot value.  The annotation records the source and result widths, traversal direction, array and bound expressions, accumulator and element locals, initial and next values, body lets, done expression, release offsets, scratch layout, and selected result placement.  Its structured instruction path permits the fold to remain nested inside a length branch and result allocation.

The consumer checks the scratch-local equations and rejects inconsistent widths, result slots, release offsets, and continuations.  It resolves the region in the decoded Talos `Program`, then checks the emitted initialization locals, effective bound, loop guard, staged accumulator copies, done branch, forward or reverse back edge, and result-local transfer.  The generated `AnnotationMatches` equality independently fixes the complete selected instruction interval used by the artifact proof.

Demo 9 supplies the first fixed artifact for this region kind.  Recompilation preserved the 1,979-byte WASM digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5` and added a fold region at instructions 39 through 65 of the valid branch selected by top-level instruction seven.  The generated `AnnotationMatches` module names that complete interval as a `Wasm.Program` and proves by reduction that the structured path selects it, while the recipe names the equality and the three generic `ArrayFold.foldPrefix` declarations.

The controlled fixed-artifact reproof completed Stage 5 in 3,188.251 seconds and produced a 416-line proof.  The baseline took 3,431.870 seconds and 493 lines, giving a 7.1-percent time reduction and a 77-line reduction, while the earlier fold-prefix run took 4,055.765 seconds and 475 lines.  Independent verification accepted the same 1,979-byte WASM artifact, the generated fold-region equality, the behavior theorem, and the final artifact theorem.

The journal shows that annotation-driven retrieval selected the fold-prefix, length-dispatch, allocation, and array-memory entries and rejected structurally unrelated entries.  The `_from hArray` dispatch tactic and opt-in allocator list tactics resolved concrete inference and local-list failures, but two broad simplification calls exhausted one million heartbeats before the proof adopted named post-allocation frames.  The agent then used the annotated accumulator, item, index, and effective-stop roles to state the prefix-fold invariant, leaving the application transition, memory bounds, and result representation as ordinary Lean obligations.

The fold matcher now recognizes the exact forward, one-word continuing prefix formed by the unsigned stop guard and generated element-address load.  `AnnotationMatches` names the nested 16-instruction prefix as `FixedArrayTraversalInput.continuingProgram` and proves that equality by reduction, while `continuingProgram_spec` discharges the guard, address normalization, memory read, and item-local update for an arbitrary continuation.  Independent package verification accepted this equality against Demo 9's unchanged artifact.

### Traversal-prefix screen

The controlled reproof selected `fixed-array-traversal-input` through the structured LTG indexes and applied the generated continuing-region equality with `FixedArrayTraversalInput.continuingProgram_spec`.  The theorem discharged every guard, indexed-address, bounds, represented-element read, and item-local premise.  The agent then proved the wrapping accumulator update, fold-prefix successor equation, unchanged-local facts, encoded successor, and strict measure decrease.

The run produced no accepted proof after approximately 4,285 seconds, exceeding the retained 3,188.251-second annotated run by about 1,097 seconds.  Its journal and candidate stopped changing for about twenty-two minutes while the completed loop branch and singleton result remained unfinished, so the owned session was interrupted and recorded as a censored lower bound.  The checked traversal theorem therefore has direct structural evidence but no proof-time benefit from this observation.

The residual concentrates on the fold-exit guard, payload store, result-pointer transfer, and singleton representation.  The run also showed that concrete local-list getter facts must precede broad simplification of the dependent loop continuation, and that reverse-oriented `UInt64.ofNat_add` or `toUInt32` addition equations create simplifier cycles.  Inspection found existing generic checked support in `FixedArrayResult.payloadStore_spec` and `singletonStore_at`, but structured LTG had no entry that a proving agent could retrieve through its recorded result-store queries.  The new `fixed-array-result` entry exposes those declarations and gives a completed fold a three-part boundary: prefix completion, emitted payload-store execution, and output representation.

The next controlled reproof found `fixed-array-result` on its first LTG query and produced an independently verified 678-line artifact proof.  The proof applies `lengthStore_spec` twice, `payloadStore_spec` once, `singletonStore_at` once, and `FixedArrayTraversalInput.continuingProgram_spec` once.  Stage 5 took 3,149.420 seconds, but the journal records two broad dependency-repository searches whose path results included external artifact proofs, so this run supplies capability evidence and no timing evidence.

The journal identifies three remaining general boundaries.  The advertised length-dispatch invocation used the inference-sensitive tactic before the agent switched to its `_from hArray` variant, the fold setup required manual input-length loads and effective-stop selection, and the successor frame required direct proofs over seven local-list updates after broad simplification exceeded its resource limits.  The recipe now advertises the `_from` tactic, while the checked result entry adds `emptyStore_at` for the invalid branch; fold setup and successor-frame composition remain the next annotation-theorem work.

The search violation also exposed an isolation defect in the proof task.  Artifact-proof workspaces now mirror every allowed `Project.ProofKit` source under `PROOF_KIT_SOURCE/`, and the prompt restricts proof-kit searches to that bounded tree.  The mirror lets an agent inspect selected declarations without searching dependency checkouts that contain demos, benchmarks, and archived proofs.

The fold matcher now checks two additional subregions against generic programs.  A forward, one-word, one-accumulator fold over the complete input array receives `<region>_setup_eq`, which identifies the 23-instruction setup as `FixedArrayFold.forwardSetupProgram`; a single selected result slot receives `<region>_result_eq`, which identifies its two-instruction accumulator transfer as `FixedArrayFold.resultProgram`.  Both equalities reduce against the decoded Demo 9 artifact in the generated `AnnotationMatches` module.

`forwardSetupProgram_spec` executes both represented-length loads, all loop-local initialization, and the effective-stop selection before passing `forwardSetupFrame` to an arbitrary continuation.  `resultProgram_spec` copies the completed accumulator to its selected result local and passes `resultFrame` to an arbitrary continuation.  These theorems depend on the matched compiler shape and array representation while leaving the fold step, invariant, measure, and public output specification to separate proofs.

An annotation-only rebuild accepted the unchanged 1,979-byte Demo 9 artifact and checked both new subregion equalities in Lean.  Independent package verification then accepted those equalities, the retained behavior theorem, and the artifact theorem under the expanded proof kit.  These checks established the input to a controlled fixed-artifact reproof.

The controlled reproof selected `fixed-array-fold-structure` and applied `forwardSetupProgram_spec`, `continuingProgram_spec`, and `resultProgram_spec` in its first Codex session.  Stage 5 completed in 2,082.889 seconds, compared with 3,188.251 seconds for the preceding retained run, a reduction of 1,105.362 seconds or 34.7 percent.  The proof grew from 416 to 508 lines because it stated two capacity-prefix theorems locally and used explicit shared-theorem applications at the recognized boundaries.

The journal exposed two repeated representation gaps after the new fold boundaries succeeded.  `FixedArrayCapacity.constantProgram_spec` now proves the compiler's constant result-length capacity calculation for arbitrary length, stride, destination local, frame, and continuation, while `Frame.internal_getElem?_of_get` and `internal_getElem_of_get` convert combined-local invariants into internal-list facts.  Both declarations are indexed in structured LTG with evidence from Demos 2, 3, 5, and 9.

The length-dispatch consumer now scans each decoded valid and invalid branch for the complete constant-capacity prefix.  A match produces branch-specific `AnnotationMatches` equalities and adds the capacity theorem, normalized value, and post-prefix frame to the length recipe, while any changed arithmetic instruction removes support for that branch.  A fresh Demo 9 package checked equalities for lengths one and zero against the unchanged artifact and passed independent verification.

## Scalar-loop annotations

The compiler now emits `leanexe.loop.while.v1` for every extracted `Stmt.while` region and `leanexe.loop.fold.v1` for a top-level `loopFoldMultiSlotAssign`.  A while annotation contains the IR condition, IR body statement, scratch-local start, structured instruction location, continuation, and generator chain.  A loop-fold annotation adds accumulator locals, initial and staged next-state expressions, body lets, done expression, release offsets, staging locals, and result targets.

The consumer validates each structured location against the frozen decoded Program before retaining its recipe.  A while region must resolve to one block containing one loop with an exit branch and back edge, while a loop-fold region must also match its accumulator copies, scratch layout, done test, and result copies.  The IR expressions remain untrusted guidance because the artifact matcher checks the emitted control boundary rather than reconstructing the compiler's expression-lowering proof.

Recompiling Demo 1's frozen source produced the same 1,938-byte artifact and SHA-256 digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`.  Function zero now carries one while region at top-level instruction interval two through three, with scratch locals beginning at 18 and a complete IR statement for the trial-division branches.  The initial proof plan selected `Wasm.wp_loop_cons`, `wp_block_loop`, `wp_entry_to_loop`, and the loop, frame, and arithmetic guidance sections, establishing the control-flow annotation tested by the later reproofs.

The first controlled invocation completed Stage 5 in 276.795 seconds and passed independent package verification, but its journal records that Codex found the retained singleton-3 proof in the repository and copied it.  The accepted 532-line source is byte-identical to that prior proof, with SHA-256 digest `ddce88feccb5b074bf8951189dd5f538ed286201cbe2c0d96d229e61815f38a1`.  This result constitutes a censored benchmark-integrity failure rather than evidence that the loop annotation reduced proof time.

Artifact-proof tasks now prohibit reading demos, benchmarks, archived packages, or proofs from another generated namespace.  The task may still read dependency source when it needs to confirm a declaration named by the supplied proof-kit catalog or strategy guide.  The next Demo 1 run must produce its proof from the frozen task context, generic proof assets, and checked annotations before entering a timing comparison.

The isolated replacement ran for approximately 1,082 seconds without producing an accepted proof or a Lean diagnostic, after which the owned Codex process was interrupted.  This censored observation exceeds the 680.396-second slowest retained singleton run and the plan's 900-second scalar-loop threshold.  The annotation-only recipe therefore fails promotion and will not receive repeat trials.

This result motivated a checked artifact-specific transition map computed before the proving session.  The generic scalar statement descriptor represents local reads, constants, unsigned arithmetic, conditions, assignments, sequences, and branches, while its proof theorem establishes the emitted Talos weakest-precondition transition for any matching descriptor.  Generated `AnnotationMatches` code now proves both that Demo 1's exact loop body equals the descriptor program and that its compact fixed-frame transitions agree with the descriptor evaluator.

### Checked scalar-loop descriptors

`LeanExe.Wasm.ScalarDescriptor` now reifies a typed subset of compiler IR containing `UInt64` local reads and constants, wrapping arithmetic, checked unsigned division and remainder, bit operations, shifts, comparisons, Boolean operations, scalar conditionals, assignments, sequences, and statement conditionals.  Successful reification selects the descriptor emitter in the production expression, condition, and statement entry points, while unsupported IR continues through the existing emitter.  `LeanExe.Wasm.ScalarCertificate` proves that each successful reification produces the descriptor instruction sequence, including the complete block-wrapped while form.

The while annotation carries descriptor version one and an optional structured descriptor.  The JavaScript consumer validates every tag, field, local index, operation, and decimal `UInt64` constant before producing a proof recipe.  A missing descriptor retains the older control-flow recipe, while a validated descriptor selects `Project.ProofKit.ScalarTransition.whileProgram_spec` and names the generated program and exact region equality.

The generated `AnnotationMatches` module translates the descriptor into the neutral artifact-side type and proves by reduction that the frozen decoded instruction interval equals its `whileProgram`.  The retained artifact proof imports this neutral module and the proof kit, without importing compiler IR, the emitter, or `ScalarCertificate`.  The compiler theorem checks annotation production, while the decoded-region equality remains the authority used by the artifact theorem.

The complete package path passed on the current array-wrapper Demo 1.  `tools/leanexegen annotate` recompiled its frozen Source to the same 1,938-byte artifact with SHA-256 digest `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7`, emitted an `and` guard and conditional statement descriptor for function zero, and built the generated equality over top-level interval two through three.  Independent `tools/leanexegen verify` then accepted the annotated package, while a separate check reproduced the original 1,348-byte scalar walkthrough artifact and proved the corresponding equality against a freshly generated Talos model.

The checked descriptor removes instruction decoding, branch reconstruction, checked-divisor expansion, assignment ordering, and scratch-local preservation from the proving task.  The remaining Demo 1 work consists of the trial-division invariant, its preservation through the descriptor evaluator, measure decrease, and the terminal prime-factor equation.  Fixed-artifact proof-generation trials later showed that raw descriptor evaluation was too expensive and that compact transition equations improved the matched result.

The first Codex 0.147.0 trial found that the complete current annotation package increases proof time.  The unannotated package completed Stage 5 in 2,017.931 seconds, while the annotated package completed in 3,692.913 seconds, and independent verification accepted both results.  The annotated package also supplied length-dispatch and direct-call recipes, and its journal records many wrapper-proof iterations, so a scalar-only package must separate the loop theorem's effect before the result can direct its replacement.

Scalar descriptors now compute read sets, explicit statement write sets, and scratch width.  `ScalarTransition.Stmt.eval_preserves_below` proves that evaluating a statement preserves each application local below the scratch boundary that the write set excludes, and the generated loop recipe names this theorem.  This effect certificate applies to scalar loops with untouched frame locals, while Demo 1's dense write set required fixed-frame branch equations that summarize scratch staging.

Selective annotation packages now support causal recipe tests.  `leanexegen annotate --only-region` validates the complete sidecar first, retains the named semantic region and mandatory direct-call coverage, then generates `AnnotationMatches` and proof recipes from that subset.  The verified Demo 1 control and candidate contain identical call recipes and differ only by `function-0.while-loop-0`, excluding the length-dispatch recipe that affected the first comparison.

### Isolated scalar-descriptor result

The calls-only control completed Stage 5 in 2,645.818 seconds, including 2,558.659 seconds in Codex and 75.772 seconds in outer acceptance.  Adding only the scalar-loop region increased Stage 5 to 3,894.697 seconds, including 3,811.538 seconds in Codex and 73.440 seconds in outer acceptance.  Both packages contain the same 1,938-byte WASM digest and passed independent `leanexegen verify` checks.

The candidate applies the generated descriptor equality and `ScalarTransition.whileProgram_spec` throughout function zero, but does not use `Stmt.eval_preserves_below`.  Its proof fell from 722 to 674 lines and from 3,418 to 3,257 whitespace-delimited words, providing secondary evidence that the descriptor removes some local proof structure.  Its 47.202-percent proving-time regression rejects the current scalar recipe despite that structural improvement; raw source bytes and identifier length do not enter the proof-complexity comparison.

The control journal shows that Codex reconstructed the neutral descriptor during its first few edited checks, after which both runs faced the same number-theoretic invariant, scalar evaluator cases, local-index conversions, and fixed-width arithmetic.  The candidate journal also records repeated work on the public singleton wrapper and explicit allocator-entry frame.  Those observations determined the next two additions: a shared singleton-wrapper composition and checked fixed-frame branch transitions that summarize scratch staging.

The shared wrapper composition is now implemented.  `FixedArraySingletonWrapper.wrapperProgram_spec` parameterizes the scalar callee and proves the complete public singleton-array boundary, while `AnnotationMatches` supplies a whole-function equality to the exact decoded entry program.  A production `leanexegen annotate` run preserved Demo 1's 1,938-byte artifact digest and built that equality by `rfl`.

The proof recipe records the wrapper as a complete composition, and the deterministic starter reaches its weakest-precondition boundary before free-form proof generation begins.  A structural matcher checks the one-parameter, fourteen-local layout, canonical length normalization, checked singleton load, direct-call placement, allocator boundary, result suffix, and public result local before generating the equality.  Lean remains authoritative for the complete match, so an omitted or changed nested instruction makes the generated equality fail rather than becoming a proof assumption.

### Checked scalar transition equations

`Project.ProofKit.ScalarTransitionU64` evaluates the descriptor over lists of `UInt64` and proves generic correspondence with the typed `ScalarTransition.State` evaluator.  The annotation consumer symbolically computes a fixed-frame condition transition and body transition, then proves both equations before the proving session begins.  The public equations lift the compact results to the state type consumed by `whileProgram_spec`, so the application proof can rewrite one loop step without reducing intermediate scratch-local writes or `Wasm.Value` conversions.

The generator propagates constant Boolean words and retains only semantic control branches.  Demo 1's nested Boolean normalization reduces to five body branches: the small remainder, trial-bound success, divisor found, candidate two, and later-candidate cases.  Two shared `UInt64` zero-or-one comparison facts and a restricted simplifier set check these branches without unfolding fixed-width equality internals.

The production annotation command rebuilt the exact Demo 1 artifact digest, generated the transition equations, and completed independent package verification.  The proof recipe names the lifted condition and body equations and instructs the proving agent to rewrite with them before reducing either descriptor evaluator.  The matched control retained length dispatch, mandatory direct calls, and the complete singleton wrapper but omitted the scalar-loop region, while the candidate added only that region.

The control completed Stage 5 in 2,262.084 seconds, while the candidate completed in 1,965.454 seconds.  The checked transitions reduced proving time by 296.630 seconds, or 13.113 percent, and independent `leanexegen verify` accepted both packages.  The candidate's Codex interval fell by 323.088 seconds, while its outer acceptance took 26.755 seconds longer.

The candidate rewrites with the generated condition equation three times and the body equation five times.  Its accepted proof uses 12 `wp_run` applications and 635 lines, compared with 36 applications and 643 lines in the control.  The control journal records repeated discovery of emitted division guards, Boolean normalization, and branch sequencing, while the candidate journal concentrates on the application invariant and arithmetic after entering the generated transition.

Both journals still spend checks converting the function-entry frame into the loop-head state.  A generated entry-to-loop adapter can state the argument order, fixed-store form, exact generated `U64State`, and post-loop continuation before the proving session.  This boundary should receive a fixed-artifact screen before the method moves to a held-out scalar loop.

The annotation consumer now emits that adapter for a top-level scalar loop whose function parameters and locals are all `i64` and whose entry prefix consists of constant loads and local transfers.  It symbolically computes the loop-head values, proves the exact decomposition from the decoded function tail to the named scalar-loop program, and states a `wp` equivalence for arbitrary module, host state, postcondition, and scalar arguments.  The recipe names the generated `entry_to_loop` theorem before the condition and body equations, and the proof prompt directs the agent to use it immediately after `TerminatesWith.of_wp_entry_for`.

The first implementation check used the fixed 1,938-byte Demo 1 artifact.  `tools/leanexegen annotate` built the generated tail equality and entry theorem, and `tools/leanexegen verify` independently accepted the resulting package and final exact-byte theorem.  Three controlled reproofs then measured the complete Stage 5 effect.

Those runs completed in 1,282.711, 1,601.646, and 1,421.556 seconds, giving a 1,421.556-second median and a 318.935-second range.  The median is 543.898 seconds, or 27.7 percent, below the 1,965.454-second matched compact-transition result.  Median Codex time fell by 26.8 percent, and median independent outer-acceptance time fell by 41.7 percent.

The accepted proofs contain 548, 596, and 572 lines, with a 572-line median compared with 635 lines before the entry adapter.  Their `wp_run` counts are 9, 10, and 12, giving a median of 10 compared with 12 before the adapter.  Each proof applies the checked entry equality, `whileProgram_spec`, condition equations, body equations, direct-call boundary, and singleton-wrapper composition while using a distinct mathematical organization for the prime-factor argument.

Every journal reports that the agent had to derive the external operand-stack reversal before the entry equality matched.  A stronger generated `terminates_with_of_loop` theorem now composes `TerminatesWith.of_wp_entry_for` with the checked entry prefix, states the external arguments in WebAssembly order, and leaves the caller at the exact compact loop-head state.  `tools/leanexegen annotate` built this theorem for the same artifact, and a separate `tools/leanexegen verify` accepted the resulting package.

The journals also distinguish reusable arithmetic guidance from application mathematics.  One run rebuilt word-decrement normalization through modulo `2^64`, while the other two used `UInt64.toNat_sub_of_le`; another run found that generic order lemmas selected an incompatible instance for `UInt64`.  The arithmetic guidance now names the existing subtraction theorems and directs unsigned comparisons through `UInt64.lt_iff_toNat_lt` or `UInt64.le_iff_toNat_le` before natural-number reasoning.

A fixed-artifact screen of the stronger `TerminatesWith` adapter completed Stage 5 in 1,418.100 seconds, compared with the lower adapter's three-run median of 1,421.556 seconds.  This 0.2-percent difference lies inside the earlier 318.935-second range, so it does not establish a time improvement, although the proof fell from median values of 572 lines and 10 `wp_run` applications to 541 lines and five applications.  Its journal shows that the adapter removed external-stack and entry-frame discovery, leaving invariant construction, application mathematics, and `UInt64`-to-`Nat` conversions as the remaining search work.

The accepted proof applies the stronger adapter once, `ScalarTransition.whileProgram_spec` once, and the generated condition and body equations two and four times.  The supplied subtraction guidance prevented the modular reconstruction seen in an earlier run, but it did not reduce the end-to-end time outside the observed distribution.  The next experiment will keep these general assets and apply them to a held-out scalar loop with different arithmetic and invariant structure.

### Held-out scalar post-test result

Demo 6 exposed a distinct compiler form: `Expr.loopFoldMultiSlot` nested beneath a scalar assignment.  Its emitted code initializes several accumulator locals, executes a body-first loop with staged values and a done flag, and copies the selected accumulator into the destination after the loop.  The earlier recognizers covered statement-level while loops and top-level loop-fold assignments, so the baseline annotation omitted this region.

The compiler now emits `leanexe.loop.scalar-post-test.v1` for this expression form when every body operation fits the typed scalar descriptor and the release-offset list is empty.  The annotation names the accumulator locals, initial expressions, result slot, destination, scratch boundary, exact top-level block, and body-first descriptor.  Inequality is a first-class scalar condition because the compiler emits the final done test as `i64.ne`; the generated equality therefore matches the decoded instruction region by reduction rather than replacing that instruction with an equivalent sequence.

`ScalarTransition.postTestProgram_spec` proves the body-first loop for an artifact-defined invariant and decreasing measure.  Generated `AnnotationMatches` declarations prove exact region equality, compact body and condition transitions, the entry prefix, and a `TerminatesWith` adapter for the external scalar call.  Independent annotation-package verification accepted those declarations over Demo 6's unchanged 1,770-byte WASM artifact with SHA-256 digest `8126a2d03d514dd1335250b05fc9a1f9b89b84b55cc5b4d3e5a019c0ca6599cf`.

The held-out baseline completed Stage 5 in 1,056.072 seconds and produced a 191-line proof after nine journaled scalar edits.  The first fixed-artifact post-test run completed in 495.497 seconds, a reduction of 560.575 seconds or 53.1 percent, and produced a 155-line proof after three edited candidates.  Codex time fell from 954.785 to 446.255 seconds, while outer acceptance fell from 88.670 to 35.786 seconds.

Two repeats of the retained configuration completed in 520.301 and 510.885 seconds.  The three-run median is 510.885 seconds, the range is 24.804 seconds, and the median reduction from the held-out baseline is 545.187 seconds or 51.6 percent.  The proofs contain 155, 157, and 171 lines, while their journals record three, two, and two edited candidates and no reconstruction of the emitted loop transition.

The accepted candidate applies the generated `terminates_with_of_loop` theorem, `postTestProgram_spec`, and both compact transition equations.  It retains one `wp_run` application while eliminating the baseline's raw `wp_loop_cons` and seventeen explicit `wp_iff_cons` applications.  Its remaining edits concern folding the exact three-instruction exit suffix and normalizing the generated compact state constructor in the terminal case.  The journal attributes no edit to reconstructing the loop body, checked remainder branch, staged accumulator transfers, done test, or external argument order.

A follow-up generated a checked `exit_wp` theorem for the exact three-instruction result-copy suffix.  The accepted proof used it and eliminated the remaining `wp_run`, but Stage 5 increased to 633.288 seconds, 24.0 percent above the retained median, and the journal records four edited candidates caused in part by explicit argument and folded-state presentation.  The experiment passed independent verification and remains preserved with its journal and telemetry, but the active recipe omits the theorem because the time and proof-search metrics regressed.

Every later proof-time iteration reviews the journal, accepted source, and telemetry before changing the annotation vocabulary or LTG.  The proof prompt now asks the agent to name each supplied recipe, theorem, tactic, and annotation it tried, describe its effect or reason for abandonment, and identify missing general assistance suggested by diagnostics.  It also permits abandoning a direct recipe whose exact shape does not match or whose residual goals are worse, without restructuring unrelated code to force the application.

### Held-out counter-transfer result

Demo 7 applies the existing scalar post-test annotation to a different two-accumulator transition: `(remaining, result)` changes to `(remaining - 1, result + 1)` until the first component reaches zero.  The reference proof received the exact scalar region, compact transition equations, scalar entry theorem, and singleton-wrapper composition, but it derived the fixed-width counter facts during the proof session.  Stage 5 took 577.039 seconds, produced 171 lines, and required four edited candidates.

The retained LTG adds `State.localU64ToNat`, `CounterTransition.decrement_add_increment`, and `CounterTransition.decrement_toNat_lt`.  The recipe selects the two counter theorems only when the checked descriptor contains unit decrement and unit increment, while any scalar binary operation adds `U64Op.apply` as focused transition guidance.  The declarations mention scalar state and `UInt64` operations rather than Demo 7, its generated namespace, local count, wrapper, or specification.

Three retained runs completed in 520.815, 405.284, and 816.771 seconds.  Their median is 520.815 seconds, 56.224 seconds or 9.7 percent below the reference, but their 411.486-second range records substantial proof-agent variance.  Median proof size fell from 171 to 135 lines, while the journals contain three, one, and ten edited candidates.

The slow journal attributed most revisions to unifying `postTestProgram_spec` with the generated scalar-entry theorem after the invariant and measure were complete.  An experimental generated theorem composed those checked boundaries and passed exact-artifact verification, but its three screens took 387.160, 558.581, and 748.263 seconds.  The 558.581-second median is 7.3 percent above the retained configuration, and median proof size rose from 135 to 140 lines, so the active generator and recipe omit that composition theorem.

That screen retained the operation-selected arithmetic lemmas and guidance while preserving the rejected composition packages for analysis.  The counter LTG improved the primary median and the secondary proof size on a held-out loop, although the timing distribution showed that application and presentation search still dominated some sessions.  The subsequent experiments therefore targeted the repeated invariant and compact-state boundary rather than another local arithmetic helper.

### Rejected cut-point and coordinate screens

A deterministic singleton-wrapper starter defined the scalar result through the formal singleton output and applied `FixedArraySingletonWrapper.wrapperProgram_spec` before Codex began.  The resulting proof passed independent exact-artifact acceptance, but Stage 5 took 936.788 seconds, 79.9 percent above the retained median, and required four edited candidates.  The generator removed that starter and preserved its package for comparison.

The cut-point journal also recorded that annotations use combined-local indices while `State.localU64ToNat` indexes `State.locals`.  A candidate helper accepted a combined-local index directly, and three agents used it without coordinate errors in accepted 142-, 140-, and 141-line proofs.  Their Stage 5 times were 651.892, 577.172, and 521.718 seconds, giving a 577.172-second median that is 10.8 percent above the retained configuration despite reducing median edit count from three to one.

The combined-coordinate helper and its automatic recipe entry were removed after the timing screen.  The journals establish that it improves index presentation, while the distribution shows no proof-time improvement under the current task structure.  The retained configuration remains the counter arithmetic LTG with the wrapper-boundary starter, and the failed packages remain available for later cut-point-graph work.

### Rejected task-context selection

A deterministic task-context selector treated a complete wrapper composition as covering its lower-level recipes, then retained detailed LTG catalog entries and strategy sections only for uncovered functions.  On Demo 7 it selected `Array`, `ScalarTransition`, and `FixedArraySingletonWrapper`, omitting detailed length-dispatch, direct-call, allocator, and memory material while preserving every permitted module in a compact fallback list.  This reduced the combined prompt and supplied guidance from about 13,500 words to about 6,800 words.

Two fixed-artifact runs took 777.102 and 818.470 seconds, giving a two-run median of 797.786 seconds.  The result exceeds the retained 520.815-second median by 53.2 percent, and even an arbitrarily fast third run would leave a three-run median of 777.102 seconds.  Their accepted proofs contain 123 and 142 lines, so the shorter first proof provides secondary structural evidence but cannot retain the slower selector.

Both journals used the selected wrapper composition, scalar transition recipe, and counter lemmas without consulting a fallback module.  The agents still spent several full edit-and-build cycles constructing the existential scalar invariant, normalizing compact states, and removing redundant presentation steps.  The active task therefore restores the full catalog and program-selected strategies; later retrieval work needs a checked proof skeleton or smaller elaboration unit that changes the work performed, rather than a prose reduction alone.

### Promoted checked semantic summary

`CounterTransition.postTestProgram_spec` now captures the reusable mathematical core of a two-counter body-first loop.  Its premises describe a state view, the initial counter pair and conserved sum, a zero-counter exit transition, and a nonzero transition from `(remaining, result)` to `(remaining - 1, result + 1)`.  The theorem derives sum preservation and strict `UInt64` measure decrease through the existing counter lemmas.

The annotation consumer recognizes this semantic schema only for a one-parameter, one-result function whose checked scalar body has the required two transitions.  It also checks the `(input, 0)` loop-head values, Boolean exit outcomes, returned accumulator, empty release list, and exact store-neutral suffix.  It then emits a complete `TerminatesWith` identity theorem whose proof uses generated body and condition equations, the exact entry theorem, the decoded suffix, and the shared counter-transition theorem.

The production annotation command built the generated theorem against Demo 7's unchanged 1,750-byte artifact, and separate verification accepted each proof package.  Three fixed-artifact screens completed Stage 5 in 386.828, 371.243, and 354.004 seconds, giving a 371.243-second median and a 32.824-second range.  The median is 28.7 percent below the prior retained median, while proof lines fell from a 135-line median to 68 and edited candidates fell from three to one.

Every Demo 7 agent used the generated semantic summary directly as the scalar premise of `FixedArraySingletonWrapper.wrapperProgram_spec`.  None reconstructed the loop invariant, termination measure, hidden local frame, body transition, condition transition, or exit suffix.  This consistency selected an independent compiler-generated layout as the next validation.

Demo 8 adds an audit accumulator that starts at the input and increases by two on every nonzero iteration.  The compiler emitted 23 locals, accumulator coordinates `[4, 5, 6]`, and result slot two, compared with Demo 7's 15 locals and two accumulators.  The generalized recognizer discovers the remaining-and-result pair by checking candidates against the initial state, zero transition, nonzero transition, condition outcomes, returned accumulator, and suffix.

The fresh end-to-end run generated a new specification, source, 1,793-byte WASM artifact, annotations, and proof under namespace `GeneratedRf75664d74ca656b6`.  Stage 5 completed in 313.253 seconds, and the first edited candidate used the generated semantic summary in a 70-line proof.  Separate package verification accepted the result, providing out-of-sample evidence for the semantic recognizer without changing the Demo 7 timing comparison.

### Promoted complete checked composition

The singleton-wrapper composition now records the exact scalar callee identified by its checked direct-call region.  When that callee has exactly one generated counter-transfer identity theorem, the deterministic starter applies `FixedArraySingletonWrapper.wrapperProgram_spec` and supplies the generated theorem as its callee premise.  Recipe validation checks the callee identity against the wrapper annotation, and older stored recipes remain valid without selecting the stronger starter.

This composition closes the public length dispatch, checked input read, scalar call, allocation, result stores, return, scalar invariant, and scalar termination before proof generation.  Codex receives two equations relating the wrapper result to the formal specification, so application semantics remain in the generated behavioral proof.  The earlier rejected cut-point left the scalar proof open; the checked summary supplies the premise that changes this decomposition.

Three fixed-artifact Demo 7 runs completed Stage 5 in 232.164, 201.366, and 204.537 seconds.  Their 204.537-second median is 166.706 seconds, or 44.9 percent, below the checked-summary median, while the range is 30.798 seconds.  Every first edited candidate passed, the median proof has 72 lines, and separate verification accepted all three packages over the unchanged 1,750-byte artifact.

The component covers singleton-array wrappers whose exact scalar callee satisfies the checked counter-transfer schema.  A fixed-artifact Demo 8 run received the same complete starter, used the generated three-accumulator theorem, changed only the two formal-result equations, and passed on its first edited candidate.  The accepted proof confirms structural transfer across a different local layout and an independent audit accumulator.

The Demo 8 run took 477.180 seconds, 52.3 percent longer than its earlier 313.253-second proof, and produced 72 lines instead of 70.  One run cannot separate agent variance from a configuration effect, but it supplies no timing improvement on this artifact.  The Demo 7 distribution remains the proof-time evidence for retaining the starter, while Demo 8 supplies independent applicability evidence and a preserved negative timing result.

### Residual specification normalization example

A deterministic follow-up unfolded `FormalSpec.expected` after complete checked composition and reduced the size-one array through `Array.size_eq_one_iff`.  This rule depends on the residual theorem shape rather than a generated function or specification body, and it closes definitional specifications while leaving harder semantic equations available for proof generation.  Demo 8 accepted the untouched 67-line starter through Codex in 219.561 seconds, 29.9 percent below its initial run.

Two fixed Demo 7 Codex runs accepted the same untouched 67-line starter in 242.798 and 211.558 seconds.  This isolated screen could not beat the retained complete-starter median, so its accepted packages and journals remain worked examples.  The next iteration combined normalization with direct acceptance of a starter that passes the full artifact check, eliminating an unnecessary Codex session.

An initial direct implementation built the artifact theorem twice and took 227.698 seconds.  The consolidated path uses the first full check for both completeness detection and package acceptance, falling back to Codex only when the first Lean target reports an ordinary proof failure.  Runner failures and failures in byte comparison, declaration audit, or later acceptance still stop the run.

Three consolidated Demo 7 runs completed in 112.152, 125.103, and 156.268 seconds, giving a 125.103-second median that is 38.8 percent below the prior 204.537-second median.  All three accepted the same 67-line proof with zero Codex time and passed separate verification.  Demo 8 exercised the same path over its three-accumulator layout in 212.727 seconds, 32.1 percent below its initial run, and also passed separate verification.

### Capacity and loop-edge iteration

The next fixed Demo 9 proof received exact capacity-prefix equalities in both length branches and applied `FixedArrayCapacity.constantProgram_spec` twice.  It also applied the checked dispatch, allocator, fold setup, continuing traversal, result placement, memory framing, length store, payload store, and array-representation theorems.  Independent verification accepted the 642-line proof over the unchanged 1,979-byte artifact.

The journal records a monotonic Stage 5 duration of 3,070.994 seconds, 47.4 percent above the retained fold-structure proof.  Broad reduction crossed the true traversal guard into the caller's result suffix and later expanded the accumulator/index update inside the complete artifact theorem, exhausting the heartbeat budget at both boundaries.  The agent also rebuilt combined-to-internal getter conversions because its traversal search did not select the separate frame-projection entry.

`FixedArrayTraversalInput.continuingProgram_exit_spec` now proves the equal-index guard edge through `Break 1`, while `FixedArrayResult.finishProgram_spec` proves the final root-to-destination-to-return transfer.  The array-fold recipe advertises the exit theorem and both frame-projection declarations beside the exact continuing-prefix equality, and the traversal LTG entry links directly to the frame entry.  The wrapping-add accumulator/index update remains local evidence until another compiler output or demo establishes a recurring shape or motivates a checked descriptor for fold-step code.

### Entry-dispatch opacity package

A local irreducibility screen showed that the ordinary length-dispatch tactic still depends on unfolding the complete decoded function body.  Marking `func0Def` irreducible hid required function-record projections, while marking only `func0` hid the reduction from the program name to `FixedArrayLengthDispatch.leProgram`.  Both variants failed at the first body-level `change` before reaching either branch.

The length-dispatch consumer now emits named valid-branch, invalid-branch, dispatch, and suffix programs when the checked region begins at the function's first top-level instruction.  It also emits an exact region equality and a function equality from the decoded body to the named dispatch followed by the named suffix.  The branch definitions contain the exact decoded Lean instruction lists, so the equality checks artifact structure without relying on the source compiler or a theorem about source lowering.

Demo 10's complete annotation package compiled these declarations and passed independent verification over the unchanged 1,979-byte artifact.  With `func0` locally irreducible, the primary proof changed the body-level goal to the named program, rewrote it through the generated equality, and then used its existing dispatch and branch proofs.  Lean accepted `ArtifactResult` after two explicit reductions of the empty named suffix.

The modified proof contains 578 lines, 1,951 words, and 31,087 bytes, compared with 572 lines, 1,931 words, and 30,577 bytes for the primary proof.  Its warm `Behavior` and `ArtifactResult` targets took 8.2 and 2.1 seconds, while one corresponding reducible build took 9.0 and 2.3 seconds; these single cached builds do not establish a timing improvement.  The generated annotation module grew from 11,597 to 24,930 bytes because the package names concrete branch bodies, which records a distribution and checking cost that later package representations should reduce.

The same generator compiled and passed independent package verification on Demo 7's normalized-equality dispatch and nonempty suffix.  That second artifact checks the alternate dispatch constructor, function-prefix composition, and suffix rendering without testing an irreducible proof.  A fresh fixed-artifact reproof is still required to determine whether a proving agent retrieves this interface and uses it without expanding the named branch bodies.

### Compact suffix theorem boundary

The fresh Demo 10 reproof received the generated function and branch equalities but selected the ordinary length-dispatch tactic.  Its journal contains no use of `function_0_length_dispatch_0_function_eq` or local irreducibility, so the run supplies no fresh-agent evidence for the entry-opacity interface.  The checked package remains useful for manual opacity and exact branch access, while automatic selection requires another experiment or a stronger recipe.

The run exposed a reusable proof-construction boundary after the checked fold setup.  Four related builds ended without a diagnostic while `Wasm.wp_loop_cons` carried the result-placement suffix and public artifact continuation, and three recorded the six-gibibyte child-memory ceiling.  An inline `Wasm.wp.conseq` with a compact loop postcondition retained the failure, while moving the suffix into a separate `productSuffix_spec` declaration restored ordinary diagnostics and allowed proof construction to continue.

The final proof passed independent verification over the unchanged 1,979-byte artifact.  Stage 5 took 2,331.276 seconds, and the accepted source contains 687 lines, compared with 1,596.295 seconds and 572 lines for the retained proof.  Structured LTG now records the separate-declaration method as provisional completion guidance, and the proof prompt prohibits an unchanged retry after timeout, memory-limit, or silent target failure.

`FixedArrayFold.singletonResultProgram_spec` now distills the artifact-local suffix theorem into checked ProofKit support.  It parameterizes the accumulator, result, root, destination, and return locals, accepts the caller's frame and represented singleton result, and reaches `singletonResultPost` without naming a fold operation or formal specification.  `finishFrame_return_get` supplies the final getter fact from the ordinary validity premises.

The annotation consumer recognizes this composition only when every instruction after the annotated fold result placement is the standard singleton payload store and root transfer.  It extracts the five local roles, emits a named `singletonResultProgram`, and proves an exact decoded-region equality from result placement through the end of the enclosing branch.  The recipe advertises the equality, program, semantic theorem, and compact endpoint together.

A production annotation run built these declarations over Demo 10's unchanged artifact, and independent package verification accepted the generated equality, retained behavior theorem, and final artifact theorem.  The preserved capability package records no theorem use because its behavioral proof predates the theorem.  A later fixed-artifact reproof supplied the first fresh-selection evidence.

The fresh agent retrieved `compact-loop-suffix-boundary` from the structured indexes, selected the exact singleton-result recipe, and used `FixedArrayFold.singletonResultProgram_spec` inside a local `productSuffix_spec` adapter.  The adapter retained the public specification consequence and concrete frame premises, but it replaced separate result-placement, payload-store, and root-transfer instruction proofs with the shared theorem.  Independent verification accepted the resulting artifact theorem over the unchanged digest.

Stage 5 took 2,998.613 seconds, including 2,875.208 seconds in Codex and 110.879 seconds in outer acceptance.  This is 28.6 percent slower than the earlier compact-suffix run and 87.8 percent slower than the retained primary proof.  The accepted source contains 707 lines, 3,072 whitespace-delimited words, and 34,081 bytes, compared with 687 lines and 35,160 bytes for the earlier compact-suffix proof; the shared declaration improved composition structure without reducing generation time or line count.

The journal identified the next compiler-motif boundary after the shared suffix succeeded.  Applying the loop rule under the generated scalar frame exhausted one million heartbeats, while an exact frame equality removed that failure and a continuation-generic `productLoopBody_spec` composed the traversal exit, generated continuing traversal, compiler-derived scalar transitions, guarded back edge, invariant callback, and decreasing-measure callback.  That helper remains artifact-local because its invariant and multiplication fold coordinate occur in its type, but the repeated composition shape motivates a parameterized checked fold-body theorem whose callbacks carry the application mathematics.

### Checked continuing fold-body composition

`Project.ProofKit.FixedArrayFoldBody.continuingGuardedProgram_spec` implements the parameterized boundary without naming an accumulator operation, fold invariant, termination measure, or formal specification.  It executes the active traversal guard, loads the represented input element, identifies the loaded frame with a compact scalar state, and applies the compiler-described body, condition, continuing statement, and guarded back edge.  Its two callbacks expose `Break 1` and `Break 0` to the caller, where the artifact proof reconstructs application semantics and the strict measure.

The annotation consumer now emits `<region>_continuing_loaded_frame_eq` beside the existing continuing frame, item-validity theorem, and scalar evaluator equations.  The fold recipe advertises that equality and `FixedArrayFoldBody.continuingGuardedProgram_spec` only after the decoded traversal and guarded-step regions satisfy the structural matcher.  The structured LTG entry indexes the theorem under arrays, loops, compiler motifs, and proof construction, with Demo 9 and Demo 10 as checked consumers.

A production Demo 10 annotation package compiled the generated loaded-frame equality over the unchanged artifact and passed separate package verification.  A manual substitution in the fresh singleton-suffix proof passed the complete `ArtifactResult` target, replacing one artifact-local loaded-frame theorem and the separate traversal and guarded-back-edge composition.  The modified source contains 704 lines, 3,065 whitespace-delimited words, and 34,043 bytes, compared with 707 lines, 3,072 words, and 34,081 bytes for the accepted source from which it was derived.

The manual result establishes interface fit and a small reduction in local scaffolding.  It does not establish automatic selection or a proof-generation-time improvement because no fresh proving session produced that source.  The following fixed-artifact screens supplied the generated recipe and structured LTG entry to Demo 10, then used Demo 9 as the cross-operation transfer test.

The fresh fixed-artifact screen retrieved `fixed-array-fold-body` on its second structured query and used `continuingGuardedProgram_spec` on the strict-index branch.  The accepted proof passes the generated loaded-frame, multiplication-body, false-condition, and index-increment equations to the shared theorem, then proves the product-prefix successor and decreasing measure in its continuation callback.  A separate `leanexegen verify -s` run accepted the complete package over the unchanged 1,979-byte artifact and digest.

Stage 5 took 1,913.092 seconds, which is 36.2 percent below the preceding 2,998.613-second singleton-suffix reproof and 19.8 percent above the retained 1,596.295-second primary proof.  The source contains 650 lines and 2,102 whitespace-delimited words, compared with 707 lines and 3,072 words for the preceding reproof.  The new boundary therefore improved the directly preceding composition-heavy run in both time and source structure, while the primary proof remains faster and shorter.

The journal identified a correctable interface-use cost.  Lean inferred the dependent `hItem` and `hIndex` premises from later arguments, shifting positional tactic bullets and causing three avoidable edit-and-check cycles.  The structured LTG entry now requires named structural and dependent premises, local unfolding only at the loaded-frame equality, and direct use of the generated continuing evaluator rather than broad simplification.

The Demo 9 transfer screen kept the formal specification, source, 1,979-byte WASM module, and digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5` fixed.  Its first annotation-driven catalog query selected `fixed-array-fold-body`, and the accepted proof used `continuingGuardedProgram_spec` with the generated wrapping-add body, false condition, index increment, and loaded-frame equality.  A separate package-verification run accepted the artifact theorem and both sample executions.

Stage 5 took 2,074.169 seconds, 0.4 percent less than the retained fold-structure proof and 5.2 percent more than the guarded-back-edge screen.  The source contains 588 lines, 2,484 whitespace-delimited words, and 29,973 bytes, compared with 589 lines, 2,208 words, and 31,148 bytes for the guarded-back-edge proof.  The timing and size evidence is mixed, while accepted use for wrapping multiplication and wrapping addition establishes transfer across accumulator operations.

The Demo 9 journal confirms that named dependent premises prevented the bullet shifting seen in Demo 10.  It also shows that the application should fix `module_`, `env`, `st`, and `frame` when callback inference generalizes the weakest-precondition context, and that a proof-local invariant frame should acquire named parameter, length, value-stack, and getter facts before suffix composition.  The structured LTG entry records these instructions and advances to promoted compiler-motif evidence on cross-operation applicability rather than a proof-time claim.

### Generated continuing-frame accessors

The annotation consumer now emits exact frame-shape and getter theorems beside every compiler-described continuing fold frame.  The declarations state the parameter list, internal-local length, empty operand stack, and `Locals.get` result at every combined parameter-and-local index.  Each theorem checks by reduction against the scalar state generated from the decoded function's parameter and local counts.

The fold recipe lists every generated accessor with `FixedArrayFold.resultFrame_get_result` and `resultFrame_get_of_ne`.  The first shared theorem reads the accumulator value written to a valid nonparameter result local, while the second preserves a distinct valid nonparameter getter across that write.  An artifact proof can therefore cross both the continuing-frame and result-placement boundaries without declaring frame-specific `rfl` theorems.

A proof that wraps the generated frame in a semantic abbreviation should use `simp only [<semantic-frame>, <generated-accessor>]`.  Unrestricted simplification can unfold `Wasm.Locals.get` into parameter and internal-list branches before the exact accessor matches, recreating the representation proof.  The restricted form keeps the compiler-derived equality intact and exposes only the requested frame fact.

The fixed Demo 9 substitution removed ten local projection declarations from the accepted fold-body proof and passed independent package verification over the unchanged artifact.  Its source decreased from 588 to 555 lines and from 2,484 to 2,084 whitespace-delimited words; bytes decreased from 29,973 to 29,291 because the generated names are long.  This manual experiment measures proof structure rather than generation time, while Demo 10 independently checks the accessor family on a different fold artifact.

A fresh fixed-artifact Demo 9 run selected the frame-accessor entry, used the generated frame-shape and combined-local getter theorems, and applied both shared result-frame getters.  Its accepted 616-line proof contains no proof-local frame-projection theorem, and separate package verification accepted the unchanged artifact digest.  Stage 5 took 2,230.869 seconds, 7.6 percent longer than the preceding fold-body reproof, so the experiment establishes automatic retrieval and structural use without a proof-time or source-size improvement.

The Demo 10 transfer used the generated value-stack and index accessors and both result-frame theorems, but its journal never selected the accessor LTG entry.  It discharged eleven frame facts by reduction despite receiving the entry, strategy paragraph, and complete accessor recipe, then completed an independently verified 600-line proof in 2,099.237 seconds.  The proof prompt now treats a new residual goal class as a retrieval checkpoint and requires an accessor search before reducing frame projections or introducing local frame facts.

Held-out Demo 11 tested that retrieval checkpoint on a bitwise-XOR fold.  The journal searched the recipe and catalog before a capacity-frame reduction, recorded the absence of an exact capacity accessor, and later used the generated parameter, local-length, operand-stack, accumulator, root, index, and stop accessors at the fold boundaries.  Independent verification accepted the 676-line proof in 2,452.384 seconds, so the result establishes goal-directed retrieval and cross-operation use while supplying negative time and size evidence.

The accessor entry now has accepted consumers for addition, multiplication, and bitwise XOR and advances to promoted compiler-motif support.  The XOR proof still needed local declarations around the public postcondition and singleton suffix because the complete loop assertion remained expensive.  A compact generated completion adapter or a general `Locals` equality theorem constitutes the next hypothesis, while the current checkpoint adds neither without another controlled screen.

### Generated fold-completion adapters

`Project.ProofKit.Frame.ext` proves equality of two `Wasm.Locals` values from equality of their parameter lists, internal-local lists, and operand stacks.  The same module supplies projection theorems for replacing an operand stack, including preservation of every combined-local getter.  These declarations address equivalent-frame goals without exposing the representation of `Wasm.Locals` throughout an artifact proof.

`FixedArrayFold.singletonResultProgram_spec_to` executes the compiler's completed-fold suffix against an arbitrary postcondition over its exact final store and frame.  For every matched singleton-result suffix, the annotation consumer now generates `<fold>_singleton_result_spec`, which applies the generic theorem with the decoded local roles and the exact continuing-frame accessors.  The artifact proof retains the accumulator's mathematical meaning, its payload bound, the represented singleton result, and the final public-postcondition argument.

The Demo 11 annotation package checked this adapter against the unchanged 1,979-byte XOR artifact with digest `4f56fd45fe246f3199dc81169235aa0673659b3b2e82e4beeb4c1d910501bd64`.  A manual substitution removed the proof-local singleton-result theorem and postcondition bridge, applied the generated adapter directly, and used `Frame.ext` for the equivalent exit frame.  The complete artifact theorem passed, while the proof decreased from 676 to 580 lines, from 2,798 to 2,350 whitespace-delimited words, and from 34,648 to 30,182 bytes.

The same adapter passed manual substitutions in Demo 9's unchanged wrapping-sum artifact and Demo 10's unchanged wrapping-product artifact.  The addition proof decreased from 616 to 569 lines, from 2,541 to 2,404 words, and from 30,901 to 28,245 bytes.  The multiplication proof decreased from 600 to 553 lines, from 2,371 to 2,162 words, and from 30,568 to 28,254 bytes.

The accepted addition, multiplication, and XOR uses establish transfer across accumulator operations without putting any operation in the shared theorem or generated adapter.  These manual substitutions measure interface fit and proof structure, but supply no proof-generation-time result because an agent did not generate the edited proofs from fresh tasks.  A controlled screen was therefore required to record retrieval, journal observations, edited Lean checks, Stage 5 time, and independent package verification.

The fresh Demo 9 screen selected the completion entry during its first annotation-directed search and applied the generated adapter directly to the public valid-branch postcondition.  Independent verification accepted the resulting 526-line proof over the unchanged artifact digest.  Stage 5 took 1,992.546 seconds, 10.7 percent less than the preceding frame-accessor screen and 1.0 percent more than the best guarded-back-edge screen, while the proof removed 90 lines and 502 words from the frame-accessor proof.

The journal separates successful suffix composition from the work that remains.  The adapter closed accumulator placement, payload storage, root transfer, representation, and the public result without a proof-local suffix theorem.  Capacity-frame getters, the allocator's returned-root getter, and the annotated `releaseReadyLocal` still required representation reduction or a larger invariant because the current sidecar names those values without generating the corresponding frame interface.

The follow-up adds generic capacity and allocator frame projections.  `capacityFrame_get_capacity` and `capacityFrame_internal_get_capacity` expose the normalized capacity in the coordinate systems used by later theorems, while `allocFrame_get_root` exposes the returned array pointer from any shifted allocator window.  Their statements depend on frame bounds and allocator offsets rather than an artifact function or fold operation.

The generated continuing frame already had a checked accessor for `releaseReadyLocal`, but the recipe described it only by its numeric slot.  Fold recipes now attach compiler role names to every generated frame getter, so a search for `releaseReadyLocal` identifies the exact accessor declaration.  A regenerated Demo 9 annotation package contains the role-labelled recipe, and independent verification accepts that package over the unchanged artifact.

A fresh Demo 10 transfer selected and used the capacity getter, allocator-root getter, generated singleton-result adapter, shared fold-body theorem, generated loaded-frame equality, and compiler-derived multiplication transitions.  Independent verification accepted its 684-line proof over the unchanged artifact in 1,979.854 seconds.  The run was 5.7 percent faster than the preceding frame-accessor screen but produced 84 more lines and remained 24.0 percent slower than the retained primary proof.

The journal attributes the larger proof to complete branch and loop reconstruction rather than failure of the new interfaces.  The invalid branch used both new frame projections directly, and the completed-loop branch used the exact suffix adapter directly.  Two parser conflicts, one positional dependent-premise attempt, and one broad simplifier failure also consumed iterations that structured tactic metadata and stronger proof-construction guidance can address.

### Structured tactic records

Schema-2 LTG entries can now index tactics as checked retrieval records.  A record names the command, defining ProofKit module, residual goal shape, required premises, applicable annotation kinds, and fallback theorem.  Catalog validation confirms that the command occurs in the named module and that its module, annotations, and fallback already belong to the canonical entry.

The first inventory contains five commands across four entries: bounded length dispatch, block-wrapped loop reasoning, singleton and pair `UInt64` array reconstruction, and disjoint word reads.  Generated category indexes include the complete records and their command, module, and fallback names in searchable terms.  The proof task compares a selected record's goal shape, premises, and annotations with each new residual goal before choosing its command or fallback theorem.  A fixed-artifact proof screen must still determine whether an agent follows that retrieval rule and whether the selection changes proof construction.

### First structured-tactic proof screen

The first controlled Demo 9 task preserved the specification, source, 1,979-byte WASM artifact, decoded Program, and artifact digest used by the earlier fold screens.  The agent selected `wp_fixed_array_length_le_dispatch_from` for the bounded-length dispatch and `wp_block_loop` for the block-wrapped fold, and it used neither fallback declaration.  Its journal rejected the indexed result, singleton-wrapper, and word-read tactics after comparing their goal shapes and premises with the current residual goals.

The independent outer Lean check rejected the generated candidate despite the agent's reported successful check.  One broad simplification exceeded the configured step limit, `omega` lacked the represented input array's size bound when proving the successor index fit in `UInt64`, and the measure rewrite encountered a callback frame whose parameter and local projections had advanced while its operand-stack projection remained attached to the predecessor.  The failure supplies tactic-retrieval evidence, but it supplies no accepted artifact proof or proof-generation time.

A focused repair constructed the semantic successor as `UInt64.ofNat (index + 1)` and used `UInt64.ofNat_add` only to discharge the compiler-generated evaluator equation.  It then changed the loop callback frame to `afterContinue.toState.toLocals []`, normalized the operand stack with the generated continuing-frame accessor, and used the represented array's size theorem for the fixed-width bound.  The complete `ArtifactResult` target accepted the repaired candidate under the standard Lean runner limits.

The structured LTG fold-body entry now records those two proof-construction rules.  The rejected candidate, full outer diagnostic, frequent prose journal, task inputs, and separately checked repair are retained under the Demo 9 benchmark.  A corrected fresh task will test whether another agent follows the guidance and obtains independent acceptance over the same artifact.

The corrected fresh task again selected and applied `wp_fixed_array_length_le_dispatch_from` after comparing its indexed goal shape, premise, and annotation kind with the entry boundary.  Its candidate then entered `FixedArrayCapacity.constantProgram_spec` in both branches, where one Lean check remained silent and the candidate and journal stopped changing for about twenty-two minutes.  The owned session was interrupted after approximately forty-eight minutes without reaching allocation, fold induction, result construction, or the revised continuation-frame rules.

The censored run therefore adds repeated dispatch-retrieval evidence while leaving the fold-guidance correction untested by a fresh accepted proof.  Its preserved journal rejects the indexed `word_reads` tactic at the branch-level `Wasm.wp` goal, demonstrating another shape-based negative selection.  Further work at this boundary requires a smaller capacity-to-allocation elaboration boundary or a checked composition theorem before another fixed-artifact run.

## Completion criteria

The first complete increment emits a validated sidecar for every ordinary library-mode compilation requested by `leanexegen`.  Demos 1, 2, and 3 prove the same specifications over the same WASM bytes through an annotation-driven deterministic proof plan.  The retained evidence records proof-generation timings, annotation validation, region coverage, and independent Lean acceptance.

The design succeeds only if annotations reduce proof-generation time or expose a smaller, well-defined semantic bottleneck that leads to a general proof-kit theorem.  A sidecar that gives Codex prose descriptions while leaving it to rediscover instruction boundaries and continuations does not meet the objective.  The useful product is a checked structural decomposition of the artifact that the proof generator can turn into Lean proof steps.

The recipe registry evaluates proof-generation time, proof structure, edited candidates, retrieval behavior, annotation coverage, compiler-derived evidence, and transfer across artifacts.  Fewer proof steps, less local scaffolding, fewer repeated derivations, or greater shared theorem use can justify retaining a slower experiment as provisional support or a worked example while later screens test its value.  Raw source bytes, word length, and identifier length carry no negative weight; descriptive theorem names often record valuable abstraction use.  The retained attempt records identify which direct, indirect, and guidance methods earned selection, which remain provisional, and which supplied useful negative evidence.
