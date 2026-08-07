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
| `leanexe.array.result.v1` | Length, element-producing regions, allocator window, destination local, and continuation. | Compose allocation, stores, and the final represented-array fact. |
| `leanexe.runtime.allocate.v1` | Size expression, allocator locals, globals, memory-growth branch, and destination. | Select the allocator theorem and establish its post-frame. |
| `leanexe.runtime.retain.v1` | Pointer location, runtime function index, and continuation. | Apply the retain theorem at the emitted ownership boundary. |
| `leanexe.runtime.release.v1` | Pointer location, runtime function index, and continuation. | Apply the release theorem at the emitted ownership boundary. |
| `leanexe.call.direct.v1` | Callee index, argument locations, result locations, and continuation. | Apply a previously proved function theorem and restore the caller frame. |
| `leanexe.loop.counted.v1` | Index local, initial value, bound, step, direction, accumulator locals, body, exit, and continuation. | Construct the loop invariant and decreasing measure from compiler-known structure. |

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

The current unannotated reference points are 372.474 seconds for Demo 1, 512.533 seconds for Demo 2, and 278.656 seconds for Demo 3.  Demo 3's repeated pair-result runs varied from 278.656 to 1,243.846 seconds, so one favorable run does not establish a reliable improvement.  The primary result is the per-demo median proof-generation time, accompanied by the worst per-demo ratio so a large improvement on one artifact cannot conceal a regression on another.

The future compiler-verification theorem may use region boundaries to organize lowering lemmas, but the sidecar does not constitute that theorem or a source certificate.  Artifact proofs continue to use annotations without trusting the compiler, while compiler verification may later prove that a region kind implements its corresponding IR operation.  The two uses share the region vocabulary and structured emitter without sharing a trust assumption.

## Implemented iterations and evidence

The compiler now emits `leanexe.call.direct.v1`, `leanexe.array.length-dispatch.v1`, `leanexe.array.search-key.v1`, `leanexe.array.eq-node.v1`, and `leanexe.array.lt-node.v1` regions through `lean-wasm compile --annotations`.  Annotated emission remains the canonical instruction-emission path, and each corpus migration requires the recompiled bytes to equal the frozen WASM before accepting a sidecar.  The JavaScript consumer checks the structured location, exact top-level instruction sequence, checked-loader branches, Boolean-normalization branches, local window, operand order, branch roles, and continuation before selecting a proof recipe.

Package schema 5 retains `program.annotations.json` and `proof-recipes.json` under the package manifest's file digests.  `leanexegen annotate` converts an older package by recompiling its frozen Source, requiring byte-for-byte equality with the frozen WASM, matching the new sidecar against the frozen Program, and writing a separate annotated package.  A subsequent `reprove` regenerates recipes from the frozen annotations and omits Source and the compiler from the proof task.

The direct-call slice found two Demo 1 calls and selected `Wasm.wp_call_tw`, with `wp_entry_single_call` available for a single top-level call.  Its first annotated reproof took 279.110 seconds, compared with 372.474 seconds for the retained reference, but both sessions produced the same 532-line Behavior source.  The single timing difference does not establish a causal improvement.

The length-dispatch slice covers both emitted encodings: normalized equality in Demo 1 and normalized inequality in Demos 2 and 3.  `FixedArrayLengthDispatch.eqProgram_spec`, `program_spec`, `wp_fixed_array_length_eq_dispatch`, and `wp_fixed_array_length_dispatch` prove the length read, encoding, Boolean normalization, branch choice, and enclosing continuation.  The compiler originally searched for `eqzI64`, while the internal emitter uses `eqzI32`; exact comparison with the emitted instruction type found and corrected that recognizer defect.

The length recipes shortened the accepted proofs but increased total proving time.  Demo 1 fell from 532 to 517 lines while Stage 5 rose from 372.474 to 637.770 seconds.  Demo 2 fell from 900 to 508 lines while Stage 5 rose from 512.533 to 1,387.816 seconds, so proof length did not predict the required performance metric.

The search slice adds a checked key load, equality nodes in both operand orders, and key-first unsigned less-than nodes.  `FixedArrayEqNode.SearchFrame` records the input, local shape, empty stack, and saved key; `afterLoad` and `branch` preserve those facts; `branchN` and `FixedArraySearch.pairPost_branchN_conseq` represent nested continuations.  `FixedArrayLtNode.program_spec` and `wp_fixed_array_lt_node` extend the same frame across a checked indexed load and expose the semantic ordering branches.

The recipe planner sorts regions by structured instruction location, producing depth-first program order instead of compiler-kind order.  Demo 3 now receives length and key-load recipes followed by equality and less-than recipes interleaved at indices 1, 3, 7, 9, 5, 11, and 13.  Exact matching rejects a malformed less-than comparison, an incorrect operand order, a changed checked-loader branch, or a changed Boolean-normalization branch.

Optional search recipes did not improve the first Demo 3 screen.  The accepted proof ignored them, retained the 672-line reference proof with one added blank line, and took 392.544 seconds instead of 278.656 seconds.  An experimental deterministic starter applied a partial structural outline and reduced the proof to 604 lines, but Stage 5 rose to 1,221.892 seconds; leanexegen no longer emits that starter behavior.

The current compiler was run from scratch over the retained Demo 1, Demo 2, and Demo 3 Sources.  Each run reproduced its frozen WASM digest, matched every sidecar region against the decoded Program, and passed independent package verification under the managed Lean runner.  The accepted region counts appear below.

| Demo | Frozen WASM SHA-256 | Matched regions |
|---|---|---|
| 1 | `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7` | One length dispatch and two direct calls. |
| 2 | `ceb37cd3d61158e7f4162c97cac9b79022518a4e67f895d45a3619c7b5a29712` | One length dispatch, one search-key load, and ten equality nodes. |
| 3 | `1a93ec55974666ad54fad73d321b8b9e1f7d67970b272c13bcc77055c8e7631d` | One length dispatch, one search-key load, seven equality nodes, and three less-than nodes. |

Cross-demo validation exposed an overbroad search-key recognizer: Demo 1's ordinary load of its single input initially matched the loader shape.  The compiler now requires a search-key candidate's local window and saved local to match an equality or less-than consumer in the same function, removing the Demo 1 false classification while preserving Demos 2 and 3.  The proof consumer still treats this classification as untrusted guidance and checks every selected instruction region independently.

A fresh Demo 3 reproof with the complete tree recipe set could not start because headless Codex reported an account usage limit until August 10, 2026.  Two attempts failed before proof generation or Lean execution, so they provide no timing result.  The package, annotation, recipe, proof-kit, and independent theorem checks completed without that service.

The next result-region slice should annotate the complete allocator, pair stores, destination assignment, and return continuation only after the consumer can match that whole sequence against `FixedArrayPairResult.constResultProgram` or `inputResultProgram`.  The compiler can identify the array-literal assignment from its IR, but a label over that source operation does not validate the corresponding decoded suffix.  The implementation needs either a shared generated instruction-template description or a checked decomposition equality, avoiding a second hand-maintained copy of the allocator template in JavaScript.

## Completion criteria

The first complete increment emits a validated sidecar for every ordinary library-mode compilation requested by `leanexegen`.  Demos 1, 2, and 3 prove the same specifications over the same WASM bytes through an annotation-driven deterministic proof plan.  The retained evidence records proof-generation timings, annotation validation, region coverage, and independent Lean acceptance.

The design succeeds only if annotations reduce proof-generation time or expose a smaller, well-defined semantic bottleneck that leads to a general proof-kit theorem.  A sidecar that gives Codex prose descriptions while leaving it to rediscover instruction boundaries and continuations does not meet the objective.  The useful product is a checked structural decomposition of the artifact that the proof generator can turn into Lean proof steps.

The recipe registry succeeds only if attempted proof assets reduce total proof-generation time across the corpus.  Local tactic speed, shorter proof text, or a larger catalog does not compensate for slower completed proofs.  The retained attempt records should identify which direct, indirect, and guidance methods earned their place in the active registry.
