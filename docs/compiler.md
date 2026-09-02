# Compiler Architecture

LeanExe loads an elaborated declaration from a built Lean module, specializes the reachable executable terms, lowers them to a first-order IR, and emits a standalone WebAssembly module.  Lean performs parsing, elaboration, type checking, instance synthesis, termination checking, and proof erasure before LeanExe examines the declaration.  The [language specification](spec.md) defines which checked terms LeanExe accepts, while this document defines the implementation stages and their assurance boundaries.

## Extraction and specialization

`LeanExe.Extract.Env` imports the requested module from `.lake/build/lib/lean` and resolves the fully qualified entry declaration.  `LeanExe.Extract.Core` collects reachable declarations within the accepted dependency boundary, classifies public entries and internal helpers, and lowers their elaborated expressions.  Pattern and structural-recursion modules recognize the specific generated forms used for direct recursion, well-founded recursion, folds, predicates, loops, monadic control, and specialized library calls.

Extraction specializes static inputs before deciding whether a helper belongs to the executable subset.  Static inputs include concrete type arguments, erased proofs, direct lambdas used by recognized helpers, and resolved type-class evidence.  A bounded normalizer reduces applications and method projections until the remaining term is first-order, or reports the expression that failed to specialize.

| Module | Responsibility |
|--------|----------------|
| `LeanExe/Extract/Env.lean` | Module import and declaration lookup. |
| `LeanExe/Extract/Types.lean` | Runtime type recognition, ABI signatures, entry classification, and inline specialization classes. |
| `LeanExe/Extract/Patterns.lean` | Generated matcher, monad, loop, and direct-callback recognition. |
| `LeanExe/Extract/StructuralRec.lean` | Direct and mutual structural recursion, closed folds and predicates, and generated descent forms. |
| `LeanExe/Extract/Demand.lean` | May-evaluate, must-evaluate, and may-trap analysis used to preserve source evaluation order. |
| `LeanExe/Extract/Storage.lean` | Flattened fields, local storage, heap slots, and parameter bindings. |
| `LeanExe/Extract/Values.lean` | Runtime values, liveness, owner slots, and child-pointer masks. |
| `LeanExe/Extract/ReleaseCheck.lean` | Direct-handoff validation for explicit `LeanExe.Runtime.release` calls. |
| `LeanExe/Extract/Core.lean` | Dependency collection, two-pass ownership summaries, expression lowering, and module construction. |

The compiler runs extraction twice.  The first pass computes function summaries, including fresh result-owner offsets, and the second pass lowers each function with the complete summaries available.  This structure allows the second pass to distinguish a fresh helper result from a borrowed heap reference and to insert releases only at supported ownership boundaries.

## IR and ownership

`LeanExe.IR.Core` defines the first-order intermediate representation.  Its values cover supported scalars, arrays, byte arrays, flattened records and variants, and internal recursive pointers.  Its statements cover locals, arithmetic, conditions, calls, traps, allocation, loads, stores, releases, loops, folds, and multi-slot accumulator updates.

The IR includes an executable reference evaluator used for scalar comparison and diagnostics.  Its heap behavior is intentionally incomplete: several heap operations use abstract placeholder results, releases have no observable allocator semantics, and loop evaluation has a fixed safety bound.  The evaluator therefore supports differential checks for its declared fragment and does not constitute a source-to-WASM semantics theorem.

Ownership summaries record which result slots contain fresh roots, which arguments may be borrowed by a result, and which heap fields require retain or release operations.  Generated modules represent heap objects with reference-counted headers, kind tags, payload widths, child-pointer masks, and free-list links.  The runtime supports raw byte buffers, fixed-slot records, and arrays whose element layouts identify owned child pointers.

The compiler inserts releases for supported fresh nonrecursive temporaries and replaced loop or fold accumulators.  An explicit `LeanExe.Runtime.release` must appear as the complete value of a `let` binding and must consume a direct fresh allocation, a helper result whose summary marks the root fresh, or a statically owner-zero array.  `ReleaseCheck` rejects parameter roots, unresolved aliases, copied aliases, later use, repeated release, branch-dependent ownership, unsupported fields, and heap-bearing escapes before IR emission.

## WebAssembly backend

`LeanExe.Wasm.Instr` is the structured instruction language shared by binary emission, WAT rendering, and annotation analysis.  The backend lowers each IR function to a `List Instr`, adds allocator and reference-counting runtime functions, assembles the required sections, and serializes the module as WASM bytes.  `compile-wat` prints the same instruction trees, and `tools/check-wat.sh` checks that `wasm-tools parse` reconstructs the direct binary byte for byte.

| Module | Responsibility |
|--------|----------------|
| `LeanExe/Wasm/Instr.lean` | Structured instructions used by both serializers and annotation analysis. |
| `LeanExe/Wasm/Binary.lean` | IR lowering, runtime functions, section assembly, binary encoding, WASI adapters, and annotation collection. |
| `LeanExe/Wasm/Image.lean` | Canonical versioned final-module image, codec, profile limits, and semantic validation. |
| `LeanExe/Wasm/Image/Emit.lean` | Pure accepted-subset decoder and WebAssembly binary emitter for the library image profile. |
| `LeanExe/Wasm/Wat.lean` | WAT serialization from structured instructions. |
| `LeanExe/Wasm/Leb.lean` | Unsigned and signed LEB128 plus section and vector encodings. |
| `LeanExe/Wasm/LebTheorems.lean` | Checked properties of the compiler's LEB128 implementation. |
| `LeanExe/Wasm/Annotations.lean` | Typed annotation document and region-parameter representations. |
| `LeanExe/Wasm/ScalarDescriptor.lean` | Neutral scalar expression, condition, statement, and loop descriptors. |
| `LeanExe/Wasm/ScalarCertificate.lean` | Theorems connecting successful scalar reification to emitted structured instructions. |

The backend still assembles module sections directly into bytes rather than constructing the Talos module type.  Exact-artifact verification handles this boundary independently by decoding the emitted binary with the proof workspace's checked binary decoder and translating the validated result to Talos.  WAT and the external Talos generator remain useful for source-driven proof-cache production and cross-checking, but the exact-artifact theorem does not obtain its module from either tool.

`compile-image --module M --entry M.entry --out module.image` writes the canonical schema-version-2 image after extraction, lowering, runtime selection, and numeric index resolution.  `emitImage : ByteArray -> Except ByteArray ByteArray` decodes that image and emits the complete library-mode module from code that LeanExe itself accepts.  The bootstrap test requires the Wasmtime-hosted Stage 1 emitter and JavaScript-hosted Stage 2 emitter to reproduce the Stage 1 artifact byte for byte.  This is a self-hosted binary-emitter boundary; Lean and the native compiler still perform all earlier compiler stages.

## Compiler annotations

The compiler emits annotation schema 1 beside a WASM artifact.  Each region contains a stable kind, a structured instruction location, region-specific parameters, and the compiler functions that generated it.  Region recognition operates on the structured instruction tree and records direct calls, array wrappers and traversals, scalar and array loops, length dispatches, encoded optional-index decoders, comparison nodes, and result construction.

Annotations remain untrusted proof inputs until the artifact package checks them against the decoded program.  `tools/leanexegen-annotations.js` validates the JSON schema, selects the named instruction interval from the exact Talos module, and generates Lean equalities and semantic adapters.  A stale location, opcode, local index, constant, or descriptor makes annotation generation or the generated Lean checks fail.

The scalar descriptor path also has compiler-side theorems.  If `ScalarDescriptor.Expr.ofIR`, `Cond.ofIR`, `Stmt.ofIR`, `While.ofIR`, or `EncodedIndex.ofIR` succeeds, the corresponding theorem in `ScalarCertificate` proves equality between descriptor emission and the backend's public emitter.  `EncodedIndex.ofProgramPrefix` then finds that exact decoder shape in the emitted instruction tree and records its source, two-slot scratch window, destination, and encoding.

The artifact consumer checks the complete decoder again against the decoded binary, including both outer branches and the nested unsigned-subtraction branch.  It generates a Lean equality to `Project.ProofKit.EncodedIndexDecoder.program`, whose neutral semantic theorem executes the local-frame update.  A generated artifact proof can use those declarations without importing the IR descriptor or compiler certificate.

Development validation preserved the exact Demo 12 and ClobDepth binaries while generating decoder regions at three distinct local layouts.  Demo 12 passed generated-equality and package verification, while the ClobDepth source proof applies the neutral theorem at both of its decoder sites and passes the complete Talos proof gate.  These results establish emitter-byte preservation, exact region recognition, and cross-program semantic reuse without establishing a proof-generation-time reduction.

## Assurance boundaries

| Claim | Current evidence |
|-------|------------------|
| Lean source is well typed | The pinned Lean kernel accepts the built declaration. |
| Source lies in the supported executable subset | Extraction and reporting reject unsupported types, dependencies, terms, recursion forms, effects, and surviving higher-order values. |
| Explicit release satisfies the implemented direct-handoff rule | `ReleaseCheck` validates every reachable explicit release before module extraction succeeds. |
| WAT and binary serializers receive the same function instruction trees | Both consume `LeanExe.Wasm.Instr`; the byte round-trip test checks the complete module output. |
| Selected scalar descriptors and encoded-index decoders agree with compiler emission | `LeanExe.Wasm.ScalarCertificate` proves successful reification equalities. |
| A distributed binary satisfies a behavioral theorem | The exact-artifact path independently embeds, decodes, validates, translates, and proves the registered bytes. |
| All accepted Lean programs compile correctly | No general extraction, IR, ownership, lowering, or serializer correctness theorem exists. |

Differential execution and source-driven artifact proofs provide program evidence for the tested cases.  Exact-artifact proofs provide stronger evidence about named binaries without establishing a universal compiler theorem.  The [Source-Theorem Transport Plan](../plans/theorem-transport.md) describes a future refinement path whose assumptions would include explicit source, IR, lowering, and byte-identity connections.

## Diagnostics

`report` classifies the entry and its dependencies, `dump-ir` prints accepted IR, `ownership-report` prints owner summaries and release judgments, and `eval-ir` runs the reference evaluator's scalar fragment.  `compile-wat` provides a readable view of the structured instruction output, while `wasm-tools print` provides an independent view of the emitted binary.  [Developing LeanExe](../DEVELOPING.md) defines the diagnostic order and the tests required after a compiler change.
