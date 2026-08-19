# Artifact Proving

LeanExe proves behavioral properties of exact WebAssembly binaries by reasoning over the Talos execution semantics.  The final theorem starts from bytes embedded in Lean, passes through checked decoding and validation, and identifies the resulting Talos module with the module used by the behavioral proof.  Source programs, compiler internals, annotations, and proof-generation agents may help construct that proof without becoming premises of the retained theorem.

## Two proof paths

The source-driven path begins with a registered Lean declaration.  `tools/talos-artifact.js prepare` compiles the declaration, renders the generated module as WAT, asks the pinned Talos generator for a Lean module value, and updates the tracked execution cache after successful generation.  `tools/talos-proof.js check` regenerates that model and checks the handwritten behavioral theorem against it.

The exact-artifact path begins with a frozen `program.wasm`.  It embeds the complete byte sequence in Lean, decodes the binary into raw syntax, validates the accepted Core 3.0 profile, translates the validated module to Talos, and proves equality with the execution cache used by the behavioral theorem.  `tools/artifact-proof.js` checks the package identity, theorem declarations, logical dependencies, and behavioral result without reading source or invoking the compiler.

| Property | Source-driven path | Exact-artifact path |
|----------|--------------------|---------------------|
| Initial subject | Current compiler output for a registered Lean entry | Registered immutable WASM bytes |
| Model production | WAT plus the external Talos generator | Checked binary decoder, validator, and translator |
| Compiler required during check | Yes | No |
| Source required during check | Yes | No |
| Behavioral theorem | Input-generic theorem over a Talos module | The same theorem after checked module equality |
| Primary use | Compiler development and proof construction | Independent verification of a distributed artifact |

The [artifact format](artifact-format.md) defines the binary and package boundary.  [Verifying a Program](verifying.md) defines the commands and repository files for each path.  The [Talos proof inventory](../proofs/talos/README.md) names the current theorems.

## Proof construction

A behavioral proof normally states a `Wasm.TerminatesWith` result over represented inputs, allocator conditions, memory bounds, and a postcondition for return values and observable state.  It enters the function through a weakest-precondition theorem, divides the body at semantic boundaries, and composes checked lemmas for calls, loops, branches, allocation, loads, stores, release, and final result construction.  Application-specific mathematics supplies invariants, measures, representation relations, and the connection between returned words and the intended computation.

ProofKit contains reusable Talos theorems and tactics for recurring generated patterns.  Its modules cover frames, memory reads and writes, arrays, allocation, runtime functions, direct calls, scalar transitions, traversal, bounded dispatch, loop composition, and result wrappers.  [Artifact-Proof Strategies](proof-strategies.md) gives general construction guidance, while the [ProofKit reference](../proofs/talos/lean/Project/ProofKit/README.md) names the checked API.

Generated proof packages preserve a frequent prose journal.  The journal records which supplied help the agent found, which theorem or tactic applied, why an attempted abstraction failed, how the proof approach changed, and which recurring obligation lacks a suitable shared boundary.  Journal observations are evaluated with the accepted proof and telemetry before annotations, ProofKit, LTG, or agent instructions change.

## Annotation-directed support

Compiler annotations describe selected regions of the structured instruction output.  A region names its kind, exact structured location, parameters, and generating compiler functions.  The current vocabulary covers direct calls, length dispatches, array searches and comparison nodes, map and filter wrappers, array folds, scalar loops, pair results, and related composition boundaries.

The sidecar does not establish a fact about the distributed binary by itself.  The annotation consumer validates the document, selects the corresponding region from the decoded artifact, and generates a Lean declaration whose equality or semantic adapter checks against that exact region.  Any mismatch in artifact identity, path, interval, opcode, local index, constant, descriptor, or expected continuation prevents the declaration from checking.

Proof recipes name the generated equality, the compatible ProofKit theorem, its imports, and the premises the application proof must supply.  Some recipes compose several checked regions, such as a bounded-length branch followed by allocation and a singleton result.  [WebAssembly Annotations](annotations.md) defines the current schema and recipe-generation rules.

## Compiler theorem use

Compiler theorems currently help one part of annotation production.  `LeanExe.Wasm.ScalarCertificate` proves that successful reification of supported scalar IR expressions, conditions, statements, and loops agrees with the backend's structured instruction emitter.  The compiler can therefore reject descriptor drift at the emitter boundary and issue a descriptor that follows from its own lowering definitions.

The artifact package checks the descriptor again against the exact decoded region.  Its retained proof imports neutral scalar-descriptor semantics and the checked region equality rather than importing `LeanExe.IR`, the emitter, or `ScalarCertificate`.  This gives compiler theorems an indirect role in proof construction while preserving the independent exact-artifact theorem boundary.

A complete source-to-WASM correctness theorem would support a second result with a larger stated dependency set.  That theorem would connect source semantics, IR semantics, lowering, byte identity, and modeled WASM execution, allowing a source theorem to transport to the artifact.  The current artifact-only path does not require that theorem, and the [Source-Theorem Transport Plan](../plans/theorem-transport.md) keeps the two claims distinct.

## Knowledge-forest retrieval

The knowledge forest selects versioned packages whose LTG catalogs index checked proof assets, tactics, guidance, annotation support, and worked examples.  A proof task starts with the forest, package category indexes, and artifact-derived features, then retrieves selected entry metadata and content as needed.  Category memberships, feature terms, annotation kinds, consumer evidence, exclusions, related entries, declaration names, and tactic records support this selection.

`tools/knowledge check` validates package identities, dependencies, catalog structure, package-local source paths and imports, evidence bindings, and the selected forest.  Promotion asks Lean to build package-local modules and resolve advertised declarations.  `tools/ltg check` and `tools/ltg metrics` retain the detailed catalog and ProofKit checks for the core package, while [Knowledge Forest and Structured LTG](ltg.md) defines retrieval and lifecycle operations.

Narrow material remains in the catalog when it forms a checked worked example with a distinct lesson.  Promotion to shared automatic selection requires recurring use or a reason that the entry describes a common compiler or WASM motif.  Exact-artifact exclusions keep a measured task from retrieving its own proof, while separate forest selections control broader evaluation families.

A completed artifact proof can produce a knowledge package for later proof construction.  That package may retain checked Lean support, guidance, or a worked example, and promotion places the reviewed package in a selectable forest snapshot.  Later proofs still establish their own exact-artifact theorem, while any imported package-local theorem appears in the checked Lean dependency graph.

## Agent and checker boundary

`tools/leanexegen` gives a proof-generation task the frozen formal specification, exact Talos program, selected annotations, ProofKit, a filtered knowledge-forest snapshot, and explicit instructions to iterate with Lean.  The source-generation task and proof-generation task are separate, and the proof task does not receive the source.  The outer process then runs package validation, import checks, artifact identity checks, and independent Lean verification.

The agent may ignore an annotation, knowledge entry, theorem, tactic, or suggested approach when it does not fit the goal.  Acceptance depends on the resulting Lean theorem and package checks rather than on following a prescribed proof script.  Reproof mode freezes the specification, source, and WASM so an experiment can change the selected forest without changing the subject.

## Evaluation

Proof-generation time has the greatest weight because the work seeks practical artifact proofs, but no single timing result determines retention.  Evaluation also considers independent acceptance, LTG retrieval, agent revisions, proof structure, local scaffolding, repeated derivations, shared theorem and tactic use, compiler-derived evidence use, and transfer to another artifact.  Identifier length and raw word bytes do not count as proof complexity because descriptive names often record shared abstraction use.

Experiments preserve accepted, rejected, and censored outcomes.  A fixed-artifact comparison holds the formal specification, source, binary, model, tool versions, task instructions, resource profile, and cache policy constant.  A new demo provides out-of-sample evidence when existing artifacts share the structure targeted by an annotation or theorem.

The current demonstrations show useful transfer for fixed-array wrappers, searches, maps, filters, scalar post-test loops, array folds, frame accessors, allocator composition, and fixed results.  Demo 12 adds a bounded early-exit first-match scan and a variable-length copy-and-shift result over a 2,183-byte artifact containing 597 instructions and five loops.  Its baseline proof used the checked length dispatch, capacity, allocator, result-store, and copy-loop patterns, while constructing the inner search and erase reasoning locally; Stage 5 took 3,907.231 seconds, and the accepted source contains 860 lines, 3,516 whitespace-delimited words, and 39,249 bytes.

The first journal review produced two shared interfaces.  `FixedArrayFindIdxEq.program_spec` executes the exact one-word literal-key first-match loop, while `UInt64Array.At.eraseIdx!_of_reads` reconstructs the erased array from target memory facts after allocation and copying.  The compiler emits and the artifact consumer checks `leanexe.array.find-idx-eq.v1`, and an independently verified annotation package equates Demo 12's frozen search interval with `FixedArrayFindIdxEq.program 8 0`.

An exploratory fixed-artifact reproof retrieved and used both interfaces, rejected the fold support as a mismatch, and completed its artifact theorem in a focused Lean check.  Concurrent editing changed a shared ProofKit module during the run, so the ordinary package gate could not rebuild a consistent dependency set.  The attempt supplies structural evidence but no accepted proof-time measurement.  The accepted baseline remains 3,907.231 seconds, 860 lines, 3,516 words, and 39,249 bytes.

`FixedArrayCopy.program_spec` now executes the complete raw-cell prefix and shifted-suffix loop pair, accepting either ordering of nonoverlapping source and target regions and preserving the target header and source reads.  Its generated `leanexe.array.erase-copy.v1` recipe supplies combined and per-loop equalities, while `eraseIdxProgram_spec` adapts the width-one, source-before-target case to public `Array.eraseIdx!` representation.  A production annotation pass preserved Demo 12's artifact digest, checked the exact nested interval `[53,59)` against `FixedArrayCopy.program 1 8 14 11 12 15`, and passed a separate `leanexegen verify -s` rebuild of the complete package.  The exact loop shape also appears in the CLOB `matchFuel` and `limit` functions at width five, but the current CLOB proofs need stronger global, ownership, and outside-region continuations and do not use the theorem.  A clean fixed-artifact reproof will evaluate the settled support.
