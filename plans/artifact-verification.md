# Artifact-Level Verification Plan

**Status:** Formal implementation and warm gates complete; immutable revision and cold-checkout evidence pending as of 2026-08-03.

## Goal

This project will prove properties of an exact WebAssembly binary without relying on its source program or compiler.  Verification will begin with frozen `.wasm` bytes, decode and validate those bytes inside the formal boundary, and prove a behavioral specification over the resulting Talos module.  The compiler, `wasm-tools`, and the Talos source emitter may serve as test or cache-producing tools, but the theorem will not trust their output.

The implemented closed statement exposes decoding, validation, and module identity as separate obligations.  Its existential values prevent a generated Talos module from entering the proof without a successful decode of the artifact bytes.  The registered behavioral theorem applies to `executionCache`, which the final equality identifies with the translation of the validated artifact.

```lean
theorem artifact_module_eq_cache :
  ∃ raw validated,
    Wasm.Binary.decode artifactBytes = .ok raw ∧
    Wasm.Binary.validate raw = .ok validated ∧
    Wasm.Binary.CoreValid raw ∧
    Wasm.Binary.ValidatedModule.toTalos validated = executionCache
```

`artifactBytes` identifies the formal subject.  `Wasm.Binary.decode` connects the bytes to a faithful static module, validation establishes the selected WebAssembly profile, and the final equality connects that module to the registered execution model.  Existing `TerminatesWith` proofs supply behavior for that model and transport across the equality without introducing source or compiler premises.

```text
program.wasm
     │ exact byte import and identity check
     ▼
artifactBytes : ByteArray
     │ checked binary decoder
     ▼
RawModule
     │ complete validation for the accepted profile
     ▼
ValidatedModule
     │ proved erasure
     ▼
Talos Wasm.Module
     │ handwritten weakest-precondition proof
     ▼
ArtifactSpec
```

## Definition of Completion

Artifact-level verification is complete when one command checks an exact `.wasm` file without invoking LeanExe or reading Lean source.  The command must establish byte identity, successful decoding, module validity, equality with any cached Talos model, and the registered behavioral theorem under the pinned proof toolchain.  A separately distributed binary must match the proof package's bytes exactly.

The initial claim will state correctness under the pinned Talos semantics for a module proved to decode from valid WebAssembly bytes.  Conformance tests against the official WebAssembly suite and differential execution under Wasmtime will support the fidelity of Talos semantics, while Talos remains an explicit trusted component.  A theorem relating Talos execution to the official WebAssembly operational semantics belongs to a separate project.

## Scope and Decisions

The first profile covers the core modules currently emitted by `lean-wasm compile`.  Those artifacts use the type, function, memory, global, export, and code sections; one memory; mutable scalar globals; no imports, tables, start function, elements, or data segments; and the instruction forms represented by `LeanExe.Wasm.Instr`.  The decoder and validator reject every unrecognized section, type, opcode, feature, or module shape.

| Decision | Resolution | Required record |
|----------|------------|-----------------|
| Normative format | WebAssembly Core 3.0 binary grammar, restricted to the current core artifact profile and binary format version 1. | Name the specification release and every accepted feature. |
| Semantic claim | Correctness under the pinned Talos semantics for a module proved valid in the restricted WebAssembly profile. | State Talos fidelity as a trusted assumption supported by conformance and differential tests. |
| Decoder location | Keep the decoder, validator, and proofs under `Project.Artifact.Binary` in the proof workspace, with translation into the pinned Talos representation. | Record the seventeen normative verifier sources, their digest, and the Talos revision. |
| Artifact storage | Store each frozen binary in a content-addressed proof package with a SHA-256 manifest. | Treat the exact embedded bytes as the theorem subject and the hash as its external identifier. |
| Cached model | Track generated `Program.lean` as an untrusted elaboration cache after Lean checks equality with decoding the embedded bytes. | Include every cache in the release identity and never accept one without the equality theorem. |
| Kernel | Pin Lean 4.31.0 in both workspaces and record the owner's acceptance of its known defect after the narrow project-source audit. | Record the exact Lean commit, reproduction identity and result, audit command, roots, forbidden identifiers, and audit limitations. |

These decisions produced a proof workflow separate from source compilation.  The source-driven registry still identifies a source module and entry for compiler tests, while the artifact registry identifies a frozen binary, byte digest, validation profile, cached model, specification target, and theorem names.  `tools/artifact-proof.js` reads only the artifact registry and proof workspace.

## Trusted Base

The intended trusted base consists of the selected Lean kernel, the formal statement of the restricted WebAssembly binary grammar and validation rules, the pinned Talos execution semantics, the artifact specification, and the host assumptions stated by that specification.  File input and byte comparison remain an operational boundary between the external `.wasm` file and the embedded byte value checked by Lean.  The proof manifest must identify every trusted component by version or commit.

The compiler, compiler source, compiler IR, `wasm-tools print`, the WAT decoder, the Talos model emitter, and Wasmtime remain outside the formal artifact theorem.  They may provide independent comparison and execution tests.  A failure in one of those tools must not allow a model different from `Wasm.Binary.decode artifactBytes` to enter the proof.

## Formal Components

### Binary Grammar

Define a faithful static syntax that retains every fact needed for validation before translation to Talos's runtime-oriented module.  The syntax must retain function types, global types and mutability, memory limits, export descriptors, section order, function type indices, local declarations, block types, instruction immediates, and exact function bodies.  Erase static information only after validation succeeds.

Define an `Encodes : ByteArray → RawModule → Prop` relation from the selected WebAssembly binary grammar.  Keep this declarative relation separate from the executable decoder so decoder correctness does not reduce to restating its implementation.  The accepted profile may reject valid WebAssembly constructs outside its scope, but every accepted byte sequence must satisfy the normative grammar.

The executable decoder should use an explicit byte cursor and return the unused suffix or require complete consumption at the top level.  It must check the magic and version fields, section identifiers, section order and uniqueness, declared section sizes, vector lengths, integer widths, function-body sizes, structured-control termination, and complete-file consumption.  Each component parser should receive a soundness theorem that composes into `decode_sound`.

```lean
theorem decode_sound
    (h : Wasm.Binary.decode bytes = .ok module_) :
    Encodes bytes module_
```

### Validation

Define `CoreValid : RawModule → Prop` from the selected WebAssembly validation rules and implement a decidable validator against it.  The validator must cover type-index bounds, function and code count agreement, function signatures, local and global indices, global mutability, memory presence and limits, export uniqueness and index validity, calls, branches, block result types, function results, loads, stores, and operand-stack typing.  Unsupported constructs must reject rather than pass through an incomplete checker.

The current Talos `Module.validate` cannot serve as this validator.  It explicitly implements a partial set of structural and GC checks, and its straight-line stack checker accepts control flow or instructions it does not model.  The new validator must prove soundness for every accepted construct in the restricted profile.

```lean
theorem validate_sound
    (h : Wasm.Binary.validate module_ = .ok validated) :
    CoreValid module_
```

`ValidatedModule` should contain the raw module and its validity evidence or expose a constructor available only through validation.  Translation to the existing Talos `Wasm.Module` should consume `ValidatedModule`, preserving functions, exports, memory, globals, and instruction meanings.  A translation theorem must state the relevant field equalities used by the existing artifact proofs.

### Artifact Identity

The formal proof should contain the exact artifact bytes as a Lean value.  A small byte-import step may generate that literal from `program.wasm`, but the gate must compare the literal's bytes with the input file and record the file's SHA-256.  The digest identifies the artifact in manifests and release records; the full byte value remains the subject of the theorem.

Each immutable proof package stores the frozen binary and its manifest in a content-addressed directory.  The corresponding Lean modules remain in the proof tree, where Lake can compile them by module name.  The artifact registry selects one package and proof target for each case.  The package uses this layout:

```text
proofs/artifacts/<case>/<sha256>/
  program.wasm
  manifest.json
```

`Project.<Case>.ArtifactBytes` contains the exact embedded bytes and their recorded length and digest.  `Project.<Case>.Program` contains the cached Talos module used by the behavioral proof, while `Project.<Case>.ArtifactTranslation` proves that translation of the decoded raw cache equals that module.  The package manifest names these modules and the identity, decode, validation, cache-equality, and behavioral theorems checked by the gate.

### Behavioral Specification

Retain the current weakest-precondition proof architecture after the binary and validation boundary.  A primary theorem should quantify over meaningful inputs and state termination, return values, traps where applicable, memory changes, allocator state, ownership, and frame conditions needed by callers.  Structural facts such as the absence of imports, exact exports, memory limits, and determinism should come from decidable module checks rather than repeated instruction proofs.

The specification remains a human-reviewed part of the trusted statement.  The artifact verifier cannot determine whether a weak postcondition captures the intended application behavior.  Each proof inventory entry must state the theorem's premises, outputs, memory effects, invalid-input behavior, and host assumptions.

## Work Plan

| Phase | Implementation | Acceptance gate | Status |
|-------|----------------|-----------------|--------|
| 0. Proof baseline | Record the selected Lean kernel disposition, finish the heavy proof divisions, and close the current aggregate gate. | Clean aggregate proof result under the selected kernel and resource policy. | Complete on 2026-08-02 under Lean 4.31.0; the release records the accepted known defect and narrow lexical audit |
| 1. Artifact specification | Write the restricted profile, trusted-base statement, `RawModule`, `Encodes`, `CoreValid`, artifact manifest schema, and final theorem signature. | Design review resolves every decision in the table above. | Complete on 2026-08-01 |
| 2. Binary primitives | Implement byte cursors, fixed bytes, unsigned and signed LEB128, names, vectors, sizes, and bounded sub-parsers. | Unit tests cover boundaries, truncation, accepted overlong values, and trailing bytes; component soundness lemmas build. | Complete on 2026-08-01 |
| 3. Module decoder | Implement the six accepted sections and the current instruction set, with complete structured-control parsing. | All twenty frozen artifacts decode; corruptions, truncations, bad section sizes, duplicate sections, and unsupported opcodes reject. | Complete on 2026-08-01 |
| 4. Decoder proof | Prove component and top-level soundness against `Encodes`. | `decode_sound` builds without axioms or `sorry`. | Complete on 2026-08-01 |
| 5. Validator | Implement complete stack, index, mutability, memory, export, and module checks for the profile. | Official invalid examples within the profile and repository-generated invalid fixtures reject; `validate_sound` builds. | Complete on 2026-08-01; fifteen exact official invalid cases passed on 2026-08-02. |
| 6. Talos translation | Translate `ValidatedModule` to `Wasm.Module` and generate checked cache-equality theorems. | Every translated module equals the current decoded Talos model for all twenty artifacts. | Complete on 2026-08-01 |
| 7. Artifact gate | Add an artifact registry and an artifact-only proof command. | The command never invokes LeanExe or `wasm-tools`; it checks bytes, hash, decode, validation, cache equality, and the selected specification. | Complete on 2026-08-01 |
| 8. Proof migration | Move the twenty existing artifact proofs to frozen byte packages without weakening their statements. | Focused proof checks and the aggregate artifact gate pass for every case. | Complete on 2026-08-02 |
| 9. Conformance and release evidence | Run the supported official WebAssembly tests, differential Wasmtime cases, cold-checkout setup, and manifest verification. | Release manifest records the exact artifacts, tool pins, theorem names, commands, and results. | Warm conformance and artifact receipts complete; immutable revision and cold result pending |

`tools/artifact-proof.js check-all` passed all twenty registered packages on 2026-08-03 under the standard cgroup, CPU, priority, serialization, and timeout policy.  The run checked file identity, embedded bytes, exact declaration types, decoder and validator soundness dependencies, closed translation equalities, every behavioral specification, every theorem named by the manifests, and each theorem's permitted axiom dependencies.  Phase 9 now contains only the immutable-revision and cold-checkout conditions.

`proofs/artifacts/release.json` binds the registry and package-manifest hashes, each binary digest, every theorem name, all tool pins, and the canonical release-input digest.  That digest now includes every project proof source, tracked `Program.lean` execution cache, recursive local root-package import, Lake definition, selected package, and verification driver, correcting the earlier warm-only identity that omitted clean-checkout proof inputs.  The release records Lean 4.31.0 at commit `68218e876d2a38b1985b8590fff244a83c321783`, acceptance of the archived reproduction, and the narrow lexical source audit that qualifies the owner's disposition.

`tools/artifact-conformance.js check` pins CodeLib revision `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`, official WebAssembly testsuite revision `9233a0a8d5920a8d32358ee915a3662ff3385029`, and Wasmtime 44.0.0.  Its twenty-five-file execution slice produced 3,853 Talos passes, six known assertion failures, and 627 skipped commands, while Wasmtime passed all twenty-five files with `function-references=y`.  Talos produced no cascades, decoder errors, interpreter errors, or fuel exhaustion in the selected slice.

The gate also extracts fifteen official `assert_invalid` and `assert_malformed` modules selected by exact file, assertion kind, and source line.  Every module matched its configured artifact decoder or validator stage and exact error constructor on 2026-08-03.  These cases supply independent executable evidence for malformed headers, section errors, integer width, alignment, operand stacks, and memory limits without becoming premises of `decode_sound` or `validate_sound`.

All six Talos failures occur in `memory_grow.wast`.  Talos copies an imported memory into the importing store but applies the importing declaration's six-page maximum, allowing memory exported with a five-page maximum to grow to six pages.  The artifact profile rejects imports, so the gate accepts only those six exact rows as an upstream warning, removes the warning when upstream repairs them, and rejects any changed or additional failure.  The [Talos imported-memory defect report](../docs/telos-bug.md) records the provenance, execution path, scope, and repair boundary.

## Artifact-Only Command

The implemented interface accepts a frozen binary and one registered proof target.  Those inputs determine the artifact identity and the theorem to build.  The command has this form:

```sh
tools/artifact-proof.js check \
  proofs/artifacts/example/<sha256>/program.wasm \
  Project.Example.Spec
```

The command verifies the manifest and byte digest, checks the embedded byte literal, builds the decoder and validation certificate, checks equality with the cached model, and builds the specification target.  It runs every Lean-based child through `tools/leanrun`, which applies the repository's systemd memory, CPU, priority, I/O, timeout, and serial-execution policy.  The Node driver forwards interruption and termination signals to the active child process group, while a proof failure identifies the first boundary: identity, decoding, validation, translation, cache equality, or behavioral proof.

The aggregate mode verifies registry consistency before checking artifacts serially.  It rejects an unregistered proof target, a changed binary, a stale cached model, a missing validity theorem, or a manifest whose theorem names disagree with the proof modules.  Migration computes every replacement first and rolls back applied replacements after a write failure, so a failed migration cannot leave a partially updated package set.

## Tests and Evidence

Decoder tests should include every accepted integer boundary, each instruction opcode and immediate form, nesting of blocks, loops, and conditionals, section-size mismatches, premature end-of-file, duplicate or out-of-order sections, invalid function-body lengths, invalid UTF-8 names, and unsupported features.  Mutation tests provide diagnostic coverage but do not replace `decode_sound`.  The twenty current artifacts provide integration cases across scalar code, loops, arrays, runtime allocation, retain, release, and recursive calls.

Validator tests should cover stack underflow, wrong operand types, wrong block results, invalid branch depths, local and global index errors, writes to immutable globals, missing memory, invalid calls, duplicate exports, mismatched function and code sections, and invalid limits.  The supported portion of the official WebAssembly validation corpus should run as an independent compatibility gate.  Every rejected construct must have one stable diagnostic category and a location when the decoder can provide one.

Semantic tests should run the supported official execution corpus through Talos and compare selected artifacts with Wasmtime.  Record coverage by instruction form rather than one aggregate pass count, because an untested instruction weakens every artifact containing it.  The proof inventory should identify the semantic features used by each artifact.

## Migration

The migration began with `gcd`, then covered `fold_sum`, the allocator and release cases, the LEB128 encoder, and the CLOB cases.  Each of the twenty packages now has frozen bytes, a manifest, embedded bytes, decoded and validated caches, an exact translation theorem, and the existing behavioral specification.  The behavioral statements and generated function indices did not change during migration.

The current WAT path remains an independent compiler comparison.  Artifact verification neither invokes it nor depends on its output, and the exact-translation gate has passed for all twenty packages.  Removal of the WAT comparison belongs to later compiler-workflow maintenance rather than artifact-proof soundness.

## Relationship to Emitter Work

The emitter restructuring serves compiler verification by relating compiler structure to emitted bytes.  Artifact-level verification starts at the bytes, so it should depend on the binary decoder and validator rather than on `assemble`, `serialize`, or `toTalos`.  This ordering keeps the compiler outside the artifact theorem.

After the artifact verifier is complete, the emitter can use it as an independent check.  A compiler theorem may prove that serialization produces bytes decoded as the compiler's structured module, while the artifact theorem continues to mention only those bytes and the validated Talos module.  The two results then compose without making compiler correctness a premise of artifact correctness.

## Relationship to Source-Theorem Transport

The [Source-Theorem Transport Plan](theorem-transport.md) depends on this plan for exact-byte import, decoding, validation, and translation into Talos.  It adds a kernel-checked source-to-IR certificate, a proved scalar IR lowering, and full-module equality between that lowering and the module decoded from the artifact.  Those results compose an existing theorem about a Lean function with a theorem about the exact artifact's scalar entry point.

Artifact verification remains useful without source code, an IR value, or a compiler.  Source-theorem transport uses the artifact boundary but does not replace the handwritten artifact specifications covered by this plan.  Keeping the plans separate allows an artifact recipient to check a behavioral theorem without accepting the source program or any claim about how the artifact was produced.

## References

The normative format and validation references are the [WebAssembly Core 3.0 specification](https://webassembly.github.io/spec/core/), its [binary-format grammar](https://webassembly.github.io/spec/core/binary/), its [module binary grammar](https://webassembly.github.io/spec/core/binary/modules.html), and its [validation algorithm](https://webassembly.github.io/spec/core/appendix/algorithm.html).  Repository implementation context appears in [Verifying a Program](../docs/verifying.md), [Emitter Restructuring](../docs/emitter.md), [Module Guarantees and the Road to Them](../docs/guarantees.md), [Talos Proofs](../proofs/talos/README.md), and the [Source-Theorem Transport Plan](theorem-transport.md).  Decisions, failed approaches, and completed gate results belong in `devnotes.md` as the work proceeds.
