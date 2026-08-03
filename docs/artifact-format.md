# Artifact Verification Format

**Status:** Implemented for twenty registered artifacts.  The schema-three aggregate gate passed on 2026-08-03, and the conformance gate passed with the configured Talos imported-memory warning.  The release record remains a draft until an immutable source revision and its cold-checkout receipt exist.

## Formal Subject and Claim

Artifact verification starts with the exact bytes of one WebAssembly binary.  A Lean `ByteArray` contains those bytes, and a checked file comparison connects that value to the distributed `program.wasm`.  The artifact theorem does not read Lean source, invoke LeanExe, or assume a compiler-generated module model.

The formal path has four boundaries: binary decoding, WebAssembly validation, translation into Talos, and behavioral proof.  Each boundary has an executable check and a proposition that states its meaning.  A closed theorem identifies the validated artifact's Talos module with the cached execution module, while the case registry names the source behavioral theorem proved about that same module.

```lean
theorem artifact_module_eq_cache :
  ∃ raw validated,
    Wasm.Binary.decode artifactBytes = .ok raw ∧
    Wasm.Binary.validate raw = .ok validated ∧
    Wasm.Binary.CoreValid raw ∧
    Wasm.Binary.ValidatedModule.toTalos validated = executionCache
```

## Normative Binary Profile

The binary grammar follows the WebAssembly Core 3.0 specification and binary format version 1.  The initial profile accepts the type, function, memory, global, export, and code sections with section identifiers 1, 3, 5, 6, 7, and 10.  An accepted module contains each present section at most once and in the order prescribed by the WebAssembly binary grammar, and each section parser consumes exactly its declared payload.

The type section accepts function types whose parameters and results contain `i32` and `i64`.  The function section retains every type index, while the code section retains every local declaration group and structured instruction body.  Validation later checks all type indices, the agreement between function and code counts, the accepted function-result arity, and the expanded local count.

The memory section accepts 32-bit limits encoded with flag 0 or 1.  The raw representation retains every declared memory and both bounds, while the initial validator requires exactly one memory and checks its bounds against the WebAssembly page limit.  Imports, shared memory, memory64, and multiple memories lie outside the initial profile.

The global section accepts immutable or mutable `i32` and `i64` globals initialized by a matching scalar constant expression.  The export section accepts function, memory, and global descriptors and retains each UTF-8 name as both bytes and decoded text.  Validation checks initializer types, export-name uniqueness, descriptor indices, and the one-memory restriction.

The code profile consists of `unreachable`, `drop`, structured `block`, `loop`, and `if`, direct branches, `return`, direct calls, local and global access, scalar constants, the integer operations emitted by LeanExe, six memory operations, and memory size or growth.  Structured control accepts empty, `i32`, or `i64` block results.  Memory instructions retain alignment and offset immediates, and memory size or growth retains the memory index that validation restricts to zero.

The decoder rejects custom sections, imports, tables, start functions, elements, data, data counts, tags, unsupported value types, reference types, SIMD, atomics, exception handling, GC types, unsupported opcodes, and every reserved or malformed encoding.  Rejection defines the boundary of the first profile and does not imply that the rejected input violates the full WebAssembly specification.  Extending the profile requires syntax, decoding, validation, translation, soundness proofs, and semantic coverage for each added form.

## Raw Representation

`Wasm.Binary.RawModule` retains the accepted section sequence, function types, declared function type indices, memories, globals, exports, and code bodies.  The representation keeps function declarations separate from bodies because their count and type agreement are validation obligations.  It also keeps local groups compressed and keeps `local.tee` distinct, so decoding does not perform semantic transformations.

Signed constant instructions contain mathematical integers within the signed width accepted by the binary grammar.  A later Talos translation converts those integers to their two's-complement bit patterns.  Names retain their bytes because artifact identity concerns the complete binary, while decoded text supplies WebAssembly export-name comparison.

`Encodes bytes raw` states the accepted declarative binary grammar independently of the executable decoder.  The decoder uses a bounded cursor and requires complete consumption at file, section, function-body, name, and vector boundaries.  `decode_sound` proves that every successful decoder result satisfies `Encodes`.

## Validation and Translation

`CoreValid raw` states the WebAssembly typing and structural rules for the restricted profile.  The executable validator checks function and code agreement, index bounds, local and global types, global mutability, memory requirements, export uniqueness, branch depths, block results, calls, and operand-stack typing.  `validate_sound` connects every successful validation result to `CoreValid` without treating a test corpus as proof.

`ValidatedModule` exposes translation only after validation.  Translation preserves functions, memory, globals, and instruction meanings required by the behavioral specifications; the Talos execution representation omits export lookup data that its semantics never reads.  `local.tee i` translates to the Talos instruction sequence that writes local `i` and reads it again because the current Talos syntax has no separate tee constructor.

## Artifact Package and Manifest

Each immutable proof package has the path `proofs/artifacts/<case>/<sha256>/` and contains `program.wasm` and `manifest.json`.  The SHA-256 directory name and manifest digest identify the external file, while `Project.<Case>.ArtifactBytes` in the proof tree supplies the complete byte value used by the theorem.  A changed byte sequence receives another digest and directory.

Manifest schema three records the package identity and validation profile, the import modules and declarations for embedded bytes, decoded raw data, and the cached execution module, the closed artifact-correctness theorem, and the concrete source behavioral theorems.  It also records both workspace's Lean toolchain, the Talos revision, `verifierSourceSha256`, and any host assumptions that qualify the specification.  Registry validation checks the digest-shaped directory, exact field set, file identities, declaration-name relationships, case registry, toolchain pins, Talos pin, and verifier digest before Lean starts.

`verifierSourceSha256` covers seventeen named normative files: binary syntax, cursor, LEB parser, primitives, decoder, grammar, validity predicate, validator, translator, equality and evidence support, and their six proof modules.  The hash starts with `leanexe-verifier-source-v1` followed by a NUL byte, then consumes each repository-relative path in code-unit order, a NUL byte, its byte length, another NUL byte, and its raw contents.  Utilities, generated package certificates, tests, and cached modules remain outside this digest and enter the release identity or source revision through separate fields.

The release-input digest covers every Lean source under `proofs/talos/lean/Project`, the aggregate module, the recursive local `LeanExe` import closure used by those proofs, both Lake workspaces, toolchain and runtime pins, every registered manifest and binary, conformance configuration, and the exact proof, conformance, identity, and cold-checkout drivers.  The twenty tracked `Program.lean` files enter this digest as untrusted execution caches, while the closed equality theorem prevents their contents from replacing the module decoded from the artifact bytes.  The source revision remains a separate identity for the complete checked repository state, and the cold command requires the selected inputs to match byte-for-byte across the current tree and detached checkout.

The artifact-only command accepts one frozen binary and one registered proof target.  It compares the file with the embedded bytes, verifies the digest and manifest, builds decoding and validation evidence, checks cached-model equality, and checks the behavioral theorem.  The command reports the first failed boundary and runs every Lean child through `tools/leanrun`.

```sh
tools/artifact-proof.js check \
  proofs/artifacts/<case>/<sha256>/program.wasm \
  Project.<Case>.ArtifactTranslation
```

`tools/artifact-proof.js check-artifacts` checks byte identity, embedded bytes, and exact artifact theorems for all registered packages.  `tools/artifact-proof.js check-all` adds every behavioral specification, checks the exact types of the identity, cache-equality, decoder-soundness, validator-soundness, and closed artifact theorems, and audits their logical dependencies.  The declaration audit rejects `sorryAx` and every axiom outside `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, and Lean's theorem-local `native_decide` or `bv_decide` certificate families; neither mode reads source programs, invokes LeanExe, or invokes `wasm-tools`.

## Implementation Status

All twenty registered packages pass the byte-identity, embedded-byte, decoder, validator, exact Talos translation, behavioral-specification, and manifest-declaration boundaries.  `tools/artifact-proof.js check-all` completed under the constrained proof toolchain on 2026-08-03, and `check-artifacts` passed again after signal-aware child-process handling replaced synchronous execution in the Node driver.  These results establish the implemented artifact boundary under the pinned Talos semantics.

The pinned twenty-five-file official execution slice produced 3,853 Talos passes, six known assertion failures, and 627 skipped commands, while Wasmtime 44.0.0 passed every selected file.  The six failures concern imported memory in `memory_grow.wast`: Talos uses the importing declaration's maximum instead of the exported memory instance's maximum.  The gate records their exact rows as an upstream warning outside the accepted no-import profile and treats every changed or additional failure as fatal.

The same gate checks fifteen official invalid modules against exact artifact decoder or validator error constructors.  The cases cover malformed headers and sections, integer overflow, invalid memory limits and alignments, stack underflow, and unused stack results.  This corpus tests the executable classifier independently of the twenty accepted artifacts, while `decode_sound` and `validate_sound` remain the formal evidence for successful results.

The draft release record binds all twenty artifact and package identities, every theorem name, the verifier source digest, the release-input digest, and the tool pins.  Lean 4.31.0 accepts the archived kernel reproduction, and the owner accepts that defect after the recorded local lexical audit; this qualification does not repair the kernel.  The artifact and conformance receipts now bind the expanded 565-file release-input digest; an immutable source revision and a matching cold-checkout receipt remain absent.

## Trusted Base and Evidence

The final claim trusts the selected Lean kernel, the formal grammar and validation propositions, the pinned Talos semantics, the artifact specification, and its stated host assumptions.  File reading and byte comparison connect an external file to the embedded byte value and remain an operational assumption of the command.  The release record identifies every trusted revision and the exact theorem names checked.

LeanExe, its source language, its compiler passes, `wasm-tools`, the WAT decoder, the Talos emitter, Wasmtime, and generated cache files remain outside the theorem.  Official WebAssembly tests and Wasmtime comparisons test the implementation and Talos semantics without replacing the Lean proofs.  The current WAT path remains an independent comparison during migration.

## Normative References

The format definition uses the WebAssembly Core 3.0 [binary module grammar](https://webassembly.github.io/spec/core/binary/modules.html), [binary values](https://webassembly.github.io/spec/core/binary/values.html), [binary instructions](https://webassembly.github.io/spec/core/binary/instructions.html), and [binary conventions](https://webassembly.github.io/spec/core/binary/conventions.html).  Validation follows the specification's [module rules](https://webassembly.github.io/spec/core/valid/modules.html), [validation conventions](https://webassembly.github.io/spec/core/valid/conventions.html), and [validation algorithm](https://webassembly.github.io/spec/core/appendix/algorithm.html).  The [artifact-level verification plan](../plans/artifact-verification.md) defines the implementation order and acceptance gates.
