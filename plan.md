# Development Plan

This file is the only active project work queue.  The compiler, execution suite, twenty source-driven Talos proofs, twenty exact-artifact packages, annotation generator, ProofKit, structured LTG, and twelve demonstrations already exist.  Detailed plans under `plans/` support unfinished items listed here and do not define separate priorities.

## 1. Reconcile current documentation and release evidence

The documentation describes one implementation and assigns each changing fact
to one source of truth.  The last accepted warm evidence, now historical,
carried input digest
`5de9678970b1a9b74d50c1407457423a7fa6eabd3f430f56cfdc0e407af2b7e5`, source
revision `0e0d752904fc90dee3ef3511ffab91f3d358c1ed`, and successful receipts dated
2026-08-26.  The current draft release record identifies the Lean 4.34.0-rc2 and
Talos `fda69ca67a81ea4f1fa4e376bdc5861d9fe5479a` inputs, but its warm receipts are
pending and `sourceRevision` is null.  Cold verification remains deferred and
does not form part of the current work.

- [x] Consolidate navigation, language, compiler, artifact-proof, annotation, and proof-guidance documents.
- [x] Remove superseded plans and experiment reports after migrating current facts and links.
- [x] Standardize demo documentation and replace workspace examples that use `/tmp` with repository-local `./tmp` paths.
- [x] Run local-link, stale-reference, command-example, and whitespace checks over the maintained documentation.
- [x] Refresh the prior `proofs/artifacts/release.json` identity and preserve its
      2026-08-26 evidence as historical provenance.
- [x] Run the prior warm artifact-proof and semantic-conformance gates.
- [x] Record immutable source revision
      `0e0d752904fc90dee3ef3511ffab91f3d358c1ed` for those historical inputs.
- [ ] Record migrated warm receipts and an immutable source revision after the
      pre-FP `fda69ca` compatibility gates pass.
- [ ] Complete the cold-checkout gate when cold verification resumes.
- [ ] Require `tools/artifact-release.js check-ready` to pass before describing the release as ready.

The 2026-08-26 warm artifact gate passed all twenty packages.  The conformance gate matched fifteen expected invalid-module classifications, produced 3,853 Talos passes, six configured failures, 627 skips, no cascades, decoder errors, interpreter errors, or fuel exhaustion, and passed all twenty-five files under Wasmtime.  The separate source-driven aggregate also passed all twenty registered cases.

## 2. Validate annotation-directed proof support on a new shape

The existing fold demonstrations use addition, multiplication, and XOR over closely related generated control flow.  Demo 12 instead searches a bounded array for its first zero, returns the input when no zero exists, and otherwise allocates a result through the emitted copy-and-shift path.  Its frozen request requires `Array.findIdx?` and `Array.eraseIdx!`, providing an early-exit search and a value-dependent result shape for the current annotation, ProofKit, LTG, and journaling path.  Independent verification accepted its exact 2,183-byte artifact proof after 3,907.231 seconds of Stage 5 work.

- [x] Select the bounded first-zero removal program as the structurally different evaluation.
- [x] Generate and independently accept a direct artifact proof without changing the frozen WASM.
- [x] Review the journal, proof, telemetry, retrieved LTG entries, annotations, and agent revisions together.
- [x] Retain general or credible recurring abstractions, while classifying narrow material as checked worked examples.
- [x] Add checked search, erase reconstruction, and exact copy-loop interfaces with matching compiler annotations and structured LTG entries.
- [x] Run a clean fixed-artifact reproof against settled ProofKit inputs, then compare proof-generation time and proof structure with the retained baseline without imposing a single timing threshold.

The clean reproof preserved artifact digest `7cdd8adba75d4f076d0a142f824a19a0d34d6a5cedd1a810a417a7fc5789f7b6`, and a separate `tools/leanexegen verify -s` invocation accepted the measured package before the follow-up ProofKit changes.  Stage 5 took 3,987.145392 seconds against the 3,907.231311-second baseline, an increase of 2.045 percent, while the accepted proof fell from 860 to 607 lines, 3,516 to 2,587 words, 39,249 to 28,874 bytes, and 47 to 38 journaled checks.  Seven LTG entries were used and none rejected, while `FixedArrayFindIdxEq.program_spec` and `FixedArrayCopy.eraseIdxProgram_spec` removed all local search, prefix-copy, and shifted-suffix loop invariants.  The journal then led to shared theorems for the dynamic local length store and encoded-index comparison with one.  Erase setup and branch-aware result transfer remain under review.

This phase promotes an annotation recipe or LTG entry only when its statement describes a recurring compiler or WASM motif and transfers beyond one program.  Specific checked examples remain searchable when they teach a distinct proof technique.  Automatic selection requires stronger recurring evidence than catalog retention.

## 3. Extend compiler-theorem-directed artifact proving

`LeanExe.Wasm.ScalarCertificate` already proves selected equalities between IR emission and structured WASM instruction sequences.  Annotation generation uses those equalities indirectly when it emits checked region declarations and proof recipes.  The next increment should determine whether a modest compiler theorem can remove or select a meaningful WAT-level proof step while the final theorem continues to concern exact decoded bytes.

- [x] Inventory the current scalar-certificate and emitter-agreement theorems against emitted annotation kinds.
- [x] Choose the recurring zero-or-index-plus-one decoder, which appears in Demo 12, ClobCancel, and twice in ClobDepth.
- [x] Emit a compact certificate or checked equality for that region and verify it against the decoded artifact.
- [x] Add the resulting theorem and guidance to structured LTG with its precise applicability conditions.
- [x] Test the addition on Demo 12 and the distinct ClobDepth proof.
- [x] Record its effect on explicit control reasoning, proof source, Lean checking, and available timing evidence.

The Demo 12 annotation pass preserved the 2,183-byte artifact and digest `7cdd8adba75d4f076d0a142f824a19a0d34d6a5cedd1a810a417a7fc5789f7b6`, generated the exact region equality, and passed separate package verification.  It reused the accepted behavior proof, so it provides no fresh retrieval or proof-generation measurement.  The compiler certificate, neutral ProofKit theorem, and generated LTG declaration check also passed independently.

The ClobDepth compiler run preserved its registered 3,602-byte artifact and digest `d6fe056853750dd985e3d0cd03e6ec488ae98a9791d7b5d53baac95bd352b68f`, while the complete sidecar matched the cached Talos program.  Its proof now applies `EncodedIndexDecoder.program_spec` at two different local layouts, removing four decoder-specific `wp_iff_cons` applications and four associated `wp_run` calls.  The source grew by 21 lines because it supplies region decomposition and theorem premises without a generated annotation adapter, and no comparable proof-generation timing exists.  `tools/talos-proof.js check clob_depth` accepted the complete source-driven proof.

The source theorem and compiler remain optional proof-construction inputs.  Independent artifact verification must continue to work when the source is unavailable or when no complete compiler-correctness theorem exists.  [Source-Theorem Transport](plans/theorem-transport.md) describes the larger refinement theorem that may follow successful narrow experiments.

## 4. Develop cumulative proof knowledge

The next increment tests whether one accepted proof can make a later artifact proof easier.  The implementation should remain small while this claim is unsettled.  Independent artifact verification remains the authority, while the catalog, forest, and learning commands organize proof inputs and evidence.

- [x] Derive compiler-motif task features from validated annotations instead of separate instruction matchers.
- [x] Give the learning task the generated annotation equalities, exact adapters, accepted proof, selected knowledge, journal, and telemetry.
- [x] Give each learning attempt an explicit identity so repeated attempts over one proof remain separate artifacts.
- [x] Allow proposed checked knowledge to import selected package-local modules and record its direct package dependencies.
- [x] Add an axiom report to the existing Lean check for promoted declarations.
- [x] Run one cross-artifact exercise and record whether the later proving agent selects, uses, or rejects the learned entry.
- [x] Evaluate the generated setup-frame equality on a fixed artifact using proof time, proof structure, and the agent journal.
- [x] Test cumulative proof support on Demo 12's structurally different allocating and copy-shift artifact.
- [x] Correct current LTG measurements and keep historical experiments in benchmark records and the retrospective.

Routine checks cover catalog generation and consistency, forest composition and filtering, and Lean checking of promoted declarations.  The artifact verifier remains the final proof gate.  Synthetic scale searches and malformed-input cases belong in experiments unless they expose a recurring development failure.

Digest hardening, strict archive validation, file-level exclusion policy, content-addressed dependency identities, category sharding, forest-wide indexes, and archived-package migration remain deferred.  Current scale does not require those mechanisms.  They become active work when package sources, catalog size, or observed failures require them.

Proof-generation time remains the primary optimization measure, while proof structure and size remain material.  Counts should distinguish local scaffolding from references to shared declarations, because longer shared theorem names do not make a proof more complex.  Retrieval success, revisions, independent acceptance, and cross-artifact use remain part of every evaluation.

## 5. Extend compiler and runtime semantics when programs require it

The completed CLOB work established input-generic theorems for `quote`, `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, `market`, and `depth`.  Shared runtime proofs cover allocation, reference counting, fixed arrays, recursive teardown, and the ownership shapes used by those artifacts.  Further compiler work should begin from a reduced accepted-program requirement or a proof boundary exposed by current artifacts.

Current candidates include broader explicit-release analysis, shared interior ownership, recursive array-node teardown, and source forms that require a new specialization boundary.  Each candidate needs a reduced source fixture, source comparison, generated-WASM execution test, ownership report where applicable, and the relevant aggregate proof gates.  A feature does not enter the accepted language until the specification, manual, diagnostics, and tests agree with its implementation.

[Proof-Grade Floating-Point Artifact Semantics](plans/f64-artifact-semantics.md) records the active `talosfp` work described in phase 7.  It reuses Talos's proof-visible IEEE32 and IEEE64 arithmetic while preserving LeanExe's independent exact-byte boundary and integer bit-pattern ABI.

## 6. Establish a self-hosted WebAssembly emitter

The first self-hosting increment moves only final WebAssembly binary serialization into a LeanExe-compiled module.  A canonical module image records the already-lowered library-mode functions, locals, exports, globals, memory, and structured instruction streams.  A pure emitter compiled by the existing native compiler consumes that image as bytes and returns the exact WebAssembly bytes.  [Self-Hosted WebAssembly Emitter](plans/self-hosted-emitter.md) defines the boundary and bootstrap gates.

- [x] Define and validate a canonical versioned module-image format at the final structured-instruction boundary.
- [x] Refactor native library-mode emission through that image without changing any registered artifact bytes.
- [x] Implement a pure `ByteArray -> Except ByteArray ByteArray` image emitter inside the accepted LeanExe subset.
- [x] Compile the emitter to WebAssembly and require it to reproduce its own complete module byte for byte.
- [x] Require native and WebAssembly emission to agree on every registered compiler case and on malformed-image rejection tests.
- [x] Record the exact bootstrap revisions, image identity, artifact digests, host assumptions, and verification receipts.

This phase establishes a self-hosted binary emitter, not a source- or IR-self-hosted compiler.  Lean remains responsible for parsing, elaboration, checking, extraction, ownership analysis, and lowering.  A fixed point is an engineering bootstrap result rather than a compiler-correctness theorem, and independent exact-artifact verification remains authoritative for behavioral claims.

## 7. Bring proof-grade Talos floating point to LeanExe

The `talosfp` branch starts from the `selfhost` branch tip and moves the native
compiler and proof workspace to exact Lean 4.34.0-rc2.  The self-hosted emitter
is experimental and is not part of this implementation or its validation
path.  Its checks may be run separately when work explicitly targets that
experiment, but they do not block floating-point work.  The detailed
[floating-point plan](plans/f64-artifact-semantics.md) fixes the ownership,
bit-pattern ABI, migration sequence, exact-binary profile, first guarded kernel,
and acceptance gates.

- [x] Migrate and validate the native compiler under exact Lean 4.34.0-rc2 while preserving all twenty registered artifact bytes.
- [ ] Move the existing proof corpus through pre-FP Talos `fda69ca`, then immutable FP revision `87e3aa5`, without regressing integer artifacts.
- [ ] Extend the independent binary decoder, validator, validity proof, and Talos translation with internal f64 add, multiply, and reinterpretation.
- [ ] Add restricted `UInt64` bit-pattern intrinsics and exact structured lowering while retaining the public integer ABI.
- [ ] Prove an exact scalar multiplication artifact and a guarded two-term dot artifact with a finite result and explicit accumulated real-error bound.
- [ ] Prove a generated runtime-length dot artifact with absolute, gamma-times-mass, and condition-number contracts.
- [ ] Prove a generated affine or Horner artifact and retain reusable ProofKit, annotation, certificate, and LTG support justified by both kernels.
- [ ] Expand the admitted operations to representative division, square root, and f32 uses; update maintained documentation and active release evidence.

Native floating-point execution and Wasmtime remain regression tools.  Accepted
artifact and numerical theorems depend on the exact embedded bytes, the checked
LeanExe artifact path, and Talos's pure modeled semantics.

As of 2026-09-03, the pre-FP `fda69ca` migration is in progress.  The
dependency pin, typed control metadata, function type-index handling,
`local.tee` support, regenerated program caches, and the compatibility repairs
found so far are implemented.  Every large application proof root now passes
under exact Lean 4.34.0-rc2.  A subsequent standalone-module sweep exposed
compatibility failures in `Project.ProofKit.FixedArrayEqNode` and
`Project.ProofKit.FixedArrayAllocator`; both have been repaired and pass their
focused builds.  `Project.ProofKit.LTGCheck`, `Project.PairFree.Probe`, the
translator metadata tests, and the complete 3,674-job `Project` aggregate now
pass as well.  The first full exact-artifact run exposed one omitted migration
boundary: raw-byte translation did not preserve the regenerated module's GC
function-type mirror, non-function exports, or proof-visible global metadata.
The shared translator now preserves those fields; a focused metadata regression
and `Project.Gcd.ArtifactTranslation` pass.  The next checkpoint reruns all
twenty exact-artifact packages, followed separately by conformance, runtime,
identity, and axiom gates before the pre-FP migration row is checked.  No
floating-point opcode or intrinsic work has started.

## Required gates

| Change | Required evidence |
|--------|-------------------|
| Documentation only | `git diff --check`, `tools/check-docs.js`, and command review. |
| Source language or compiler | Focused Lean build through `tools/leanrun`, targeted execution comparisons, `node test/run_all.js`, WAT round trip, and all affected Talos proofs. |
| Self-hosted emitter | Native/image byte equality, Stage 1/Stage 2 self-reproduction, registered-corpus equality, malformed-image tests, two-host execution, and all source-language/compiler gates. |
| Exact-artifact verifier | Focused artifact package, `tools/artifact-proof.js check-all`, decoder and validator tests, and conformance checks when semantics change. |
| ProofKit, annotations, or LTG | Focused Lean modules, generated declaration checks, `tools/ltg check`, fixed-artifact package verification, and journal plus telemetry review. |
| Release evidence | Refreshed input identity, warm artifact and conformance receipts, immutable revision, cold-checkout receipt, and `check-ready`. |

## Completion conditions

The next floating-point stable point requires exact Lean 4.34.0-rc2, preservation
of the prior native compiler, integer proof, and artifact identities or an
explicit review of each deliberate change, and independently accepted scalar,
guarded fixed-kernel, runtime-length dot, and affine or Horner artifact proofs.
Their public numerical theorems must expose every domain and overflow-exclusion
assumption, pass axiom audits, and depend only on pure modeled semantics.  The
repository status, registries, proof inventories, plans, documentation, active
release evidence, and pushed `talosfp` tree must agree at that revision.  A
release-ready state still additionally requires the deferred cold-checkout
receipt and a successful `check-ready` result.
