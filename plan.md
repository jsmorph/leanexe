# Development Plan

This file is the only active project work queue.  The compiler, execution suite, twenty source-driven Talos proofs, twenty exact-artifact packages, annotation generator, ProofKit, structured LTG, and twelve demonstrations already exist.  Detailed plans under `plans/` support unfinished items listed here and do not define separate priorities.

## 1. Reconcile current documentation and release evidence

The documentation describes one implementation and assigns each changing fact to one source of truth.  The release record carries the current input identity, source revision, and successful warm-gate receipts dated 2026-08-13.  Cold verification remains deferred and does not form part of the current work.

- [x] Consolidate navigation, language, compiler, artifact-proof, annotation, and proof-guidance documents.
- [x] Remove superseded plans and experiment reports after migrating current facts and links.
- [x] Standardize demo documentation and replace workspace examples that use `/tmp` with repository-local `./tmp` paths.
- [x] Run local-link, stale-reference, command-example, and whitespace checks over the maintained documentation.
- [x] Refresh `proofs/artifacts/release.json` against the settled release inputs.
- [x] Run the warm artifact-proof and semantic-conformance gates for the refreshed identity.
- [x] Record an immutable source revision for the current release inputs.
- [ ] Complete the cold-checkout gate when cold verification resumes.
- [ ] Require `tools/artifact-release.js check-ready` to pass before describing the release as ready.

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

- [ ] Inventory the current scalar-certificate and emitter-agreement theorems against emitted annotation kinds.
- [ ] Choose one recurring region whose proof still reconstructs facts already known during compilation.
- [ ] Emit a compact certificate or checked equality for that region and verify it against the decoded artifact.
- [ ] Add the resulting theorem, tactic, or guidance to structured LTG with its precise applicability conditions.
- [ ] Test the addition on one development demo and one held-out demo.
- [ ] Record whether the theorem reduces search, explicit scaffolding, Lean checking time, or repeated derivation.

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

[Proof-Grade `f64` Artifact Semantics](plans/f64-artifact-semantics.md) records a deferred extension for exact binary64 execution, integer bit-pattern ABI transport, finite-result kernel theorems, and checked numerical error certificates.  Its first vertical slice requires an explicit design review before implementation.  A later root-plan decision will activate this work.

## Required gates

| Change | Required evidence |
|--------|-------------------|
| Documentation only | `git diff --check`, `tools/check-docs.js`, and command review. |
| Source language or compiler | Focused Lean build through `tools/leanrun`, targeted execution comparisons, `node test/run_all.js`, WAT round trip, and all affected Talos proofs. |
| Exact-artifact verifier | Focused artifact package, `tools/artifact-proof.js check-all`, decoder and validator tests, and conformance checks when semantics change. |
| ProofKit, annotations, or LTG | Focused Lean modules, generated declaration checks, `tools/ltg check`, fixed-artifact package verification, and journal plus telemetry review. |
| Release evidence | Refreshed input identity, warm artifact and conformance receipts, immutable revision, cold-checkout receipt, and `check-ready`. |

## Completion conditions

The next stable point requires current and nonduplicative documentation, a release record that passes identity inspection, and one accepted structurally different array-control-flow demonstration using the maintained annotation and LTG path.  Demo 12 satisfies the demonstration condition.  The stable point also requires one evaluated compiler-theorem-directed artifact-proof increment with an explicit trust boundary and held-out evidence, while repository status, registries, proof inventories, metrics, plans, and release records must agree at that revision.  A later release-ready state will also require the deferred cold-checkout receipt and a successful `check-ready` result.
