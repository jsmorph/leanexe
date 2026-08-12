# Development Plan

This file is the only active project work queue.  The compiler, execution suite, twenty source-driven Talos proofs, twenty exact-artifact packages, annotation generator, ProofKit, structured LTG, and eleven demonstrations already exist.  Detailed plans under `plans/` support unfinished items listed here and do not define separate priorities.

## 1. Reconcile current documentation and release evidence

The documentation now describes one implementation and assigns each changing fact to one source of truth.  The release record carries the current input identity and successful warm-gate receipts dated 2026-08-11.  The remaining work in this phase consists of immutable revision selection and the cold-checkout gate.

- [x] Consolidate navigation, language, compiler, artifact-proof, annotation, and proof-guidance documents.
- [x] Remove superseded plans and experiment reports after migrating current facts and links.
- [x] Standardize demo documentation and replace workspace examples that use `/tmp` with repository-local `./tmp` paths.
- [x] Run local-link, stale-reference, command-example, and whitespace checks over the maintained documentation.
- [x] Refresh `proofs/artifacts/release.json` against the settled release inputs.
- [x] Run the warm artifact-proof and semantic-conformance gates for the refreshed identity.
- [ ] Record an immutable source revision and complete the cold-checkout gate.
- [ ] Require `tools/artifact-release.js check-ready` to pass before describing the release as ready.

## 2. Validate annotation-directed proof support on a new shape

The existing fold demonstrations use addition, multiplication, and XOR over closely related generated control flow.  Their evidence supports shared frame, allocation, traversal, and result-construction interfaces, but it does not establish transfer to a different fold structure.  The next demonstration must freeze its request, specification, source, and WASM before receiving current annotation, ProofKit, LTG, and journaling support.

- [ ] Select a fold whose accumulator layout or scalar control differs structurally from Demos 9–11.
- [ ] Generate and independently accept a direct artifact proof without changing the frozen WASM.
- [ ] Review the journal, proof, telemetry, retrieved LTG entries, annotations, and agent revisions together.
- [ ] Retain general or credible recurring abstractions, while classifying narrow material as checked worked examples.
- [ ] Compare proof-generation time and proof structure with the relevant retained evidence without imposing a single timing threshold.

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

## 4. Maintain the proof knowledge base as an artifact

Structured LTG is a checked, versioned knowledge base rather than prompt text copied into every task.  Its categories, metadata, declarations, tactics, worked examples, exclusions, generated indexes, task bundle, and metrics must remain internally consistent.  Every proof iteration must use journals and telemetry to inform annotations, shared lemmas, tactics, guidance, retrieval instructions, and journal instructions.

- [ ] Run `tools/ltg check` whenever catalog metadata or indexed Lean support changes.
- [ ] Update the dated metrics snapshot when the catalog or ProofKit inventory changes materially.
- [ ] Expand categories and entries in response to recurring proof shapes rather than demo names.
- [ ] Preserve accepted, rejected, and censored proof-generation evidence with fixed-artifact identities.
- [ ] Add out-of-sample demonstrations when existing examples cannot distinguish transfer from specialization.

Proof-generation time remains the primary optimization measure, while proof structure and size remain material.  Counts should distinguish substantive local scaffolding from references to shared declarations, because longer shared theorem names do not make a proof more complex.  Retrieval success, revisions, independent acceptance, and cross-demo applicability remain part of every evaluation.

## 5. Extend compiler and runtime semantics when programs require it

The completed CLOB work established input-generic theorems for `quote`, `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, `market`, and `depth`.  Shared runtime proofs cover allocation, reference counting, fixed arrays, recursive teardown, and the ownership shapes used by those artifacts.  Further compiler work should begin from a reduced accepted-program requirement or a proof boundary exposed by current artifacts.

Current candidates include broader explicit-release analysis, shared interior ownership, recursive array-node teardown, and source forms that require a new specialization boundary.  Each candidate needs a reduced source fixture, source comparison, generated-WASM execution test, ownership report where applicable, and the relevant aggregate proof gates.  A feature does not enter the accepted language until the specification, manual, diagnostics, and tests agree with its implementation.

## Required gates

| Change | Required evidence |
|--------|-------------------|
| Documentation only | `git diff --check`, `tools/check-docs.js`, and command review. |
| Source language or compiler | Focused Lean build through `tools/leanrun`, targeted execution comparisons, `node test/run_all.js`, WAT round trip, and all affected Talos proofs. |
| Exact-artifact verifier | Focused artifact package, `tools/artifact-proof.js check-all`, decoder and validator tests, and conformance checks when semantics change. |
| ProofKit, annotations, or LTG | Focused Lean modules, generated declaration checks, `tools/ltg check`, fixed-artifact package verification, and journal plus telemetry review. |
| Release evidence | Refreshed input identity, warm artifact and conformance receipts, immutable revision, cold-checkout receipt, and `check-ready`. |

## Completion conditions

The next stable point requires current and nonduplicative documentation, a release record that passes identity inspection, successful warm and cold release gates, and one accepted structurally different fold demonstration using the maintained annotation and LTG path.  It also requires one evaluated compiler-theorem-directed artifact-proof increment with an explicit trust boundary and held-out evidence.  Repository status, registries, proof inventories, metrics, plans, and release records must agree at that revision.
