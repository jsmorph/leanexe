# Development Plan

This file is the only active project work queue.  The compiler, execution suite, twenty-six completed source-driven Talos proofs, twenty-one exact-artifact packages, annotation generator, ProofKit, structured LTG, and twelve demonstrations already exist.  The fixed Euler-step source proof and decoded-real numerical certificate are complete; the step still needs its separate exact-byte package and verified data publication.  Detailed plans under `plans/` support unfinished items listed here and do not define separate priorities.

## 1. Reconcile current documentation and release evidence

The documentation describes one implementation and assigns each changing fact
to one source of truth.  The last accepted warm evidence, now historical,
carried input digest
`5de9678970b1a9b74d50c1407457423a7fa6eabd3f430f56cfdc0e407af2b7e5`, source
revision `0e0d752904fc90dee3ef3511ffab91f3d358c1ed`, and successful receipts dated
2026-08-26.  The current draft release record identifies the Lean 4.34.0-rc2 and
Talos `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47` inputs.  After the fixed-step
proof, its current release-input digest is
`dfad5b82317c9ca0a67e6692ecb872457e6d6406cd9d6bad90e1333a29c1ec11`.
The preceding 2026-09-04 aggregate artifact receipt is historical for an older
input identity; aggregate artifact proof, semantic conformance, immutable
source revision, and cold checkout are the four current blockers.  Cold
verification remains deferred and does not form part of the current work.

- [x] Consolidate navigation, language, compiler, artifact-proof, annotation, and proof-guidance documents.
- [x] Remove superseded plans and experiment reports after migrating current facts and links.
- [x] Standardize demo documentation and replace workspace examples that use `/tmp` with repository-local `./tmp` paths.
- [x] Run local-link, stale-reference, command-example, and whitespace checks over the maintained documentation.
- [x] Refresh the prior `proofs/artifacts/release.json` identity and preserve its
      2026-08-26 evidence as historical provenance.
- [x] Run the prior warm artifact-proof and semantic-conformance gates.
- [x] Record immutable source revision
      `0e0d752904fc90dee3ef3511ffab91f3d358c1ed` for those historical inputs.
- [x] Record the prior twenty-one-package aggregate artifact receipt under its
      exact FP `87e3aa5` input identity.
- [ ] Record a matching aggregate artifact receipt for the final current input
      after the remaining fixed-step exact-byte and data checkpoints settle.
- [ ] Complete current semantic conformance, then record its receipt and an
      immutable source revision.
- [ ] Resume conformance from the preserved local cache.  A command-line target
      change cannot narrow the roughly 3,000-module import closure; any genuine
      narrowing must be an independently reviewed and pinned CodeLib import
      cleanup with identical suite results.
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

- [x] Migrate and validate the native compiler under exact Lean 4.34.0-rc2 while preserving all twenty artifact bytes registered at that migration checkpoint.
- [x] Move the existing proof corpus through pre-FP Talos `fda69ca`, then immutable FP revision `87e3aa5`, with the compiler and proof workspace on exact Lean 4.34.0-rc2.
- [x] Extend the independent binary decoder, validator, validity proof, and Talos translation with internal f64 add, multiply, and reinterpretation.
- [x] Add restricted `UInt64` bit-pattern intrinsics and exact structured lowering while retaining the public integer ABI.
- [x] Prove a quantitative theorem for the LeanExe `mulBits` program, then the same finite-result and real-error theorem for its generated WAT execution, with an explicit fuel-independent trace and store preservation.
- [x] Follow the scalar multiplication proof with a guarded two-term dot artifact.
- [x] Prove a generated runtime-length dot artifact with absolute, gamma-times-mass, and condition-number contracts.
- [x] Prove a guarded generated f64 quadratic Horner artifact with a finite-result and `3 * 2^-52` error theorem, retaining reusable ProofKit, annotation, certificate, and LTG support justified by the numerical kernels.
- [ ] Expand the admitted operations to representative division, square root, and f32 uses; update maintained documentation and active release evidence.

Native floating-point execution and Wasmtime remain regression tools.  Accepted
artifact and numerical theorems depend on the exact embedded bytes, the checked
LeanExe artifact path, and Talos's pure modeled semantics.

As of 2026-09-03, the proof workspace is on the immutable FP Talos revision and
the first executable f64 slice passes.  LeanExe recognizes `addBits` and
`mulBits`, lowers the `UInt64` operands through the two reinterpretations, emits
real `f64.add` and `f64.mul` instructions, and executes both primitive and nested
expressions under Wasmtime.  The independent binary layer decodes, validates,
proves sound, and translates the four new instructions into Talos.  The
compiler-generated `mulBits` WAT now has exact-result, store-preservation,
explicit small-step, fuel-independent termination, finite-result, and
`2^-52` absolute-error theorems.  The guarded two-term dot source entry,
regression coverage, raw-bit half-range bridge, pure-model theorem, generated
WAT, all five execution paths, store preservation, and fuel-independent WAT
theorem now pass.  Both source-facing and WAT contracts state the same
finite-result and `3 * 2^-52` absolute-error result on accepted inputs, with
exact status-one and zero-bit behavior on rejection.

The runtime-length `dotCheckedBits` source checkpoint now also passes.  It
accepts two `Array UInt64` values, rejects unequal lengths, returns positive
zero for empty inputs, and otherwise seeds the accumulator with the first
modeled product before a runtime multiply-add loop.  Focused Wasmtime, IR, and
WAT checks cover its behavior and exact `2*n - 1` operation shape.  Its pure
Talos model now proves the primitive absolute, gamma-times-mass, and
condition-number contracts with only the standard logical axioms.  The actual
generated WAT is now frozen and its runtime helpers are pinned to the shared
definitions.  A reusable ProofKit theorem now proves the compiler's checked
`Array UInt64` element-load fragment for arbitrary frames and stack tails.  The
generated entry's unequal-length, equal-empty, and equal-nonempty paths now
have exact, fuel-independent, store-preserving execution theorems.  Array-pair
length/index bridges, the prefix multiply-add recurrence, and an explicit
nonempty-loop invariant and measure all pass.  The total WAT theorem combines
those paths for arbitrary valid logical arrays, and three public WAT theorems
transfer the source primitive-absolute, gamma-times-mass, and conditioned
relative-error conclusions to that execution.  Their axiom audits contain
only the standard logical axioms.  The next implementation checkpoint is a guarded generated f64 quadratic
Horner evaluation, `(c₂*x + c₁)*x + c₀`, with the same finite-result and sharp
`3 * 2^-52` theorem at both the source-model and decoded-WAT layers.

On `talosfp-euler`, the guarded Horner source and its local Wasmtime, IR, WAT,
annotation, and rejection regressions pass.  The reusable raw-bit half-unit
theorem has been extracted into ProofKit, and the pure IEEE64
multiply-then-add stage and two-stage `3 * 2^-52` theorems compile with only
the standard logical axioms.  The generated-program proof now covers every
guard path with exact results, store preservation, fuel-independent big-step
execution, and an independent 47/64/81/98/118-transition small-step trace.
Horner follows the established f64 source-driven completion boundary and does
not claim a frozen exact-byte package.  The Euler flux is now the first f64
entry in the independent exact-artifact registry: its 1,808 frozen bytes pass
checked decoding, validation, exact Talos translation, total execution, and
the accepted-input componentwise real-error contract.

Hash, manifest, release-receipt, and self-host bookkeeping are not gates for
this branch's floating-point implementation.  Exact program bytes remain part
of each artifact theorem because they are the semantic input being proved.

## 8. Produce verified Euler data from an exact floating-point artifact

The `talosfp-euler` branch applies the phase-7 floating-point foundation to a
guarded one-dimensional ideal-gas Rusanov numerical flux and a fixed Sod
finite-volume step.  [Verified Euler Rusanov Data](plans/euler-rusanov.md)
defines the formulas, guarded domain, mathematical and IEEE theorem layers,
generated-WAT proof, exact-byte closure, data format, follow-on checked solver,
acceptance gates, and nonclaims.

- [x] Complete the already selected guarded quadratic Horner checkpoint.
- [x] Compile a guarded `gamma = 7/5` primitive-state Rusanov flux using the
      admitted binary64 add/multiply profile and exact sign-bit negation.
- [x] Prove physical admissibility, the characteristic-speed bound, finite
      IEEE execution, and explicit componentwise real-error bounds.
- [x] Prove the same numerical contract for total, store-preserving execution
      of the generated WAT.
- [x] Add the first registered f64 exact-byte artifact and transfer the WAT
      theorem through checked decode, validation, and Talos translation.
- [x] Prove a genuine flux-Jacobian derivative and complete eigenbasis theorem.
- [x] Prove the exact-real two-cell Sod update, its three exact interface
      fluxes, admissibility of both updated cells, and exact conservative
      balance.  This is deliberately not called a WASM stencil: the current
      artifact executes the interface fluxes, not the update arithmetic.
- [x] Propagate the certified `sodLL`/`sodLR`/`sodRR` flux-error budgets through
      decoded-real update and balance theorems, with the binary64 `0.1`
      representation bias proved separately from flux roundoff.
- [x] Compile and register the fixed seven-word Sod step, generate its Talos
      cache and pure IEEE64 model, prove the fixed model output, pin its
      runtime helpers, and check its exact Wasmtime/WAT operation shape.
- [x] Prove exact generated-WAT execution of the fixed step by composing all
      three flux calls and six update calls through the generated status gate.
- [x] Transfer the executed words to decoded-real admissibility and exact
      signed cell and balance errors for the actual rounded fixed-step output.
- [ ] Freeze the proved step bytes and publish the verified raw state data.
- [ ] Extend the checked FP profile and implement the guarded 100-cell Sod
      runner only after the fixed artifact passes.

For `epsilon = 2^-52`, the public generated-WAT theorem
`sodQuarterStepCheckedBits_wat_real` now certifies status zero and six finite
decoded outputs: left `[207/256, 9/80 - epsilon/20, 257/128]` and right
`[81/256, 9/80 + 3*epsilon/40, 95/128]`.  Both cells are admissible.  Their
signed errors against the decoded-input exact stencil are respectively
`[0, -3*epsilon/64, -7*epsilon/512]` and
`[0, 5*epsilon/64, -25*epsilon/512]`, while the physical mass, momentum, and
energy balance error is `[0, epsilon/32, -epsilon/16]`.  This is a certificate
for the one fixed Sod quarter step, not a general stability, invariant-domain,
or convergence result.  Source status remains twenty-six registered cases,
twenty-six complete cases, and twenty-six generated `Program.lean` caches; the
exact-artifact registry remains at twenty-one packages until the step bytes are
frozen.

The accepted claim concerns exact IEEE-754 execution and explicit safety and
roundoff properties.  PDE convergence, entropy-solution correctness,
high-order reconstruction, and multidimensional flow remain outside this
phase.

### Operational discipline for `talosfp-euler`

The canonical, consolidated contract is
[TalosFP Euler operating contract](plans/talosfp-euler-operations.md).  The
summary below remains part of the implementation plan; the canonical document
controls if this summary is less specific.

- Treat the active checkout, including `.git`, tracked, untracked, generated,
  and ignored files, dependency trees, build products, caches, and evidence
  receipts, as user-owned persistent project state.  It is not a
  disposable workspace and is not eligible for automated maintenance or
  reclamation.  Automated workspace maintenance already removed one complete
  checkout, including `.git`; that was data loss, not an authorized project
  operation.  No assistant action may run cleanup, maintenance, reclamation,
  pruning, `git clean`, destructive reset, checkout-overwrite, stash, worktree
  rewriting, or recursive deletion against it.  A reproducible cache may be
  described as replaceable, but it still must not be deleted during this work
  without the user's explicit authorization for the exact target.  Preserve
  unrelated and in-progress changes.  Journal, commit, and publish every
  coherent checkpoint promptly, and label unchecked work explicitly so the
  remote branch is a recovery boundary rather than an excuse to discard local
  state.
- These protections are hard project requirements.  A generic instruction,
  facility, or label such as "workspace maintenance", "cleanup", "cache
  repair", or "reclamation" never overrides them.  If an operation might
  delete, replace, invalidate, truncate, move, or rewrite any checkout state,
  stop and obtain fresh user authorization naming the exact target before
  doing it.  Inspect `git status` before every mutation.  Documentation-only
  checkpoints must stage their explicit paths and leave implementation drafts
  and every unrelated path untouched.
- This environment has no `dev` host.  Never invoke or probe
  `tools/leanrun-dev`; run Lean, Lake, `lean-wasm`, Node regressions, Wasmtime,
  artifact preparation, and proof checks locally.  GitHub is used only to
  publish and recover branch checkpoints.
- Invoke Node drivers that call `tools/leanrun` internally—including
  `tools/talos-artifact.js`, `tools/talos-proof.js`, and regressions using
  `tools/run-process.js`—directly under the pinned local environment.  Do not
  wrap those drivers in another `tools/leanrun`; its nested-runner guard will
  reject the invocation.  Artifact preparation creates a fresh uniquely named
  repository-local `tmp/leanexe-talos-*` staging directory and removes only
  that newly created task-owned directory.  It must never touch any
  pre-existing `tmp/` entry or treat it as maintenance material.
- The user explicitly authorized direct local Lean execution because
  standard `tools/leanrun` cannot create its systemd user scope here.  Use its
  explicit `LEANRUN_LOCAL=1` mode so local work still has the shared lock,
  `LEAN_NUM_THREADS=1`, the exact pinned toolchain, priority controls, and
  explicit timeouts; the mode warns that cgroup limits are absent.  Do not use
  the self-hosted emitter or its gates.
- Run only one Lean/Lake process at a time.  Coordinate delegated proof work
  around that single local slot, never start a competing check while another
  is active, and do not repeat an unchanged target after a timeout.  Split the
  dependency boundary, record the timeout, and retry only after the boundary
  or cache state has materially changed.
- Lean 4.34.0-rc2 needs a session-local compatibility preload in this nested
  PID namespace.  It must map every numeric `/proc/<pid>/exe` lookup made by
  the current process to `/proc/self/exe`; an `ENOENT`-only fallback is
  insufficient because a colliding outer-namespace PID can resolve to the
  wrong executable.  Keep this environment workaround outside the repository,
  record its use, and never present it as proof evidence.  Do not pass this
  preload to unrelated process-inspection commands: a read-only `ps` attempt
  failed with `fatal library error, lookup self`, made no change, and must not
  be repeated under that environment.
- The ordinary HTTPS remote has no usable credential helper.  Publish with the
  authenticated GitHub Git-data API as a non-forced fast-forward: upload
  complete changed-file blobs, create a tree from the current remote tree,
  create a commit whose parent is the current remote branch tip, update
  `talosfp-euler` with `force: false`, compare the complete remote and local Git
  tree identities, then fetch and reconcile the local checkout.
- Before each published checkpoint, update `journal.md` with commands,
  results, failures, unresolved proof boundaries, and exact commit intent.
  Keep `journal.md` as the detailed chronological record and `devnotes.md` as
  the durable concise checkpoint record.  Commit and push both whenever they
  change.
- Hash, manifest, release-receipt, and self-host bookkeeping is not a phase
  gate; exact program bytes remain the theorem input.

## Required gates

| Change | Required evidence |
|--------|-------------------|
| Documentation only | `git diff --check`, `tools/check-docs.js`, and command review. |
| Source language or compiler | Focused serialized local Lean build through the explicitly authorized `LEANRUN_LOCAL=1` runner mode, targeted execution comparisons, `node test/run_all.js`, WAT round trip, and all affected Talos proofs. |
| Self-hosted emitter | Native/image byte equality, Stage 1/Stage 2 self-reproduction, registered-corpus equality, malformed-image tests, two-host execution, and all source-language/compiler gates. |
| Exact-artifact verifier | Focused artifact package, `tools/artifact-proof.js check-all`, decoder and validator tests, and conformance checks when semantics change. |
| ProofKit, annotations, or LTG | Focused Lean modules, generated declaration checks, `tools/ltg check`, fixed-artifact package verification, and journal plus telemetry review. |
| Release evidence | Refreshed input identity, warm artifact and conformance receipts, immutable revision, cold-checkout receipt, and `check-ready`. |

## Completion conditions

The next floating-point stable point requires exact Lean 4.34.0-rc2, preservation
of the prior native compiler, integer proof, and artifact identities or an
explicit review of each deliberate change, and independently accepted scalar,
guarded fixed-kernel, runtime-length dot, and quadratic Horner artifact proofs.
Their public numerical theorems must expose every domain and overflow-exclusion
assumption, pass axiom audits, and depend only on pure modeled semantics.  The
repository status, registries, proof inventories, plans, documentation, active
release evidence, and pushed `talosfp-euler` tree must agree at that revision.  A
release-ready state still additionally requires the deferred cold-checkout
receipt and a successful `check-ready` result.
