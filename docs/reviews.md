# Reviews

## 2026-08-03: Artifact-Level Verification Implementation

The repository now verifies an exact WebAssembly binary without reading its source program or invoking LeanExe.  Twenty content-addressed packages contain frozen `program.wasm` files and strict manifests, while proof modules embed the complete bytes and prove decoding, validation, translation, and behavior.  The aggregate artifact-only gate passed byte identity, embedded-byte comparison, exact artifact theorem targets, behavioral specifications, and manifest declarations for all twenty packages on 2026-08-03.

The formal boundary begins with `artifactBytes : ByteArray`.  `Wasm.Binary.Proof.decode_sound` connects a successful parse to the independent `Encodes` grammar, and `Wasm.Binary.Proof.validate_sound` connects successful validation to the independent `CoreValid` judgment.  Each package proves a closed `artifact_module_eq_cache` theorem that decodes and validates the bytes and identifies the translated validated module with the execution module used by its registered behavioral theorem.

`tools/artifact-proof.js check` verifies one registered binary and proof target.  Its aggregate modes validate registry and manifest schemas, compare SHA-256 digests and lengths, compare files with Lean's embedded byte values, build the formal artifact targets, build behavioral specifications, and check every theorem name recorded by the manifests.  The command invokes every Lean child through `tools/leanrun`, whose general approval prefix enforces the same-user `leanexe`/`vq` lock, cgroup limits, one-core quota, process priority, I/O priority, and timeout policy.

| Boundary | Result on 2026-08-03 | Remaining qualification |
|----------|----------------------|-------------------------|
| Frozen identity | Passed for twenty packages | File reading and byte comparison remain an operational boundary outside the theorem. |
| Binary grammar | `decode_sound` builds; all twenty exact binaries decode | The accepted profile rejects unsupported WebAssembly features. |
| Core validation | `validate_sound` builds; all twenty decoded modules validate, and fifteen pinned official invalid modules match exact decoder or validator errors | The corpus tests the executable checks and remains evidence rather than a theorem premise. |
| Talos translation | Exact cache-equality targets pass for all twenty packages | Talos semantics remain in the trusted base. |
| Artifact behavior | All twenty behavioral specifications and manifest declarations pass | Specifications remain human-reviewed trusted statements. |
| Proof execution | The complete aggregate passes under the shared constrained runner | `Project.ClobCancel.Spec` took 1,092 seconds and remained within its target limit. |
| Repository execution | The complete Node gate passes 791 accepted cases, 45 expected rejections, 14 expected traps, 340 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases | Execution tests support the compiler and host paths but do not enter the artifact theorem. |
| Semantic conformance | Talos reports 3,853 passes, six known assertion failures, and 627 skips across twenty-five official files; Wasmtime passes all twenty-five | The gate warns only for the six exact imported-memory rows in `memory_grow.wast`. |
| Kernel trust | Both workspaces pin Lean 4.31.0 at commit `68218e876d2a38b1985b8590fff244a83c321783`; the archived reproduction succeeds | The owner accepts the defect after the recorded lexical audit, whose narrow scope does not repair the kernel or establish the absence of other environment-mutation paths. |
| Release record | Draft binds twenty packages, theorem names, tool pins, the expanded 565-file release-input digest, and both matching warm gate receipts | An immutable source revision and its matching cold-checkout receipt remain absent. |

`tools/artifact-conformance.js check` makes the official-corpus evidence reproducible from `proofs/talos/conformance.json`.  It verifies the pinned CodeLib and official testsuite revisions, checks `wasm-tools` and Wasmtime versions, builds the artifact classifier and testsuite under `tools/leanrun`, classifies fifteen exact invalid modules, and executes twenty-five files serially through exact one-file temporary corpora.  The command reports every classification and execution outcome, warns only for configured failure rows, and stops for a changed invalid-module classification, changed or additional Talos failures, or any Wasmtime failure.

The fifteen invalid cases identify an official file, assertion kind, and source line, then require an exact artifact decoder or validator error constructor.  Text-origin `assert_invalid` modules have encoder-added custom sections removed before classification so the intended invalid core module reaches the relevant rule, while raw `assert_malformed` binaries remain unchanged.  The selected cases cover header truncation, version and section errors, integer overflow, memory alignment and limits, stack underflow, and stack-height mismatches.

The selected slice produced no Talos cascades, decoder errors, interpreter errors, or fuel exhaustion.  The six known failures in `memory_grow.wast` arise because Talos copies an imported memory into the importer but applies the import declaration's maximum, allowing a memory exported with a five-page maximum to grow to six pages.  Wasmtime passes the same file, and the warning disappears if a later pinned Talos revision reports no matching failures.

The twenty artifact theorems concern modules without imports and remain valid statements under the pinned Talos semantics.  The conformance result limits confidence that Talos represents WebAssembly outside that profile and requires the release record to state the no-import boundary.  The corpus now covers the accepted integer, control, call, local, memory, conversion, and expression forms, while `global.wast` remains a recorded gap because it mixes local globals with imported globals and a table form.

`proofs/artifacts/release.json` records every binary and package identity, theorem name, tool revision, release-input digest, and observed result.  `tools/artifact-release.js` verifies those fields against the repository and derives two blockers from the evidence fields, so `check-ready` currently fails.  Its cold mode will compare a fresh clone of the recorded revision with the current canonical inputs, verify the exact Lean and dependency revisions, reject tracked mutations, run both gates, and write the matching cold receipt.

The completed exact-artifact gate establishes that each registered behavioral proof concerns the Talos translation of the bytes in its immutable package.  Source correspondence and compiler correctness require the separate theorem-transport and compiler-verification work.  Each release also requires review of the behavioral specifications, Talos semantics, host assumptions, and selected Lean kernel.

Aggregate rebuildability now holds under the standard resource policy.  Folded-frame lemmas, `wp_run_folded`, generic loop-body scaffolding, smaller semantic modules, and reusable LEB128 allocator and iteration lemmas repaired the earlier `Validate`, `PushTwice`, `SharedPair`, `PairFree`, and `LebU32` failures.  The successful run continued through every CLOB specification and the generated manifest-declaration check, while the remaining work concerns release evidence rather than artifact-proof implementation.

## 2026-08-01: Toolchain and Execution Verifiability (Superseded Snapshot)

The reproducible stable point is incomplete.  The repository has pinned tools, broad differential execution coverage, and input-generic Talos theorems for all twenty registered artifacts.  The current checkout lacks aggregate proof and execution results, contains proof edits that have not built, and pins a Lean version affected by the kernel defect recorded in the development journal.

This review distinguishes two goals.  The near-term goal is reproducible evidence for the current twenty artifacts under the repository's required resource limits.  Literal end-to-end compiler verification also requires general results connecting extraction, IR evaluation, lowering, emitted bytes, modeled WASM execution, and source behavior.

### Snapshot

The review examined `main` at `ea3ab0a`, with additional working-tree changes in `Project.LebU32.Iter`, `Project.LebU32.Main`, and `Project.PairFree.Builds`, plus the new `Project.PairFree.Frame` module.  Node 24.13.0 and `wasm-tools` 1.251.0 match their repository pins, while the checked Wasmtime 44.0.0 installation and native host runner are present.  Both compiler and proof workspaces pin Lean 4.31.0.

| Area | State | Evidence |
|------|-------|----------|
| Tool availability | Present and version-checked | Node 24.13.0 and `wasm-tools` 1.251.0 pass their checks.  Wasmtime 44.0.0 and the native host runner are installed. |
| Artifact coverage | Twenty completed cases | Every entry in [`cases.json`](../proofs/talos/cases.json) has `complete: true`, including all planned CLOB exports.  The focused `clob_depth` gate passed after artifact regeneration. |
| Aggregate proof gate | Open | The aggregate run reached its stage timeout.  The remaining heavy proof boundaries are `LebU32.Iter`, `LebU32.NegIter`, `PairFree.Builds`, and `SharedPair.Spec`. |
| Current proof edits | Unverified | The modified `LebU32.Iter` and `PairFree.Builds` sources have no current object files, and the `LebU32.Main` object predates its edit.  `PairFree.Frame` has built, but its dependent proof has not. |
| Execution gate | Stale | The recorded 791-case baseline predates the present proof and infrastructure state.  No result from `node test/run_all.js` establishes the current checkout. |
| WAT and binary comparison | Implemented, with no current result | [`check-wat.sh`](../tools/check-wat.sh) compares nine direct binaries with binaries parsed from compiler-emitted WAT.  No result is recorded for this checkout. |
| Continuous evidence | Missing | The repository has no remote CI configuration.  Gate results exist as prose in the journal rather than retained logs or attestations tied to a commit. |
| Documentation agreement | Failing | The registry and status report describe twenty completed cases, while the development plan and developer guide still describe nineteen cases and an unfinished `depth` artifact. |
| Kernel trust | Open | The journal records a `False` derivation through checked declarations on Lean 4.31.0.  The local compiler and proof sources do not use the exploit's `addDecl` or `.inductDecl` mechanism, but the pinned kernel remains affected and the repository records no mitigation. |
| Compiler-wide theorem | Planned | Current theorems validate twenty artifacts individually.  Heap IR semantics, front-end certificates, a general lowering theorem, and rederivation of artifact results from that theorem remain future work. |

### Evidence Already Established

The execution suite covers report classification, ownership reports, Wasmtime execution, scalar and heap behavior, reference counting, allocation, strings, integer maps, JSON, WASI adapters, self-emission, standard-Lean comparisons, IR comparisons, and fuzz cases.  The last recorded complete baseline contains 791 accepted cases, 45 rejections, 14 traps, 340 standard-Lean comparisons, 62 IR comparisons, 41 reference-counting cases, nine CLI failure cases, and three process-launch error cases.  These counts describe the earlier baseline and do not establish the current checkout.

The proof registry contains twenty completed artifact cases.  The CLOB set covers `quote`, `cancel`, `findBest`, `postOnly`, `matchFuel`, `limit`, `market`, and `depth`, while the other artifacts cover scalar algorithms, recursive data, byte arrays, ownership, and the compiler's LEB128 encoder.  The focused `clob_depth` gate regenerated its current model and passed its specification build on 2026-07-18.

The reproducibility controls cover the tools that generate or decode artifacts.  The repository checks exact Node and `wasm-tools` versions, checks Wasmtime release archives against recorded SHA-256 hashes, pins Lean in both workspaces, pins Talos and its transitive Lean dependencies by commit through the Lake manifest, and enforces serial Lean execution under the required systemd resource scope.  The Talos tools regenerate each artifact before a focused or aggregate proof build and reject registry or aggregate-import inconsistencies before starting compilation.

### Open Stable-Point Evidence

The aggregate proof gate has not completed under the required memory and CPU limits.  Earlier division work reduced `Validate.Loop` from 1,560 seconds to 15 seconds and made the divided `PushTwice` proof build, which confirms that folded local frames and smaller elaboration boundaries address the measured working-set problem.  The same treatment remains incomplete for `LebU32.Iter`, `LebU32.NegIter`, `PairFree.Builds`, and `SharedPair.Spec`.

The worktree cannot serve as proof evidence in its current state.  `PairFree.Frame` has a newer object file, but `LebU32.Iter` and `PairFree.Builds` have none, and `LebU32.Main` has an object file older than its source edit.  Focused builds must establish each edited boundary before another aggregate attempt.

The execution and WAT gates also lack current results.  The proof-infrastructure changes should preserve compiler behavior, but the plan requires the complete execution suite and artifact checks before declaring the stable point.  Documentation must then agree with the registry, proof inventory, journal, and implementation.

### Trust Boundaries

The proof workspace pins Lean 4.31.0, which the [development journal](../devnotes.md#2026-07-20-a-kernel-unsoundness-in-our-own-toolchain) records as accepting a self-contained derivation of `False` through a hand-built inductive declaration and an expression-hash collision.  The exploit uses metaprogramming mechanisms absent from the local compiler and proof sources, which limits the evidence of direct exposure but does not repair the kernel.  Lean's [`Environment` implementation](https://github.com/leanprover/lean4/blob/master/src/Lean/Environment.lean) identifies declaration type checking as the kernel boundary and warns that bypassing kernel checking compromises soundness.

The repository has no recorded fixed Lean pin or independent checker result that rejects the reproduction.  Replaying object files through another checker remains an open question because the journal records an unverified report that Nanoda accepted the same construction.  A complete proof-toolchain claim therefore requires an explicit trust decision and evidence for the selected mitigation before rerunning the final proof gate.

The current artifact path contains two further semantic trust points.  LeanExe emits WASM bytes, `wasm-tools print` renders those bytes as WAT, and the external Talos generator decodes that WAT into the Lean module used by each theorem.  The [emitter restructuring plan](emitter.md) would introduce a structured module value and compare it by decidable equality with the externally decoded model, removing both external translations from the proof's semantic path.

Host conformance remains empirical.  Artifact theorems assume the ABI representation, initial globals, available pages, stack capacity, and correspondence between the Talos semantics and the Wasmtime implementation.  Differential execution tests connect those assumptions to observed behavior on selected inputs, while the artifact theorem supplies the input-generic result inside the Talos model.

### Completion Order

The first decision concerns kernel trust.  The project owner must select evidence sufficient for the intended claim, such as a fixed Lean release that rejects the reproduction or a narrower, documented trust boundary supported by an audit and an independent check.  Another successful proof build under the same affected kernel would leave this issue open.

After that decision, the proof-infrastructure work should finish the four heavy boundaries through focused, constrained builds.  The repository can then run `tools/talos-proof.js check --all`, the complete execution suite under its outer resource scope, and the WAT round-trip gate.  Each result should record the commit, exact tool versions, command, resource policy, outcome, and artifact-byte review in the development journal.

The final stable-point change must reconcile the maintained documents.  In particular, [`plan.md`](../plan.md), [`DEVELOPING.md`](../DEVELOPING.md), the [development status](status.md), the [proof inventory](../proofs/talos/README.md), and the journal must agree that twenty cases are complete and identify the results supporting that statement.  Retained gate logs or a machine-readable receipt tied to the commit would improve later verification because the repository has no remote CI.

### End-to-End Compiler Verification

The current system performs handwritten translation validation per artifact.  It does not prove the compiler pipeline once for every accepted program, and the [compiler-verification plan](../proofs/talos/compiler-verification.md) estimates that broader result at one to two person-years.  Phase zero of that plan remains open because the aggregate proof and execution gates have not closed.

The remaining phases restructure the emitter, define heap semantics for the IR, define one representation and ownership relation, prove each lowering template, prove the general back-end simulation, generate front-end extraction certificates, and rederive the twenty artifact theorems from the compiler theorem.  The Talos model would remain the formal WASM semantics, with fidelity to engines and host ABI conformance supported by differential execution.  Completion would still state explicit qualifications for bounded natural numbers, allocator budgets, the deferred `memoryGrow` path, and trusted Lean and Talos components.

### Assessment

LeanExe has substantial execution evidence and unusually broad input-generic artifact coverage.  It has not reached a reproducible stable point for the current checkout because the aggregate proof, execution, WAT, documentation-agreement, and kernel-trust conditions remain open.  Literal end-to-end compiler verification remains a separate, much larger program whose first phase depends on closing this stable point.
